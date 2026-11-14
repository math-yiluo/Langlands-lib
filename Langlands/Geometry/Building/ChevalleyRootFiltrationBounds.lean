import Langlands.Geometry.Building.ChevalleyRootFamily
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # Algebraic bounds for additive coordinates and Chevalley root filtrations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.SplitExistence
open Langlands.GroupScheme.SplitExistence.ChevalleyData
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.VectorGroup

private instance vectorGroup_isAffine (k : Type u) [Field k] (d : ℕ) :
    IsAffine (groupScheme (CommRingCat.of k) d).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin d) k)))
  infer_instance

variable {k : Type u} [Field k] [ValuativeRel k] {d : ℕ}

/-- Bounds on the standard affine coordinates bound every regular function on
the actual vector group. -/
theorem isAlgebraicallyBounded_of_coordinate_bounds
    (B : Set (rationalPoints (groupScheme (CommRingCat.of k) d)))
    (hB : ∀ i : Fin d, ∃ b : k, b ≠ 0 ∧ ∀ p ∈ B,
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        ((coordinates (CommRingCat.of k) d _ p).toAdd i) ≤ᵥ b) :
    IsAlgebraicallyBounded k (groupScheme (CommRingCat.of k) d).X B := by
  let π : MvPolynomial (Fin d) k →ₐ[k]
      AffineCoordinateRing k (groupScheme (CommRingCat.of k) d).X :=
    (spectrumCoordinateAlgEquiv k (MvPolynomial (Fin d) k)).symm.toAlgHom
  have he (p : rationalPoints (groupScheme (CommRingCat.of k) d)) (i : Fin d) :
      rationalPointAlgebraHom k (groupScheme (CommRingCat.of k) d).X p
          (π (MvPolynomial.X i)) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom
          ((coordinates (CommRingCat.of k) d _ p).toAdd i) := by
    rw [rationalPointAlgebraHom_apply_appTop, coordinates_apply]
    rfl
  intro a
  obtain ⟨b, hb, h⟩ := boundedEvaluation_of_polynomial_surjective
    (fun p : B => rationalPointAlgebraHom k (groupScheme (CommRingCat.of k) d).X p.val)
    π (spectrumCoordinateAlgEquiv k (MvPolynomial (Fin d) k)).symm.surjective
    (fun i => by
      obtain ⟨b, hb, h⟩ := hB i
      exact ⟨b, hb, fun p => by rw [he]; exact h p.val p.property⟩) a
  exact ⟨b, hb, fun p hp => h ⟨p, hp⟩⟩

end Langlands.GroupScheme.VectorGroup

namespace Langlands.Geometry.Building.ChevalleyRootFamily

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} {D : ChevalleyData P b}
  {k : Type u} [Field k] [ValuativeRel k]
  (G : D.ChevGroup k) [Finite J] [P.IsReduced]
  [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]

/-- A valuatively bounded set of field parameters has algebraically bounded
image under the actual Chevalley root homomorphism. -/
theorem isAlgebraicallyBounded_rootCoord_image (j : J) (A : Set k)
    (hA : ∃ b : k, b ≠ 0 ∧ ∀ x ∈ A, x ≤ᵥ b) :
    IsAlgebraicallyBounded k G.H.X
      ((fun x => (rootCoord G j (Multiplicative.ofAdd x) : rationalPoints G.H)) '' A) := by
  have hga : IsAlgebraicallyBounded k (Gak k).X
      ((fun x => gaRationalEquiv k (Multiplicative.ofAdd x)) '' A) := by
    apply VectorGroup.isAlgebraicallyBounded_of_coordinate_bounds (k := k) (d := 1)
    intro i
    obtain ⟨b, hb, h⟩ := hA
    refine ⟨b, hb, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    fin_cases i
    have hc := gaCoord_gaRationalEquiv k (Multiplicative.ofAdd x)
    change (VectorGroup.coordinates (CommRingCat.of k) 1 _
      (gaRationalEquiv k (Multiplicative.ofAdd x))).toAdd 0 = _ at hc
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      ((VectorGroup.coordinates (CommRingCat.of k) 1 _
        (gaRationalEquiv k (Multiplicative.ofAdd x))).toAdd 0) ≤ᵥ b
    rw [hc]
    simpa only [Iso.inv_hom_id_apply, toAdd_ofAdd] using h x hx
  have him := hga.image (G.u j).hom.hom
  simpa only [Set.image_image, Function.comp_def, rootCoord_apply_coe] using him

/-- A finite lower bound for an additive coordinate valuation gives a bound for
the corresponding Chevalley root filtration whenever that lower bound is
dominated by the value of a nonzero field element. -/
theorem isAlgebraicallyBounded_rootFiltration
    (omega : AddValuation k (WithTop ℝ))
    (hrel : ∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x)
    (r : ℝ) (hr : ∃ b : k, b ≠ 0 ∧ omega b ≤ (r : WithTop ℝ))
    (a : characterLattice (Tk (X := X) k)) (ha : a ∈ relativeRoots G.t) :
    IsAlgebraicallyBounded k G.H.X (rootFiltration G.t (family G omega) a r) := by
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).mp ha
  have hcoord : IsAlgebraicallyBounded k G.H.X
      ((fun x => (rootCoord G j (Multiplicative.ofAdd x) : rationalPoints G.H)) ''
        {x | (r : WithTop ℝ) ≤ omega x}) := by
    apply isAlgebraicallyBounded_rootCoord_image
    obtain ⟨b, hb, hbr⟩ := hr
    exact ⟨b, hb, fun x hx => (hrel x b).mpr (hbr.trans hx)⟩
  apply hcoord.mono
  intro g hg
  obtain ⟨x, hx⟩ := (rootCoord G j).surjective ⟨g, hg.1⟩
  have hxg : (rootCoord G j x : rationalPoints G.H) = g := congrArg Subtype.val hx
  refine ⟨x.toAdd, ?_, ?_⟩
  · have h := hg.2
    rw [← hxg, family_root, additiveRootValue_of_mem, MulEquiv.symm_apply_apply] at h
    exact h
  · simpa only [ofAdd_toAdd] using hxg

/-- At depth zero the unit scalar supplies the required coordinate bound. -/
theorem isAlgebraicallyBounded_zeroRootFiltration
    (omega : AddValuation k (WithTop ℝ))
    (hrel : ∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x)
    (a : characterLattice (Tk (X := X) k)) (ha : a ∈ relativeRoots G.t) :
    IsAlgebraicallyBounded k G.H.X (rootFiltration G.t (family G omega) a 0) :=
  isAlgebraicallyBounded_rootFiltration G omega hrel 0
    ⟨1, one_ne_zero, by simp⟩ a ha

end Langlands.Geometry.Building.ChevalleyRootFamily

namespace Langlands.Geometry.Building

/-- Algebraic boundedness of the zero-depth Chevalley root filtration for an
arbitrary field and additive valuation compatible with its valuative relation. -/
def ChevalleyZeroRootFiltrationBoundedStatement : Prop :=
  ∀ {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) (D : ChevalleyData P b)
    (k : Type u) [Field k] [ValuativeRel k]
    (G : D.ChevGroup k) [Finite J] [P.IsReduced]
    [Module.Finite ℤ X] [Module.Free ℤ X]
    [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    (omega : AddValuation k (WithTop ℝ)),
    (∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x) →
      ∀ a : characterLattice (Tk (X := X) k), a ∈ relativeRoots G.t →
        IsAlgebraicallyBounded k G.H.X
          (rootFiltration G.t (ChevalleyRootFamily.family G omega) a 0)

/-- The coordinate proof establishes the generic zero-depth statement. -/
theorem chevalleyZeroRootFiltrationBounded :
    ChevalleyZeroRootFiltrationBoundedStatement.{u} := by
  intro J X Y _ _ P b D k _ _ G _ _ _ _ _ _ omega hrel a ha
  exact ChevalleyRootFamily.isAlgebraicallyBounded_zeroRootFiltration G omega hrel a ha

end Langlands.Geometry.Building
