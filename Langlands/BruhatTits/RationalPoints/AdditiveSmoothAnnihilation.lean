import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.Weil.Representation.ContinuityProof
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.NumberTheory.LocalField.Basic

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.RationalPoints

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An open-kernel real homomorphism on the additive local field vanishes. -/
theorem additiveReal_eq_one (f : Multiplicative F →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (Multiplicative F))) (x : Multiplicative F) :
    f x = 1 := by
  let s : Multiplicative 𝒪[F] →* Multiplicative F :=
    AddMonoidHom.toMultiplicative
      { toFun := fun z => x.toAdd * (z : F)
        map_zero' := by simp
        map_add' := fun a b => by simp [mul_add] }
  have hs : Continuous s := by
    change Continuous (fun z : 𝒪[F] => x.toAdd * (z : F))
    exact continuous_const.mul continuous_subtype_val
  let g := f.comp s
  have hg : IsOpen (g.ker : Set (Multiplicative 𝒪[F])) := hf.preimage hs
  have hfin := Langlands.Weil.finite_range_of_open_kernel g hg
  let : Finite g.range := hfin.to_subtype
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_of_finite
    (g.rangeRestrict (Multiplicative.ofAdd (1 : 𝒪[F])))).exists_pow_eq_one
  have ht : IsOfFinOrder (g (Multiplicative.ofAdd (1 : 𝒪[F]))) :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨N, hN, congrArg (fun a : g.range => (a : Multiplicative ℝ)) hpow⟩
  have he := (isOfFinOrder_iff_eq_one _).mp ht
  change f (Multiplicative.ofAdd (x.toAdd * (1 : F))) = 1 at he
  simpa using he

/-- Every additive line in a product of local fields has trivial smooth real image. -/
theorem vectorReal_eq_one {Index : Type v}
    (f : Multiplicative (Index → F) →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (Multiplicative (Index → F))))
    (x : Multiplicative (Index → F)) : f x = 1 := by
  let s : Multiplicative F →* Multiplicative (Index → F) :=
    AddMonoidHom.toMultiplicative
      { toFun := fun z i => z * x.toAdd i
        map_zero' := by ext i; simp
        map_add' := fun a b => by ext i; simp [add_mul] }
  have hs : Continuous s := by
    change Continuous (fun z : F => fun i => z * x.toAdd i)
    exact continuous_pi fun _ => continuous_id.mul continuous_const
  have he := additiveReal_eq_one (f.comp s) (hf.preimage hs)
    (Multiplicative.ofAdd (1 : F))
  change f (Multiplicative.ofAdd (fun i => (1 : F) * x.toAdd i)) = 1 at he
  simpa using he

end LocalField

namespace VectorCoordinates

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual rational vector coordinates, with values in the base ring. -/
def rationalCoordinates :
    rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n) ≃*
      Multiplicative (Fin n → R) :=
  (VectorGroup.coordinates (CommRingCat.of R) n (Over.mk (𝟙 _))).trans
    (AddEquiv.piCongrRight fun _ =>
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toAddEquiv).toMultiplicative

@[simp]
theorem rationalCoordinates_apply
    (p : rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n)) (i : Fin n) :
    (rationalCoordinates R n p).toAdd i =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (p.left.appTop (VectorGroup.coordinateSection (CommRingCat.of R) n i)) := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((VectorGroup.coordinates (CommRingCat.of R) n _ p).toAdd i) = _
  rw [VectorGroup.coordinates_apply]

theorem polynomialPoint_apply_X
    (p : rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n)) (i : Fin n) :
    affineRingPointEquiv R (MvPolynomial (Fin n) R) R
      (rationalPointEquiv R _ p) (MvPolynomial.X i) =
      (rationalCoordinates R n p).toAdd i := by
  rw [rationalCoordinates_apply]
  change (Spec.preimage (rationalPointEquiv R _ p).left).hom (MvPolynomial.X i) = _
  rw [rationalPointEquiv_left]
  let q : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin n) R)) := p.left
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage q)
  rw [Spec.map_preimage] at h
  have he := congrArg (fun f => f (VectorGroup.coordinateSection (CommRingCat.of R) n i)) h
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (p.left.appTop (VectorGroup.coordinateSection (CommRingCat.of R) n i)) =
    (Spec.preimage p.left).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) R))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) R))).inv
          (MvPolynomial.X i))) at he
  simpa using he.symm

variable [TopologicalSpace R] [IsTopologicalRing R]

local instance vectorGroup_isAffine :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of R) n).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R))))

/-- The actual rational coordinates respect the canonical point topology. -/
def rationalCoordinatesHomeomorph :
    letI : TopologicalSpace
      (rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n)) :=
        rationalPointTopology R _
    rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n) ≃ₜ
      Multiplicative (Fin n → R) := by
  let : TopologicalSpace
      (rationalPoints (VectorGroup.groupScheme (CommRingCat.of R) n)) :=
    rationalPointTopology R _
  let E := (rationalPointHomeomorph R
    (VectorGroup.groupScheme (CommRingCat.of R) n).X).trans
      (spectrumAlgebraPointHomeomorph R R (MvPolynomial (Fin n) R))
  refine
    { (rationalCoordinates R n).toEquiv with
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous (fun p => (rationalCoordinates R n p).toAdd)
    apply continuous_pi
    intro i
    have h := (AlgPoint.continuous_eval (R := R) (S := R)
      (MvPolynomial.X i)).comp E.continuous_toFun
    convert h using 1
    funext p
    exact (polynomialPoint_apply_X R n p i).symm
  · have h : Continuous (fun x : Multiplicative (Fin n → R) =>
        AlgPoint.ofAlgHom
          (MvPolynomial.aeval x.toAdd : MvPolynomial (Fin n) R →ₐ[R] R)) := by
      apply (AlgPoint.continuous_iff _).mpr
      intro a
      change Continuous (fun x : Fin n → R => MvPolynomial.aeval x a)
      exact MvPolynomial.continuous_eval a
    have hcomp := E.symm.continuous_toFun.comp h
    convert hcomp using 1
    funext x
    change (rationalCoordinates R n).symm x =
      E.symm (AlgPoint.ofAlgHom (MvPolynomial.aeval x.toAdd))
    apply (rationalCoordinates R n).injective
    apply Multiplicative.toAdd.injective
    funext i
    rw [MulEquiv.apply_symm_apply]
    rw [← polynomialPoint_apply_X]
    change x.toAdd i =
      (E (E.symm (AlgPoint.ofAlgHom (MvPolynomial.aeval x.toAdd)))) (MvPolynomial.X i)
    rw [Homeomorph.apply_symm_apply]
    exact (MvPolynomial.aeval_X x.toAdd i).symm

end VectorCoordinates

section VectorImages

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local instance vectorGroup_isAffine :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of F) n).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) F))))

local instance vectorPointTopology :
    TopologicalSpace (rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n)) :=
  rationalPointTopology F _

local instance ambientPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Open-kernel real homomorphisms vanish on every actual rational vector-group point. -/
theorem vectorGroupReal_eq_one
    (f : rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n) →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints
      (VectorGroup.groupScheme (CommRingCat.of F) n))))
    (x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n)) :
    f x = 1 := by
  let E := VectorCoordinates.rationalCoordinates F n
  have hE : Continuous E.symm :=
    (VectorCoordinates.rationalCoordinatesHomeomorph F n).symm.continuous_toFun
  have he := vectorReal_eq_one (F := F) (Index := Fin n)
    (f.comp E.symm.toMonoidHom) (hf.preimage hE) (E x)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using he

/-- The actual image of a vector-group morphism is killed by an ambient smooth real map. -/
theorem vectorImage_eq_one
    (i : VectorGroup.groupScheme (CommRingCat.of F) n ⟶ G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G)))
    (x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n)) :
    f (rationalPoints.map i x) = 1 :=
  vectorGroupReal_eq_one n (f.comp (rationalPoints.map i))
    (hf.preimage (continuous_rationalPointMap F i.hom.hom)) x

/-- The actual vector-group point map, with its values placed in the ambient real kernel. -/
def vectorImageToOpenRealKernel
    (i : VectorGroup.groupScheme (CommRingCat.of F) n ⟶ G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G))) :
    rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n) →* f.ker :=
  (rationalPoints.map i).codRestrict f.ker (fun x => vectorImage_eq_one n i f hf x)

@[simp]
theorem vectorImageToOpenRealKernel_coe
    (i : VectorGroup.groupScheme (CommRingCat.of F) n ⟶ G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G)))
    (x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) n)) :
    (vectorImageToOpenRealKernel n i f hf x : rationalPoints G) =
      rationalPoints.map i x := rfl

end VectorImages

end Langlands.BruhatTits.RationalPoints
