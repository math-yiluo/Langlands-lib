import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.Characters

/-! # Matrix entries and algebraic boundedness for closed representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Each entry of the actual rational-point matrix is uniformly bounded on
the specified set; the bound may depend on the entry. -/
def HasBoundedRationalEntries (ρ : MatrixRepresentation G n)
    (B : Set (rationalPoints G)) : Prop :=
  ∀ i j : n, ∃ b : F, b ≠ 0 ∧
    ∀ g ∈ B, (ρ.rationalMatrix g : Matrix n n F) i j ≤ᵥ b

omit [ValuativeRel F] in
/-- Inverse rational matrix entries evaluate the actual inverse coordinates. -/
theorem rationalMatrix_inv_apply_apply (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) (i j : n) :
    (ρ.rationalMatrix g)⁻¹ i j =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((g ≫ ρ.hom.hom).left.appTop
          (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j)) := by
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((GeneralLinear.pointsEquiv n (CommRingCat.of F) _ (g ≫ ρ.hom.hom))⁻¹ i j) = _
  rw [GeneralLinear.pointsEquiv_inv_apply]

variable [IsAffine G.X.left]

/-- A closed representation transports entry and inverse-entry bounds to
all regular functions, without a reductivity or local-field hypothesis. -/
theorem isAlgebraicallyBounded_of_entries_and_inverse
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (B : Set (rationalPoints G)) (hB : ρ.HasBoundedRationalEntries B)
    (hBi : ∀ i j : n, ∃ b : F, b ≠ 0 ∧
      ∀ g ∈ B, (ρ.rationalMatrix g)⁻¹ i j ≤ᵥ b) :
    IsAlgebraicallyBounded F G.X B := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (Grp.toMon (GeneralLinear.groupScheme n (CommRingCat.of F))).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of F)
  let π : MvPolynomial (GeneralLinear.Coordinate n) F →ₐ[F]
      AffineCoordinateRing F G.X :=
    (affineCoordinatePullback F ρ.hom.hom).comp
      ((spectrumCoordinateAlgEquiv F (GeneralLinear.CoordinateRing n F)).symm.toAlgHom.comp
        (GeneralLinear.quotient n F))
  have hπ : Function.Surjective π :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2.comp
      ((spectrumCoordinateAlgEquiv F (GeneralLinear.CoordinateRing n F)).symm.surjective.comp
        (Ideal.Quotient.mk_surjective))
  have he (g : rationalPoints G) (i j : n) :
      rationalPointAlgebraHom F G.X g (π (MvPolynomial.X (.entry i j))) =
        ρ.rationalMatrix g i j := by
    rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (g.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.entrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((g.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.entrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hi (g : rationalPoints G) (i j : n) :
      rationalPointAlgebraHom F G.X g (π (MvPolynomial.X (.inverseEntry i j))) =
        (ρ.rationalMatrix g)⁻¹ i j := by
    rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_inv_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (g.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((g.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hX : ∀ s, π (MvPolynomial.X s) ∈
      boundedEvaluationSubalgebra (fun g : B => rationalPointAlgebraHom F G.X g.val) := by
    intro s
    cases s with
    | entry i j =>
        obtain ⟨b, hb, h⟩ := hB i j
        exact ⟨b, hb, fun g => by rw [he]; exact h g.val g.property⟩
    | inverseEntry i j =>
        obtain ⟨b, hb, h⟩ := hBi i j
        exact ⟨b, hb, fun g => by rw [hi]; exact h g.val g.property⟩
  intro a
  obtain ⟨b, hb, h⟩ := boundedEvaluation_of_polynomial_surjective
    (fun g : B => rationalPointAlgebraHom F G.X g.val) π hπ hX a
  exact ⟨b, hb, fun g hg => h ⟨g, hg⟩⟩

/-- On an inverse-stable set, entry bounds already bound inverse entries. -/
theorem isAlgebraicallyBounded_of_entries
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (B : Set (rationalPoints G)) (hBinv : ∀ g ∈ B, g⁻¹ ∈ B)
    (hB : ρ.HasBoundedRationalEntries B) :
    IsAlgebraicallyBounded F G.X B := by
  apply ρ.isAlgebraicallyBounded_of_entries_and_inverse hρ B hB
  intro i j
  obtain ⟨b, hb, h⟩ := hB i j
  refine ⟨b, hb, fun g hg => ?_⟩
  simpa only [map_inv] using h (g⁻¹) (hBinv g hg)

/-- Whole-group entry bounds imply the exact all-regular-functions predicate. -/
theorem isAlgebraicallyBounded_univ_of_entries
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (hB : ρ.HasBoundedRationalEntries Set.univ) :
    IsAlgebraicallyBounded F G.X Set.univ :=
  ρ.isAlgebraicallyBounded_of_entries hρ Set.univ (fun _ _ => Set.mem_univ _) hB

end Langlands.GroupScheme.MatrixRepresentation
