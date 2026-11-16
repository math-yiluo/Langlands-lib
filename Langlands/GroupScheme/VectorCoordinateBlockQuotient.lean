import Langlands.GroupScheme.VectorCoordinateBlock
import Mathlib.Logic.Equiv.Set

/-! # Fppf coordinate projections over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup.CoordinateBlock

variable (R : CommRingCat.{u}) {d m : ℕ} (I : Set (Fin d)) (σ : Fin m ≃ I)

/-- Restriction to an enumerated block of standard vector coordinates. -/
abbrev coordinateProjection :
    VectorGroup.groupScheme R d ⟶ VectorGroup.groupScheme R m :=
  blockRestriction (VectorGroup.coordinates R d) I σ
    (fun _ _ f v => VectorGroup.coordinates_comp f v)

/-- Coordinate functions selected from a standard polynomial vector group are primitive. -/
theorem isPrimitiveFamily_coordinates :
    VectorGroup.IsPrimitiveFamily (VectorGroup.corepresentableBy R d)
      (fun a : Fin m => (X (σ a).val : MvPolynomial (Fin d) R)) := by
  intro A x y a
  change aeval (Multiplicative.toAdd (x * y)) (X (σ a).val) =
    aeval (Multiplicative.toAdd x) (X (σ a).val) +
      aeval (Multiplicative.toAdd y) (X (σ a).val)
  simp only [aeval_X]
  rfl

/-- The selected and complementary variables together are polynomial coordinates.
The complement is lifted to the base-ring universe. -/
theorem bijective_aeval_coordinates :
    Function.Bijective
      (aeval (Sum.elim
        (fun a : Fin m => (X (σ a).val : MvPolynomial (Fin d) R))
        (fun a : ULift.{u} ↥(Iᶜ) => (X a.down.val : MvPolynomial (Fin d) R))) :
        MvPolynomial (Fin m ⊕ ULift.{u} ↥(Iᶜ)) R →ₐ[R] MvPolynomial (Fin d) R) := by
  let τ : Fin m ⊕ ULift.{u} ↥(Iᶜ) ≃ Fin d :=
    (Equiv.sumCongr σ Equiv.ulift).trans (Equiv.Set.sumCompl I)
  have h : (aeval (Sum.elim
        (fun a : Fin m => (X (σ a).val : MvPolynomial (Fin d) R))
        (fun a : ULift.{u} ↥(Iᶜ) => (X a.down.val : MvPolynomial (Fin d) R))) :
        MvPolynomial (Fin m ⊕ ULift.{u} ↥(Iᶜ)) R →ₐ[R] MvPolynomial (Fin d) R) =
      (renameEquiv R τ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro a
    cases a <;> simp [τ]
  rw [h]
  exact (renameEquiv R τ).bijective

/-- The geometric coordinate restriction agrees with the primitive-coordinate map. -/
theorem coordinateProjection_eq_quotientMap :
    coordinateProjection R I σ =
      VectorGroup.quotientMap (isPrimitiveFamily_coordinates R I σ) := by
  apply hom_ext_points
  intro T x
  apply VectorGroup.points_ext
  intro a
  rw [VectorGroup.coordinates_quotientMap_eq_appTop,
    comp_blockRestriction, blockRestrictionPoints_coord,
    VectorGroup.coordinates_apply]
  rfl

/-- Coordinate restriction is flat over every commutative base ring. -/
theorem flat_coordinateProjection :
    Flat (coordinateProjection R I σ).hom.hom.left := by
  rw [coordinateProjection_eq_quotientMap]
  exact VectorGroup.flat_quotientMap (isPrimitiveFamily_coordinates R I σ)
    (bijective_aeval_coordinates R I σ)

/-- Coordinate restriction is locally of finite presentation. -/
theorem locallyOfFinitePresentation_coordinateProjection :
    LocallyOfFinitePresentation (coordinateProjection R I σ).hom.hom.left := by
  rw [coordinateProjection_eq_quotientMap]
  exact VectorGroup.locallyOfFinitePresentation_quotientMap
    (isPrimitiveFamily_coordinates R I σ) (bijective_aeval_coordinates R I σ)

/-- Coordinate restriction is surjective as a map of schemes. -/
theorem surjective_coordinateProjection :
    Surjective (coordinateProjection R I σ).hom.hom.left := by
  rw [coordinateProjection_eq_quotientMap]
  exact VectorGroup.surjective_quotientMap (isPrimitiveFamily_coordinates R I σ)
    (bijective_aeval_coordinates R I σ)

/-- Any subgroup with exactly the vanishing selected coordinates is the represented
fppf kernel of coordinate restriction. -/
theorem isFppfQuotient_coordinateProjection
    (N : SubgroupFunctor (VectorGroup.groupScheme R d))
    (hN : ∀ (T : Over (Spec R)) (x : T ⟶ (VectorGroup.groupScheme R d).X),
      x ∈ N.carrier T ↔
        ∀ a : Fin m, (VectorGroup.coordinates R d T x).toAdd (σ a).val = 0) :
    RelativeRoot.IsFppfQuotient N (coordinateProjection R I σ) := by
  refine ⟨flat_coordinateProjection R I σ, surjective_coordinateProjection R I σ,
    locallyOfFinitePresentation_coordinateProjection R I σ, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  constructor
  · intro h
    apply (hN T x).2
    intro a
    have ha := congrArg (fun z => (VectorGroup.coordinates R m T z).toAdd a) h
    simpa only [comp_blockRestriction, blockRestrictionPoints_coord, map_one, toAdd_one, Pi.zero_apply] using ha
  · intro h
    apply VectorGroup.points_ext
    intro a
    rw [comp_blockRestriction, blockRestrictionPoints_coord, (hN T x).1 h a, map_one]
    rfl

end Langlands.GroupScheme.VectorGroup.CoordinateBlock
