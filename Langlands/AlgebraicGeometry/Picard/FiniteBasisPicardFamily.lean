import Langlands.AlgebraicGeometry.Picard.FirstOrderPicardFamily
import Mathlib.LinearAlgebra.Dimension.Free

/-! # An actual Picard family realizing a finite tangent basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteBasisPicardFamily

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [IsProper f]

section ChosenBasis

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  (b : Basis ι K (ArtinianDualNumberComparison.Classes f M))

/-- The weighted restrictions of a basis family are its inverse coordinate map. -/
lemma family_basis_weighted (c : ι → K) :
    Quotient.mk _ ((ArtinianTestDeformations.restrict f M
      (FiniteTangents.weighted k K c)).obj
        (FiniteTangentFamily.family f M b)) = b.equivFun.symm c := by
  rw [Basis.equivFun_symm_apply]
  exact FiniteTangentFamily.family_weighted f M b c

/-- Coefficients classify all actual pointed tangent restrictions for a finite basis. -/
theorem basisFamily_bijective : Function.Bijective
    (fun c : ι → K ↦ Quotient.mk (isIsomorphicSetoid _) ((ArtinianTestDeformations.restrict f M
      (FiniteTangents.weighted k K c)).obj (FiniteTangentFamily.family f M b))) := by
  have h : (fun c : ι → K ↦ Quotient.mk (isIsomorphicSetoid _)
      ((ArtinianTestDeformations.restrict f M
        (FiniteTangents.weighted k K c)).obj (FiniteTangentFamily.family f M b))) =
      b.equivFun.symm := funext (family_basis_weighted f M b)
  rw [h]
  exact b.equivFun.symm.bijective

/-- Every actual pointed dual-number object has a unique coefficient vector. -/
theorem basisFamily_existsUnique_parameter
    (L : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)) :
    ∃! c : ι → K, Nonempty
      (((ArtinianTestDeformations.restrict f M
        (FiniteTangents.weighted k K c)).obj (FiniteTangentFamily.family f M b)) ≅ L) := by
  refine ⟨b.equivFun (Quotient.mk _ L), ?_, ?_⟩
  · have h := (family_basis_weighted f M b (b.equivFun (Quotient.mk _ L))).trans
      (b.equivFun.symm_apply_apply (Quotient.mk _ L))
    have hi := Quotient.exact h
    exact hi
  · intro c hc
    apply b.equivFun.symm.injective
    rw [b.equivFun.symm_apply_apply, ← family_basis_weighted]
    exact Quotient.sound hc

end ChosenBasis

/-- A finite basis index retaining the universe of the actual residue field. -/
abbrev Index : Type u :=
  ULift.{u} (Fin (Module.finrank K (ArtinianDualNumberComparison.Classes f M)))

/-- A chosen basis of the actual pointed first-order classes. -/
def basis : Basis (Index f M) K (ArtinianDualNumberComparison.Classes f M) := by
  letI := ArtinianDualNumberComparison.finiteDimensional_classes f M
  exact (Module.finBasis K (ArtinianDualNumberComparison.Classes f M)).reindex
    Equiv.ulift.symm

/-- The actual finite split square-zero parameter test. -/
abbrev test : ArtinianTest k K :=
  FiniteTangents.test k K (Index f M)

/-- An actual pointed line bundle simultaneously realizing the chosen basis. -/
abbrev family : ArtinianTestDeformations.Deformations f M (test f M) :=
  FiniteTangentFamily.family f M (basis f M)

/-- The actual parameter arrow associated to a coefficient vector. -/
abbrev parameter (c : Index f M → K) : test f M ⟶ ArtinianTest.dualNumbers k K :=
  FiniteTangents.weighted k K c

/-- The coefficient-to-class correspondence is a linear equivalence. -/
def parameterLinearEquiv :
    (Index f M → K) ≃ₗ[K] ArtinianDualNumberComparison.Classes f M :=
  (basis f M).equivFun.symm

/-- The chosen finite basis family has the inverse coordinate map as restriction classes. -/
theorem family_weighted (c : Index f M → K) :
    Quotient.mk _ ((ArtinianTestDeformations.restrict f M
      (FiniteTangents.weighted k K c)).obj
        (FiniteTangentFamily.family f M (basis f M))) = (basis f M).equivFun.symm c :=
  family_basis_weighted f M (basis f M) c

/-- Every actual pointed dual-number object is obtained up to pointed isomorphism,
with a unique coefficient vector. -/
theorem existsUnique_parameter
    (L : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K)) :
    ∃! c : Index f M → K, Nonempty
      (((ArtinianTestDeformations.restrict f M
        (FiniteTangents.weighted k K c)).obj
          (FiniteTangentFamily.family f M (basis f M))) ≅ L) :=
  basisFamily_existsUnique_parameter f M (basis f M) L

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteBasisPicardFamily
