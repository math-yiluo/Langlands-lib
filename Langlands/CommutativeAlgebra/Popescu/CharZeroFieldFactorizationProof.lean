import Langlands.CommutativeAlgebra.Popescu.CharZeroFieldFactorizationStatement
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Proof: field extensions in characteristic zero have smooth factorizations -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 10.158.11 (07BV) in characteristic zero, in the mapping form of property PT. -/
theorem charZeroFieldFactorization : CharZeroFieldFactorizationStatement.{u} := by
  intro K L _ _ _ _ A _ _ _ f
  classical
  set D := f.range
  have : Algebra.FiniteType K D :=
    Algebra.FiniteType.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Algebra.FinitePresentation K D := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsFractionRing D (Localization.AtPrime (⊥ : Ideal D)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal D).primeCompl)
  let _ : Field (Localization.AtPrime (⊥ : Ideal D)) := IsFractionRing.toField D
  have : Algebra.IsSmoothAt K (⊥ : Ideal D) := Algebra.FormallySmooth.of_perfectField
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth K (⊥ : Ideal D)
  have hgu : IsUnit (D.val g) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hg ((Submodule.mem_bot _).mpr (Subtype.ext h0))
  let h₀ : Localization.Away g →+* L := IsLocalization.Away.lift g (g := D.val.toRingHom) hgu
  let h : Localization.Away g →ₐ[K] L :=
    { h₀ with
      commutes' := fun c => by
        show h₀ (algebraMap K _ c) = _
        rw [IsScalarTower.algebraMap_apply K D (Localization.Away g)]
        exact (IsLocalization.Away.lift_eq g hgu (algebraMap K D c)).trans (D.val.commutes c) }
  refine ⟨Localization.Away g, inferInstance, inferInstance, hsm,
    (IsScalarTower.toAlgHom K D (Localization.Away g)).comp f.rangeRestrict, h, ?_⟩
  ext x
  show h₀ (algebraMap D _ (f.rangeRestrict x)) = f x
  rw [IsLocalization.Away.lift_eq]
  rfl

end Langlands.CommutativeAlgebra.Popescu
