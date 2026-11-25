/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport

/-! # Finite freeness of the completed scalar coefficient inclusion

## References

* Bhatt--Scholze, Lemma 6.8.2(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

/-- The completed target integral coefficients are finite free over the source ones. -/
theorem pbcScalarCoefficient_finiteFree (T : Scheme.{u}) :
    ∃ d : ℕ, Nonempty ((proEtaleRingRestrictScalars (pbcScalarCoefficientMap l E F i T)).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (pbcAdicCompletion T (pbcIntegralDatum l F)))) ≅
      ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (pbcAdicCompletion T (pbcIntegralDatum l E)))) := by
  classical
  let FC := adicLisseForget T
  let eR := WeilConjectures.purCoefficientIso l E T
  let eS := WeilConjectures.purCoefficientIso l F T
  let φ' := WeilConjectures.completedCoefficientMap l E F i T
  have hmap : WeilConjectures.integralCompletedScalarMap l E F i T = φ' := by
    apply (WeilConjectures.completedCoefficientMap_existsUnique l E F i T).unique
    · exact (WeilConjectures.integralCompletedScalarMap_existsUnique l E F i T).exists.choose_spec
    · exact (WeilConjectures.completedCoefficientMap_existsUnique l E F i T).exists.choose_spec
  have hsq := scalarComplete_coefficientScalar_square l E F i T
  rw [hmap] at hsq
  change eR.hom ≫ φ' = pbcScalarCoefficientMap l E F i T ≫ eS.hom at hsq
  have hinv : φ' ≫ eS.inv = eR.inv ≫ pbcScalarCoefficientMap l E F i T := by
    apply (Iso.comp_inv_eq eS).mpr
    rw [Category.assoc]
    exact ((Iso.inv_comp_eq eR).mpr hsq.symm).symm
  have hb := WeilConjectures.completedIntegralFiniteFree l E T F i φ'
    (WeilConjectures.completedCoefficientMap_existsUnique l E F i T).exists.choose_spec
  obtain ⟨b⟩ := hb
  have h : FC.map φ' ≫ (FC.mapIso eS).symm.hom =
      (FC.mapIso eR).symm.hom ≫ FC.map (pbcScalarCoefficientMap l E F i T) := by
    simp only [Iso.symm_hom, Functor.mapIso_inv, ← FC.map_comp, hinv]
  let := i.toAlgebra
  exact ⟨Module.finrank E F, WeilConjectures.freeTransport (FC.mapIso eR).symm
    (FC.mapIso eS).symm (FC.map φ') (FC.map (pbcScalarCoefficientMap l E F i T)) h
    (Module.finrank E F) b⟩

end AlgebraicGeometry.Scheme
