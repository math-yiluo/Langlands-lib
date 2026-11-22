import Langlands.Galois.QuadraticFrobeniusPatching.Arithmetic
import Langlands.Galois.QuadraticFrobeniusPatching.Character

/-! # Quadratic patching from geometric Frobenius polynomials -/

noncomputable section

universe uF uC uV

namespace Langlands.GaloisRepresentation

open Filter IsDedekindDomain Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension QuadraticFrobeniusPatching
open scoped NumberField

/-- The geometric Frobenius polynomial formula supplies the two intertwining
hypotheses of quadratic patching and recovers the polynomial at split places. -/
theorem quadraticFrobeniusPatching : QuadraticFrobeniusPatchingStatement.{uF, uC, uV} := by
  intro hpatch F _ _ C _ _ _ _ _ _ n S I R P hquadratic habundant hR hP hmatching
  obtain ⟨A, ⟨hrank, hsemisimple, hrestriction⟩, _⟩ :=
    hpatch F C n S I R hquadratic habundant hR (by
      intro N σ
      let : NumberField N.val := NumberField.of_module_finite F N.val
      apply equiv_of_eventually_hasEulerPolynomialAt
        (isSemisimple_pullback_of_surjective _ σ.surjective (hR N).2) (hR N).2
      filter_upwards [eventually_hasEulerPolynomialAt_pullback_aut σ (hmatching N),
        (tendsto_under_cofinite (K := F) (L := N.val)).eventually (hmatching N)] with w hσ hw
      exact ⟨_, hσ, hw ⟨w, liesOver_under w⟩⟩) (by
      intro N M
      let T := N.val ⊔ M.val
      let iN : N.val →ₐ[F] T := IntermediateField.inclusion
        (le_sup_left (a := N.val.toIntermediateField) (b := M.val.toIntermediateField))
      let iM : M.val →ₐ[F] T := IntermediateField.inclusion
        (le_sup_right (a := N.val.toIntermediateField) (b := M.val.toIntermediateField))
      let : Algebra N.val T := iN.toRingHom.toAlgebra
      let : Algebra M.val T := iM.toRingHom.toAlgebra
      let : IsScalarTower F N.val T := IsScalarTower.of_algebraMap_eq fun x => (iN.commutes x).symm
      let : IsScalarTower F M.val T := IsScalarTower.of_algebraMap_eq fun x => (iM.commutes x).symm
      let : NumberField N.val := NumberField.of_module_finite F N.val
      let : NumberField M.val := NumberField.of_module_finite F M.val
      let : NumberField T := NumberField.of_module_finite F T
      let : IsGalois N.val T := IsGalois.tower_top_of_isGalois F N.val T
      let : IsGalois M.val T := IsGalois.tower_top_of_isGalois F M.val T
      change Nonempty (FiniteRepresentation.Equiv
        (pullback (algebraMap N.val T) (R N)).val (pullback (algebraMap M.val T) (R M)).val)
      apply equiv_of_eventually_hasEulerPolynomialAt
        (isSemisimple_pullback_of_isGalois (hR N).2) (isSemisimple_pullback_of_isGalois (hR M).2)
      have hN := eventually_hasEulerPolynomialAt_pullback (E := T)
        (fun v => (hP v).2.trans (hR N).1.symm) (hmatching N)
      have hM := eventually_hasEulerPolynomialAt_pullback (E := T)
        (fun v => (hP v).2.trans (hR M).1.symm) (hmatching M)
      filter_upwards [hN, hM] with z hzN hzM
      exact ⟨_, hzN, hzM⟩)
  refine ⟨A, hrank, hsemisimple, hrestriction, ?_⟩
  intro N
  let : NumberField N.val := NumberField.of_module_finite F N.val
  intro v w hs hw
  obtain ⟨e⟩ := hrestriction N
  exact hasEulerPolynomialAt_of_splitsCompletely v w.val hs
    ((hasEulerPolynomialAt_equiv e w.val (P v).reverse).mpr hw)

end Langlands.GaloisRepresentation
