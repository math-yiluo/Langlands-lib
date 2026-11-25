/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectBasisCoordinates
import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectDifferentialEntries
import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.FiniteMatrixRingEvaluation

/-! # The fixed matrix evaluation respects the signed differential -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Matrix evaluation carries the actual scalar quotient differential to the signed
Hom differential of the ordinary quotient model. -/
theorem evaluation_differential (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q r : ℤ) :
    evaluationHom l E W P hfree n q ≫
        (CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W P n)
          (internalPerfectOrdinaryReduction l E W P n)).d q r =
      (quotientCochains l E W P n).d q r ≫ evaluationHom l E W P hfree n r := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  by_cases hqr : q + 1 = r
  · subst r
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change CochainComplex.HomComplex.δ q (q + 1)
      (evaluate l E W P hfree n q z.down) =
        evaluate l E W P hfree n (q + 1)
          (z.down.map ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (n + 1)).d q (q + 1)))
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    rw [CochainComplex.HomComplex.δ_v q (q + 1) rfl _ i j hij (i + q) (i + 1)
      (by omega) rfl]
    dsimp only [evaluate, CochainComplex.HomComplex.Cochain.mk_v]
    have hd (i j : ℤ) :
        (internalPerfectOrdinaryReduction l E W P n).d i j ≫
            (quotientIso l E W P hfree n j).hom =
          (quotientIso l E W P hfree n i).hom ≫
            biproduct.matrix (fun s t ↦ (coefficientEndEquiv l E W n
              (LocallyConstant.const _ (Ideal.Quotient.mk
                (Padic.coefficientExtensionIdeal l E (n + 1))
                  (mapEntry l E P hfree i j (P.d i j) s t)))).asHom) :=
      quotientIso_map l E W P hfree n i j (P.d i j)
    have hd' (i j : ℤ) :
        (internalPerfectOrdinaryReduction l E W P n).d i j =
          (quotientIso l E W P hfree n i).hom ≫
            biproduct.matrix (fun s t ↦ (coefficientEndEquiv l E W n
              (LocallyConstant.const _ (Ideal.Quotient.mk
                (Padic.coefficientExtensionIdeal l E (n + 1))
                  (mapEntry l E P hfree i j (P.d i j) s t)))).asHom) ≫
              (quotientIso l E W P hfree n j).inv := by
      apply (cancel_mono (quotientIso l E W P hfree n j).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hd i j
    rw [hd' (i + q) j, hd' i (i + 1)]
    apply (cancel_epi (quotientIso l E W P hfree n i).inv).1
    apply (cancel_mono (quotientIso l E W P hfree n j).hom).1
    simp only [Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
      Linear.comp_units_smul, Linear.units_smul_comp, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    let M := Mod.regular (AdicCompletion.finiteRing l E W n)
    let e := (coefficientEndEquiv l E W n).toRingHom
    erw [ringMatrix_comp M e, ringMatrix_comp M e,
      ← ringMatrix_units_smul M e, ← ringMatrix_add M e]
    congr 1
    funext s t
    exact congrArg (fun z ↦ (e z).asHom)
      (locallyConstant_quotientEntry_differential l E (ConnectedComponents W)
        P hfree n q i j hij s t z.down).symm
  · rw [(CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W P n)
        (internalPerfectOrdinaryReduction l E W P n)).shape q r hqr,
      (quotientCochains l E W P n).shape q r hqr]
    simp

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
