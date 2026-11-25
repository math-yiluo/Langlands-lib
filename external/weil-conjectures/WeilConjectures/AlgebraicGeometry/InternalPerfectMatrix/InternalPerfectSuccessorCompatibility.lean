/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import WeilConjectures.CategoryTheory.FunctorFiniteMatrixCoordinates

/-! # Matrix assembly of successor compatibility -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Expanding the concrete scalar-extension square needs additional type reduction.
/-- Coefficient and basis successor squares imply the successor square for evaluation. -/
theorem evaluation_successor_of_squares (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ)
    (hcoeff : ∀ z : LocallyConstant (ConnectedComponents W)
      (Padic.coefficientExtensionRing l E (n + 2)),
      let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
      Φ.map (coefficientEndEquiv l E W (n + 1) z).asHom ≫
          (Mod.regularExtensionIso (AdicCompletion.transition l E W n)).hom =
        (Mod.regularExtensionIso (AdicCompletion.transition l E W n)).hom ≫
          (coefficientEndEquiv l E W n (z.map (scalarStep l E n))).asHom)
    (hbasis : ∀ i : ℤ,
      let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
      let r := Module.finrank (A l E) (P.X i)
      let B := Φ.mapBiproduct (fun _ : Fin r ↦
        Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
          biproduct.mapIso (fun _ : Fin r ↦
            Mod.regularExtensionIso (AdicCompletion.transition l E W n))
      Φ.map (quotientIso l E W P hfree (n + 1) i).hom ≫ B.hom =
        (internalPerfectOrdinaryReductionStep l E W P n).hom.f i ≫
          (quotientIso l E W P hfree n i).hom)
    (q : ℤ) :
    evaluationHom l E W P hfree (n + 1) q ≫ (successorMap l E W P n).f q =
      (quotientStep l E W P n).f q ≫ evaluationHom l E W P hfree n q := by
  let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
  let α := internalPerfectOrdinaryReductionStep l E W P n
  let r := fun i ↦ Module.finrank (A l E) (P.X i)
  let B := fun i : ℤ ↦ Φ.mapBiproduct (fun _ : Fin (r i) ↦
    Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
      biproduct.mapIso (fun _ : Fin (r i) ↦
        Mod.regularExtensionIso (AdicCompletion.transition l E W n))
  have hleft (i : ℤ) : α.inv.f i ≫
      Φ.map (quotientIso l E W P hfree (n + 1) i).hom =
        (quotientIso l E W P hfree n i).hom ≫ (B i).inv := by
    apply (cancel_mono (B i).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hbasis i, ← Category.assoc]
    have h := congrArg (fun f ↦ f.f i) α.inv_hom_id
    exact congrArg (fun f ↦ f ≫ (quotientIso l E W P hfree n i).hom) h
  have hright (i : ℤ) :
      Φ.map (quotientIso l E W P hfree (n + 1) i).inv ≫ α.hom.f i =
        (B i).hom ≫ (quotientIso l E W P hfree n i).inv := by
    apply (cancel_epi (Φ.map (quotientIso l E W P hfree (n + 1) i).hom)).1
    simp only [← Category.assoc, ← Φ.map_comp, Iso.hom_inv_id, Φ.map_id,
      Category.id_comp]
    rw [hbasis i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm (i j : ℤ) (z : Fin (r i) → Fin (r j) →
      LocallyConstant (ConnectedComponents W) (Padic.coefficientExtensionRing l E (n + 2))) :
      Φ.map (biproduct.matrix (fun s t ↦ (coefficientEndEquiv l E W (n + 1) (z s t)).asHom)) ≫
          (B j).hom =
        (B i).hom ≫ biproduct.matrix (fun s t ↦
          (coefficientEndEquiv l E W n ((z s t).map (scalarStep l E n))).asHom) := by
    dsimp only [B, Iso.trans_hom, biproduct.mapIso_hom]
    rw [← Category.assoc, Functor.mapBiproduct_matrix, Category.assoc, Category.assoc]
    congr 1
    simp only [biproduct.mapIso_hom]
    erw [biproduct.matrix_map, biproduct.map_matrix]
    congr 1
    funext s t
    exact hcoeff (z s t)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  change (((CochainComplex.HomComplex.Cochain.ofHom α.inv).comp
      ((evaluate l E W P hfree (n + 1) q z.down).map Φ) (zero_add q)).comp
        (CochainComplex.HomComplex.Cochain.ofHom α.hom) (add_zero q)).v i j hij =
    (evaluate l E W P hfree n q
      (z.down.map ((Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
        (Nat.succ_le_succ (Nat.le_succ n))).f q))).v i j hij
  simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.map_v,
    Category.assoc]
  dsimp only [evaluate, CochainComplex.HomComplex.Cochain.mk_v]
  simp only [Φ.map_comp, Category.assoc]
  rw [← Category.assoc (α.inv.f i), hleft i]
  simp only [Category.assoc]
  erw [hright j, reassoc_of% (hm i j _)]
  simp only [Iso.inv_hom_id_assoc]
  congr 2
  congr 1
  funext s t
  apply congrArg (fun v ↦ (coefficientEndEquiv l E W n v).asHom)
  apply LocallyConstant.ext
  intro x
  let w : LocallyConstant (ConnectedComponents W)
      ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 2)).X q) := z.down
  exact (ConcreteCategory.congr_hom (quotientEntry_step l E P hfree n q i j hij s t)
    (w x)).symm

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
