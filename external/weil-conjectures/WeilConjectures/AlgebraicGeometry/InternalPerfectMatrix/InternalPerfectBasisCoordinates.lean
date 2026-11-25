/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import WeilConjectures.CategoryTheory.FunctorFiniteMatrixCoordinates
import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectRankOneCoordinates

/-! # Chosen finite bases and ordinary matrix coordinates
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The lifted integral basis, with its target written as a categorical biproduct. -/
def liftedBasisIso (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i : ℤ) :
    (ModuleCat.uliftFunctor.{u + 1, u} (A l E)).obj (P.X i) ≅
      ⨁ fun _ : Fin (Module.finrank (A l E) (P.X i)) ↦
        ModuleCat.of (A l E) (ULift.{u + 1} (A l E)) := by
  let r := Module.finrank (A l E) (P.X i)
  let e : (ModuleCat.uliftFunctor.{u + 1, u} (A l E)).obj (P.X i) ≅
      FiniteConstantModel.freeScalars (A l E) r :=
    (((ULift.moduleEquiv : ULift.{u + 1} (P.X i) ≃ₗ[A l E] P.X i).trans
      (basis l E P hfree i).equivFun).trans
      (LinearEquiv.piCongrRight fun _ : Fin r ↦ ULift.moduleEquiv.symm)).toModuleIso
  exact e ≪≫ (ModuleCat.biproductIsoPi (fun _ : Fin r ↦
    ModuleCat.of (A l E) (ULift.{u + 1} (A l E)))).symm

private theorem biproductIsoPi_ι (r : ℕ) (s : Fin r) :
    biproduct.ι (fun _ : Fin r ↦ ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) s ≫
      (ModuleCat.biproductIsoPi _).hom = ModuleCat.ofHom
        (LinearMap.single (A l E) (fun _ : Fin r ↦ ULift.{u + 1} (A l E)) s) := by
  classical
  apply (cancel_mono (ModuleCat.biproductIsoPi _).inv).1
  apply biproduct.hom_ext
  intro t
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [ModuleCat.biproductIsoPi_inv_comp_π, biproduct.ι_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only []
  split_ifs <;> simp_all

/-- Conjugating an arbitrary linear map by the lifted bases gives its ordinary matrix. -/
theorem liftedBasisIso_matrix
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i j : ℤ) (f : P.X i ⟶ P.X j) :
    (liftedBasisIso l E P hfree i).inv ≫
      (ModuleCat.uliftFunctor.{u + 1, u} (A l E)).map f ≫
        (liftedBasisIso l E P hfree j).hom =
      biproduct.matrix (fun s t ↦ ModuleCat.ofHom
        (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E))
          ((basis l E P hfree j).repr (f ((basis l E P hfree i) s)) t))) := by
  classical
  apply biproduct.hom_ext'
  intro s
  apply biproduct.hom_ext
  intro t
  simp only [liftedBasisIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_π]
  erw [← Category.assoc (biproduct.ι _ s), biproductIsoPi_ι,
    ModuleCat.biproductIsoPi_inv_comp_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hb : (basis l E P hfree i).equivFun.symm
      (fun k ↦ ((Pi.single s x : Fin (Module.finrank (A l E) (P.X i)) →
        ULift.{u + 1} (A l E)) k).down) = x.down • (basis l E P hfree i) s := by
    apply (basis l E P hfree i).equivFun.injective
    rw [LinearEquiv.apply_symm_apply, map_smul]
    ext k
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, Pi.single_apply]
    by_cases h : k = s
    · subst k; simp
    · simp [h]
  change ULift.up ((basis l E P hfree j).equivFun
    (f ((basis l E P hfree i).equivFun.symm
      (fun k ↦ ((Pi.single s x : Fin (Module.finrank (A l E) (P.X i)) →
        ULift.{u + 1} (A l E)) k).down))) t) =
      ULift.up (((basis l E P hfree j).repr (f ((basis l E P hfree i) s)) t) * x.down)
  rw [hb, map_smul, map_smul]
  apply ULift.ext
  exact mul_comm _ _

-- The composite realization functor needs additional instance and type reduction.
/-- The already fixed quotient bases are the biproduct comparison of the composite
realization functor, with the normalized rank-one quotient comparison. -/
theorem quotientIso_factor (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (i : ℤ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI : (FiniteConstantModel.modelFunctor (A l E) W).Additive :=
      (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
    let F := FiniteConstantModel.modelFunctor (A l E) W
    let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
    let H := F ⋙ G
    let S := ModuleCat.of (A l E) (ULift.{u + 1} (A l E))
    let e := G.mapIso (integralRegular l E W) ≪≫
      Mod.regularExtensionIso (AdicCompletion.quotient l E W n)
    (quotientIso l E W P hfree n i).hom =
      H.map (liftedBasisIso l E P hfree i).hom ≫
        (H.mapBiproduct (fun _ : Fin (Module.finrank (A l E) (P.X i)) ↦ S)).hom ≫
          biproduct.map (fun _ ↦ e.hom) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := FiniteConstantModel.modelFunctor (A l E) W
  let : F.Additive :=
    (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
  let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let S := ModuleCat.of (A l E) (ULift.{u + 1} (A l E))
  let r := Module.finrank (A l E) (P.X i)
  change G.map (F.map (liftedBasisIso l E P hfree i).hom ≫
      (F.mapBiproduct (fun _ : Fin r ↦ S)).hom ≫
        biproduct.map (fun _ ↦ (integralRegular l E W).hom)) ≫
    (G.mapBiproduct (fun _ : Fin r ↦ Mod.regular (AdicCompletion.ring l E W))).hom ≫
      biproduct.map (fun _ ↦
        (Mod.regularExtensionIso (AdicCompletion.quotient l E W n)).hom) = _
  rw [Functor.mapBiproduct_composite F G]
  simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [reassoc_of% (Functor.mapBiproduct_map G
    (fun _ : Fin r ↦ (integralRegular l E W).hom))]
  simp only [← Functor.biproduct_map_comp, Functor.comp_map]
  rfl

-- The composite realization functor needs additional instance and type reduction.
/-- Every realized integral linear map has the matrix of its constant residue entries
in the fixed quotient bases. -/
theorem quotientIso_map (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (i j : ℤ) (f : P.X i ⟶ P.X j) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let F := FiniteConstantModel.modelFunctor (A l E) W
    let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
    let U := ModuleCat.uliftFunctor.{u + 1, u} (A l E)
    G.map (F.map (U.map f)) ≫ (quotientIso l E W P hfree n j).hom =
      (quotientIso l E W P hfree n i).hom ≫
        biproduct.matrix (fun s t ↦ (coefficientEndEquiv l E W n
          (LocallyConstant.const _ (Ideal.Quotient.mk
            (Padic.coefficientExtensionIdeal l E (n + 1))
              ((basis l E P hfree j).repr (f ((basis l E P hfree i) s)) t)))).asHom) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := FiniteConstantModel.modelFunctor (A l E) W
  let : F.Additive :=
    (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
  let G := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let H := F ⋙ G
  let U := ModuleCat.uliftFunctor.{u + 1, u} (A l E)
  let v := fun s t ↦ (basis l E P hfree j).repr (f ((basis l E P hfree i) s)) t
  have hm : U.map f ≫ (liftedBasisIso l E P hfree j).hom =
      (liftedBasisIso l E P hfree i).hom ≫ biproduct.matrix (fun s t ↦
        ModuleCat.ofHom (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) (v s t))) := by
    apply (cancel_epi (liftedBasisIso l E P hfree i).inv).1
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact liftedBasisIso_matrix l E P hfree i j f
  rw [quotientIso_factor, quotientIso_factor]
  change H.map (U.map f) ≫ (H.map (liftedBasisIso l E P hfree j).hom ≫ _) = _
  rw [← Category.assoc, ← H.map_comp, hm, H.map_comp, Category.assoc]
  simp only [Category.assoc]
  erw [quotientFreeMatrix_scalar l E W n
    (Module.finrank (A l E) (P.X i)) (Module.finrank (A l E) (P.X j)) v]
  rfl

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
