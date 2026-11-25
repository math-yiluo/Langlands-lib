/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import WeilConjectures.AlgebraicGeometry.FiniteConstantSectionNaturality
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelOrdinaryScalar

/-! # Coefficient sections under the actual successor transition -/

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

private def coefficientEncoding (W : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (constantSheaf (Scheme.ProEt.topology W) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ⟶
      (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology W)
            (AdicCompletion.finiteRing l E W n)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let e := Classical.choice (FiniteDiscreteOrdinary.encoding_exists B W)
  let c := (constantCommuteCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
      (CommRingCat.of (ULift.{u + 1} B))
  exact c.hom ≫ (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.ringIso.hom

private theorem coefficientEncoding_normalization (W : Scheme.{u}) (n : ℕ)
    (V : W.ProEtᵒᵖ) (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (coefficientEncoding l E W n).hom.app V
        ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app V a) =
      (FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing l E (n + 1)) W).hom.app V
          ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
            (AddCommGrpCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app V a) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let J := Scheme.ProEt.topology W
  let e := Classical.choice (FiniteDiscreteOrdinary.encoding_exists B W)
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
      (CommRingCat.of (ULift.{u + 1} B))
  let cV := (((sheafToPresheaf J RingCat.{u + 1}).mapIso c).app V).ringCatIsoToRingEquiv
  have hu : cV ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
      (RingCat.of (ULift.{u + 1} B)))).app V a) =
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} B)))).app V a := by
    apply cV.symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact (congrArg (fun f ↦ f.app V a) (realizationRingIso_fac J
      (ULift.{u + 1} B))).symm
  change e.ringIso.hom.hom.app V (cV _) = _
  rw [hu]
  exact e.normalization V a

private def sectionScalarMap {W : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology W) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology W) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence W.ProEtᵒᵖ AddCommGrpCat.{u + 1}).functor.map
      ((sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).mapCommMon.map
        (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.Hom.mk' a))))
          InternalAbelianSheafModule.commMonToRing⟩

private def liftedStep (n : ℕ) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom)

private theorem canonicalAbelianMap_transition (W : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (constantSheaf (Scheme.ProEt.topology W) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (liftedStep l E n).toAddMonoidHom) ≫
      FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing l E (n + 1)) W =
    FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing l E (n + 2)) W ≫
      AdicCompletion.transition l E W n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply FiniteDiscreteOrdinary.canonicalAbelianMap_coefficient
    (Padic.coefficientExtensionRing l E (n + 2))
    (Padic.coefficientExtensionRing l E (n + 1)) W
    (AddCommGrpCat.ofHom (liftedStep l E n).toAddMonoidHom)
    (AdicCompletion.transitionRing l E n)
  rfl

private theorem coefficientEncoding_transition (W : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let ρ := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (sectionScalarMap (AdicCompletion.transition l E W n))
    coefficientEncoding l E W (n + 1) ≫ ρ =
      (constantSheaf (Scheme.ProEt.topology W) RingCat.{u + 1}).map
        (RingCat.ofHom (liftedStep l E n)) ≫ coefficientEncoding l E W n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let J := Scheme.ProEt.topology W
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2))
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J
        (AdicCompletion.finiteRing l E W n))).property)
  ext V a
  have hnR := congrArg (fun f ↦ f.app V a)
    (toSheafify_naturality J ((Functor.const W.ProEtᵒᵖ).map
      (RingCat.ofHom (liftedStep l E n))))
  have hnA := congrArg (fun f ↦ f.app V a)
    (toSheafify_naturality J ((Functor.const W.ProEtᵒᵖ).map
      (AddCommGrpCat.ofHom (liftedStep l E n).toAddMonoidHom)))
  have h := congrArg (fun f ↦ f.hom.app V
    (((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V) a))
      (canonicalAbelianMap_transition l E W n)
  change (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app V
      (liftedStep l E n a) =
    (((constantSheaf J RingCat.{u + 1}).map (RingCat.ofHom (liftedStep l E n))).hom.app V)
      ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a) at hnR
  change (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app V
      (liftedStep l E n a) =
    (((constantSheaf J Ab.{u + 1}).map
      (AddCommGrpCat.ofHom (liftedStep l E n).toAddMonoidHom)).hom.app V)
      ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V a) at hnA
  change (AdicCompletion.transition l E W n).hom.app V
      ((coefficientEncoding l E W (n + 1)).hom.app V
        ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a)) =
    (coefficientEncoding l E W n).hom.app V
      ((((constantSheaf J RingCat.{u + 1}).map
        (RingCat.ofHom (liftedStep l E n))).hom.app V)
          ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app V a))
  erw [← hnR, coefficientEncoding_normalization, coefficientEncoding_normalization]
  change (FiniteDiscreteOrdinary.canonicalAbelianMap
      (Padic.coefficientExtensionRing l E (n + 1)) W).hom.app V
        ((((constantSheaf J Ab.{u + 1}).map
          (AddCommGrpCat.ofHom (liftedStep l E n).toAddMonoidHom)).hom.app V)
            ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
              (AddCommGrpCat.of A))).app V a)) = _ at h
  erw [← hnA] at h
  exact h.symm

private theorem coefficientSection_eval (W : Scheme.{u}) (n : ℕ)
    (z : LocallyConstant (ConnectedComponents W)
      (Padic.coefficientExtensionRing l E (n + 1))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
      finiteQuotient_discrete l E n
    let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
    Sheaf.unitHomEval U (coefficientSection l E W n z) =
      (coefficientEncoding l E W n).hom.app (op U)
        (((proEtale_finite_constant_sections W
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).choose U).symm
            (componentsContinuousEquiv W _ z)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let J := Scheme.ProEt.topology W
  let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
  change (InternalAbelianSheafModule.sectionGlobalEquiv J
    (AdicCompletion.finiteRing l E W n) U (Scheme.ProEt.isTerminalMkId W))
      ((InternalAbelianSheafModule.sectionGlobalEquiv J
        (AdicCompletion.finiteRing l E W n) U (Scheme.ProEt.isTerminalMkId W)).symm _) = _
  exact RingEquiv.apply_symm_apply _ _

-- The coefficient encoding square needs additional sheaf-instance reduction.
/-- Locally constant finite coefficient sections reduce by the actual coefficient map. -/
theorem coefficientSection_step (W : Scheme.{u}) (n : ℕ)
    (z : LocallyConstant (ConnectedComponents W)
      (Padic.coefficientExtensionRing l E (n + 2))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    coefficientSection l E W (n + 1) z ≫ AdicCompletion.transition l E W n =
      coefficientSection l E W n (z.map (scalarStep l E n)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 2)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 2) (by omega)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := finiteQuotient_discrete l E (n + 1)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let J := Scheme.ProEt.topology W
  let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
  let θA := (proEtale_finite_constant_sections W (ULift.{u + 1} A)).choose
  let θB := (proEtale_finite_constant_sections W (ULift.{u + 1} B)).choose
  let a := (θA U).symm (componentsContinuousEquiv W A z)
  let b := (θB U).symm (componentsContinuousEquiv W B (z.map (scalarStep l E n)))
  have hs : (((constantSheaf J RingCat.{u + 1}).map
      (RingCat.ofHom (liftedStep l E n))).hom.app (op U)) a = b := by
    apply (θB U).injective
    change _ = (θB U) ((θB U).symm _)
    rw [RingEquiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro x
    rw [proEtale_finite_constant_sections_coefficient]
    change liftedStep l E n ((θA U) ((θA U).symm _) x) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have h := congrArg (fun f ↦ f.hom.app (op U) a)
    (coefficientEncoding_transition l E W n)
  change (AdicCompletion.transition l E W n).hom.app (op U)
      ((coefficientEncoding l E W (n + 1)).hom.app (op U) a) =
    (coefficientEncoding l E W n).hom.app (op U)
      ((((constantSheaf J RingCat.{u + 1}).map
        (RingCat.ofHom (liftedStep l E n))).hom.app (op U)) a) at h
  rw [hs] at h
  apply Sheaf.unitHomEval_injective (Scheme.ProEt.isTerminalMkId W)
    (AdicCompletion.finiteRing l E W n)
  change (AdicCompletion.transition l E W n).hom.app (op U)
      (Sheaf.unitHomEval (F := AdicCompletion.finiteRing l E W (n + 1)) U
        (coefficientSection l E W (n + 1) z)) =
    Sheaf.unitHomEval (F := AdicCompletion.finiteRing l E W n) U
      (coefficientSection l E W n (z.map (scalarStep l E n)))
  exact (congrArg ((AdicCompletion.transition l E W n).hom.app (op U))
      (coefficientSection_eval l E W (n + 1) z)).trans
    (h.trans (coefficientSection_eval l E W n (z.map (scalarStep l E n))).symm)

/-- Regular multiplication by a locally constant entry commutes with successor extension. -/
theorem coefficientEnd_step (W : Scheme.{u}) (n : ℕ)
    (z : LocallyConstant (ConnectedComponents W)
      (Padic.coefficientExtensionRing l E (n + 2))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
    Φ.map (coefficientEndEquiv l E W (n + 1) z).asHom ≫
        (Mod.regularExtensionIso (AdicCompletion.transition l E W n)).hom =
      (Mod.regularExtensionIso (AdicCompletion.transition l E W n)).hom ≫
        (coefficientEndEquiv l E W n (z.map (scalarStep l E n))).asHom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have h := FiniteModelQuotient.extendRegular_lift (AdicCompletion.transition l E W n)
    (coefficientSection l E W (n + 1) z)
  rw [coefficientSection_step] at h
  exact h

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
