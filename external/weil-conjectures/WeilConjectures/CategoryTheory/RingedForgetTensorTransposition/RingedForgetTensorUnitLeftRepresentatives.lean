/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Normalized unit comparison for ringed tensor functors
Source: Stacks 0FPT (blueprint: lem-sf-ringed-forget-tensor-unit-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep fixed derived-category constructions behind their APIs during elaboration.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

section Generic
variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {HB : Bᵒᵖ × B ⥤ B} {HA : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure HB) (T : CoefficientClosedStructure HA)
  (F : B ⥤ A) (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

private theorem left_unit_of_models
    (P O X : B) (P' O' X' : A)
    (i : X ≅ S.tensor.obj (O, P)) (j : X' ≅ T.tensor.obj (O', P'))
    (aP : F.obj P ≅ P') (aO : F.obj O ≅ O') (c : F.obj X ≅ X')
    (uB : S.monoidal.tensorUnit ≅ O) (uA : T.monoidal.tensorUnit ≅ O')
    (b : X ⟶ P) (b' : X' ⟶ P')
    (hm : F.map i.hom ≫ μ.hom.app (O, P) ≫
      T.tensor.map (X := (F.obj O, F.obj P)) (Y := (O', P')) (aO.hom, aP.hom) =
      c.hom ≫ j.hom)
    (hb : i.hom ≫ S.tensor.map (X := (O, P)) (Y := (S.monoidal.tensorUnit, P))
      (uB.inv, 𝟙 P) ≫ (S.monoidal.leftUnitor P).hom = b)
    (hb' : j.hom ≫ T.tensor.map (X := (O', P')) (Y := (T.monoidal.tensorUnit, P'))
      (uA.inv, 𝟙 P') ≫ (T.monoidal.leftUnitor P').hom = b')
    (hc : F.map b ≫ aP.hom = c.hom ≫ b') :
    μ.hom.app (S.monoidal.tensorUnit, P) ≫
      T.tensor.map (X := (F.obj S.monoidal.tensorUnit, F.obj P))
        (Y := (T.monoidal.tensorUnit, F.obj P))
        ((F.mapIso uB ≪≫ aO ≪≫ uA.symm).hom, 𝟙 _) ≫
      (T.monoidal.leftUnitor (F.obj P)).hom =
        F.map (S.monoidal.leftUnitor P).hom := by
  let := S.monoidal
  let := T.monoidal
  have hi : IsIso (S.tensor.map (X := (O, P)) (Y := (S.monoidal.tensorUnit, P))
      (uB.inv, 𝟙 P)) := by
    have : IsIso (Prod.mkHom uB.inv (𝟙 P)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    exact Functor.map_isIso _ _
  -- Test the unit square after the tensor-model and unit isomorphisms.
  apply (cancel_epi (F.map (i.hom ≫ S.tensor.map
    (X := (O, P)) (Y := (S.monoidal.tensorUnit, P)) (uB.inv, 𝟙 P)))).mp
  apply (cancel_mono aP.hom).mp
  have hn : F.map (S.tensor.map (X := (O, P))
        (Y := (S.monoidal.tensorUnit, P)) (uB.inv, 𝟙 P)) ≫
      μ.hom.app (S.monoidal.tensorUnit, P) =
    μ.hom.app (O, P) ≫ T.tensor.map (X := (F.obj O, F.obj P))
      (Y := (F.obj S.monoidal.tensorUnit, F.obj P)) (F.map uB.inv, 𝟙 (F.obj P)) := by
    simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id] using
      μ.hom.naturality (X := (O, P)) (Y := (S.monoidal.tensorUnit, P)) (uB.inv, 𝟙 P)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    CoefficientClosedStructure.tensor, tensor_map]
  rw [← MonoidalCategory.leftUnitor_naturality]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id_map_assoc, Category.comp_id, Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫ (uA.inv ⊗ₘ 𝟙 P') ≫ (λ_ P').hom) hm
  simp only [CoefficientClosedStructure.tensor, tensor_map, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.comp_id] at hh
  erw [hh, hb', ← hc]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simpa only [CoefficientClosedStructure.tensor, tensor_map, Category.assoc] using
    (congrArg (fun f ↦ F.map f ≫ aP.hom) hb).symm

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private theorem left_summand
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (b : (coefficientTotalTensor.{r, c, v} J R).obj
      (ringedTensorUnitComplex.{c, v, r} J R, P) ⟶ P)
    (hb : ∀ (n : ℤ) (h : 0 + n = n) (V : Cᵒᵖ) (a : R.obj.obj V)
      (x : (P.X n).val.obj V),
      (b.f n).val.app V (coefficientTensorGenerator.{r, c, v} J R
        (ringedTensorUnitComplex.{c, v, r} J R) P 0 n n h V
        (ringedTensorUnitSection.{c, v, r} J R V a) x) = a • x)
    (n : ℤ) :
    tensorSummand.{c, v, r} J R (ringedTensorUnitComplex.{c, v, r} J R) P
        0 n n (zero_add n) ≫ b.f n =
      (@MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)).map
        (X := ((ringedTensorUnitComplex.{c, v, r} J R).X 0, P.X n))
        (Y := ((SheafOfModules.monoidalCategory R).tensorUnit, P.X n))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))).hom, 𝟙 _) ≫
      ((SheafOfModules.monoidalCategory R).leftUnitor (P.X n)).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
  apply pure_ext.{c, v, r} J R _ (P.X n) _
  intro V a x
  have ha : e.inv.val.app V (e.hom.val.app V a) = a :=
    congrArg (fun f ↦ f.val.app V a) e.hom_inv_id
  have hh := hb n (zero_add n) V (e.hom.val.app V a) x
  change (b.f n).val.app V
    ((tensorSummand.{c, v, r} J R (ringedTensorUnitComplex.{c, v, r} J R) P
      0 n n (zero_add n)).val.app V
        (sheafTensorGenerator.{c, v, r} J R
          ((ringedTensorUnitComplex.{c, v, r} J R).X 0) (P.X n) V
            (e.inv.val.app V (e.hom.val.app V a)) x)) = _ at hh
  rw [ha] at hh
  refine hh.trans ?_
  symm
  change ((λ_ (P.X n)).hom).val.app V
    ((e.hom ⊗ₘ (𝟙 (P.X n))).val.app V
      (CochainPullback.moduleTmul.{max c v r, c, v} _ _ V a x)) = _
  rw [CochainPullback.moduleTmul_map.{max c v r, c, v}]
  exact RingedDerivedNative.pureTensor_leftUnitor.{c, v, r} J R
    (P.X n) V (e.hom.val.app V a) x

attribute [local irreducible] coefficientTotalTensor tensorSummand

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
private theorem left_unit_chain
    (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (bB : (coefficientTotalTensor.{r, c, v} J R).obj
      (ringedTensorUnitComplex.{c, v, r} J R, P) ≅ P)
    (bA : (coefficientTotalTensor.{s, d, vd} J' R').obj
      (ringedTensorUnitComplex.{d, vd, s} J' R',
        (U.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (U.mapHomologicalComplex (.up ℤ)).obj P)
    (hbB : ∀ (n : ℤ) (h : 0 + n = n) (V : Cᵒᵖ) (a : R.obj.obj V)
      (x : (P.X n).val.obj V),
      (bB.hom.f n).val.app V (coefficientTensorGenerator.{r, c, v} J R
        (ringedTensorUnitComplex.{c, v, r} J R) P 0 n n h V
        (ringedTensorUnitSection.{c, v, r} J R V a) x) = a • x)
    (hbA : ∀ (n : ℤ) (h : 0 + n = n) (V : Dᵒᵖ) (a : R'.obj.obj V)
      (x : (((U.mapHomologicalComplex (.up ℤ)).obj P).X n).val.obj V),
      (bA.hom.f n).val.app V (coefficientTensorGenerator.{s, d, vd} J' R'
        (ringedTensorUnitComplex.{d, vd, s} J' R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) 0 n n h V
        (ringedTensorUnitSection.{d, vd, s} J' R' V a) x) = a • x) :
    (U.mapHomologicalComplex (.up ℤ)).map bB.hom =
      chain.hom.app (ringedTensorUnitComplex.{c, v, r} J R, P) ≫
      (coefficientTotalTensor.{s, d, vd} J' R').map
        (X := ((U.mapHomologicalComplex (.up ℤ)).obj (ringedTensorUnitComplex.{c, v, r} J R),
          (U.mapHomologicalComplex (.up ℤ)).obj P))
        (Y := (ringedTensorUnitComplex.{d, vd, s} J' R',
          (U.mapHomologicalComplex (.up ℤ)).obj P))
        (((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
          (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit).hom, 𝟙 _) ≫
        bA.hom := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{c, v, r} J R
  let O' := ringedTensorUnitComplex.{d, vd, s} J' R'
  let e : F.obj O ≅ O' :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
    (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit
  change F.map bB.hom = chain.hom.app (O, P) ≫
    (coefficientTotalTensor.{s, d, vd} J' R').map
      (X := (F.obj O, F.obj P)) (Y := (O', F.obj P)) (e.hom, 𝟙 _) ≫ bA.hom
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  -- Test target summands after the inverse comparison; U need not preserve their coproduct.
  apply (cancel_epi (chain.inv.app (O, P))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply total_hom_ext.{d, vd, s} J' R' (F.obj O) (F.obj P) (F.obj P)
  intro n p q hpq
  have hi : tensorSummand.{d, vd, s} J' R' (F.obj O) (F.obj P) p q n hpq ≫
      (chain.inv.app (O, P)).f n =
    u.tensor.inv.app (O.X p, P.X q) ≫
      U.map (tensorSummand.{c, v, r} J R O P p q n hpq) := by
    apply (cancel_mono ((chain.hom.app (O, P)).f n)).mp
    have hh : (chain.inv.app (O, P)).f n ≫ (chain.hom.app (O, P)).f n = 𝟙 _ :=
      congrArg (fun f ↦ f.f n) (chain.app (O, P)).inv_hom_id
    simp only [Category.assoc, hh, summand, Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  simp only [HomologicalComplex.comp_f]
  change tensorSummand.{d, vd, s} J' R' (F.obj O) (F.obj P) p q n hpq ≫
    (chain.inv.app (O, P)).f n ≫ U.map (bB.hom.f n) =
    tensorSummand.{d, vd, s} J' R' (F.obj O) (F.obj P) p q n hpq ≫
      (((coefficientTotalTensor.{s, d, vd} J' R').map
        (X := (F.obj O, F.obj P)) (Y := (O', F.obj P)) (e.hom, 𝟙 _)).f n) ≫
          bA.hom.f n
  by_cases hp : p = 0
  · subst p
    have hn : q = n := by omega
    subst q
    rw [reassoc_of% hi, ← U.map_comp,
      left_summand.{c, v, r} J R P bB.hom hbB n,
      reassoc_of% (summand_map.{d, vd, s} J' R' e.hom (𝟙 (F.obj P))
        0 n n hpq),
      left_summand.{d, vd, s} J' R' (F.obj P) bA.hom hbA n]
    let sB := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    let sA := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose J'
        (forget₂ CommRingCat.{max d vd s} RingCat.{max d vd s})).obj R'))
    -- The normalized chain unit has the prescribed underived degree-zero component.
    have he : e.hom.f 0 ≫ sA.hom = U.map sB.hom ≫ u.coherence.unit.hom := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
        Iso.app_hom, F, O, O', ringedTensorUnitComplex, sA, sB]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
    let tB := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)
    let tA := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R')
    let X := U.obj (P.X n)
    let I := (SheafOfModules.monoidalCategory R).tensorUnit
    let I' := (SheafOfModules.monoidalCategory R').tensorUnit
    change u.tensor.inv.app (O.X 0, P.X n) ≫
        U.map (tB.map (X := (O.X 0, P.X n)) (Y := (I, P.X n))
          (sB.hom, 𝟙 _) ≫ (λ_ (P.X n)).hom) =
      tA.map (X := (U.obj (O.X 0), X)) (Y := (O'.X 0, X)) (e.hom.f 0, 𝟙 _) ≫
        tA.map (X := (O'.X 0, X)) (Y := (I', X)) (sA.hom, 𝟙 _) ≫ (λ_ X).hom
    have hn : U.map (tB.map (X := (O.X 0, P.X n)) (Y := (I, P.X n))
        (sB.hom, 𝟙 _)) ≫ u.tensor.hom.app (I, P.X n) =
      u.tensor.hom.app (O.X 0, P.X n) ≫
        tA.map (X := (U.obj (O.X 0), X)) (Y := (U.obj I, X))
          (U.map sB.hom, 𝟙 _) := by
      simpa only [tA, tB, X, Functor.comp_map, Functor.prod_map, Functor.map_id] using
        u.tensor.hom.naturality (X := (O.X 0, P.X n)) (Y := (I, P.X n))
          (Prod.mkHom sB.hom (𝟙 (P.X n)))
    have hp : (Prod.mkHom (e.hom.f 0) (𝟙 X)) ≫ (Prod.mkHom sA.hom (𝟙 X)) =
        (Prod.mkHom (U.map sB.hom) (𝟙 X)) ≫ (Prod.mkHom u.coherence.unit.hom (𝟙 X)) := by
      apply Prod.ext
      · exact he
      · rfl
    have ht : tA.map (X := (U.obj (O.X 0), X)) (Y := (O'.X 0, X))
        (e.hom.f 0, 𝟙 _) ≫ tA.map (X := (O'.X 0, X)) (Y := (I', X)) (sA.hom, 𝟙 _) =
      tA.map (X := (U.obj (O.X 0), X)) (Y := (U.obj I, X)) (U.map sB.hom, 𝟙 _) ≫
        tA.map (X := (U.obj I, X)) (Y := (I', X)) (u.coherence.unit.hom, 𝟙 _) := by
      simpa only [Functor.map_comp] using
        congrArg (fun f : (U.obj (O.X 0), X) ⟶ (I', X) ↦ tA.map f) hp
    apply (cancel_epi (u.tensor.hom.app (O.X 0, P.X n))).mp
    rw [Iso.hom_inv_id_app_assoc, Functor.map_comp, ← u.coherence.left_unit (P.X n)]
    rw [reassoc_of% hn]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ u.tensor.hom.app (O.X 0, P.X n) ≫ f ≫ (λ_ X).hom) ht.symm
  · apply IsZero.eq_of_src
    apply (tensorRight ((F.obj P).X q)).map_isZero
    exact U.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

include u SB TB βB cB SA TA βA cA
set_option linter.unusedSectionVars false in
/--
The representative unit calculation for the left unitor is reduced to the
componentwise model equation for the normalized tensor comparison.
(blueprint: lem-sf-ringed-forget-tensor-left-representatives)
Proof in words: apply the representative model equation to the unit complex and
`P`. Naturality of the tensor-model comparisons, together with the exact-functor
localization factor, reduces the assertion to the unit square on total complexes.
In degree `n`, restrict to the only nonzero unit summand: `(0,n)` on the left
and `(n,0)` on the right. Use the summand formula and the single-complex comparison
in the displayed composite to obtain `u.coherence.left_unit`.
The corresponding unitor model equations of `cB` and `cA` transport this equality
back to the derived category. Local pure tensors and sheafification detect the
component maps, so no hypothesis of generation by global sections is needed.
Source: Stacks Project, sites-cohomology.tex, Tags 0FPT and 06YU.
-/
theorem ringed_forget_tensor_left_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) :
    (μ.hom.app (SB.monoidal.tensorUnit, DerivedCategory.Q.obj P) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj SB.monoidal.tensorUnit,
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          (Y := (SA.monoidal.tensorUnit, U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          ((U.mapDerivedCategory.mapIso cB.unitIso ≪≫
              U.mapDerivedCategoryFactors.app (ringedTensorUnitComplex.{c, v, r} J R) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
                  (SheafOfModules.unit ((sheafCompose J
                    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit) ≪≫
              cA.unitIso.symm).hom, 𝟙 _) ≫
        (SA.monoidal.leftUnitor (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).hom =
      U.mapDerivedCategory.map (SB.monoidal.leftUnitor (DerivedCategory.Q.obj P)).hom) := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{c, v, r} J R
  let O' := ringedTensorUnitComplex.{d, vd, s} J' R'
  let e : F.obj O ≅ O' :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
    (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit
  have hO := unit_kflat.{c, v, r} J R
  have fO := unit_flat.{c, v, r} J R
  have hO' := unit_kflat.{d, vd, s} J' R'
  have hUP := (hU P hP fP).1
  have hUO := (hU O hO fO).1
  obtain ⟨bB, hbB, heB⟩ := cB.leftUnitor_model P hP
  obtain ⟨bA, hbA, heA⟩ := cA.leftUnitor_model (F.obj P) hUP
  rw [cB.tensorIso_both O P hO hP] at heB
  rw [cA.tensorIso_both O' (F.obj P) hO' hUP] at heA
  have hc := left_unit_chain.{c, v, r, d, vd, s}
    J R J' R' U u chain summand P bB bA hbB hbA
  let α := U.mapDerivedCategoryFactors
  let t := (coefficientTotalTensor.{s, d, vd} J' R').mapIso
    (e.prod (Iso.refl (F.obj P)))
  let c := α.app ((coefficientTotalTensor.{r, c, v} J R).obj (O, P)) ≪≫
    DerivedCategory.Q.mapIso (chain.app (O, P)) ≪≫ DerivedCategory.Q.mapIso t
  have hm : U.mapDerivedCategory.map (TB.iso J R SB O P hO hP).hom ≫
      μ.hom.app (DerivedCategory.Q.obj O, DerivedCategory.Q.obj P) ≫
      SA.tensor.map
        (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj O),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
        (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
        ((α.app O ≪≫ DerivedCategory.Q.mapIso e).hom, (α.app P).hom) =
    c.hom ≫ (TA.iso J' R' SA O' (F.obj P) hO' hUP).hom := by
    have hm := hμ O P hO hP hUO hUP fO fP
    have hn := cA.tensorIso_naturality (F.obj O) (F.obj P) O' (F.obj P)
      (Or.inr hUP) (Or.inr hUP) e.hom (𝟙 _)
    rw [cA.tensorIso_both _ _ hUO hUP, cA.tensorIso_both _ _ hO' hUP] at hn
    let := SA.monoidal
    simp only [Functor.map_id] at hn
    calc
      _ = U.mapDerivedCategory.map (TB.iso J R SB O P hO hP).hom ≫
          μ.hom.app (DerivedCategory.Q.obj O, DerivedCategory.Q.obj P) ≫
          SA.tensor.map (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj O),
              U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
            (Y := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
            ((α.app O).hom, (α.app P).hom) ≫
          SA.tensor.map (X := (DerivedCategory.Q.obj (F.obj O),
              DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map e.hom, 𝟙 _) := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, CoefficientClosedStructure.tensor,
          tensor_map, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (α.app _).hom ≫ DerivedCategory.Q.map (chain.hom.app (O, P)) ≫
          (TA.iso J' R' SA (F.obj O) (F.obj P) hUO hUP).hom ≫
          SA.tensor.map (X := (DerivedCategory.Q.obj (F.obj O),
              DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map e.hom, 𝟙 _) := by
        simpa only [Category.assoc, α, F, Iso.app_hom] using
          congrArg (fun f ↦ f ≫ SA.tensor.map
          (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
          (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
          (DerivedCategory.Q.map e.hom, 𝟙 _)) hm
      _ = _ := by
        erw [← hn]
        simp only [c, Iso.trans_hom, Functor.mapIso_hom, t, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Prod.mkHom, Category.assoc, F, O']
  have hf : U.mapDerivedCategory.map (DerivedCategory.Q.map bB.hom) ≫
      (α.app P).hom = c.hom ≫ DerivedCategory.Q.map bA.hom := by
    have hn := α.hom.naturality bB.hom
    change U.mapDerivedCategory.map (DerivedCategory.Q.map bB.hom) ≫ (α.app P).hom =
      (α.app _).hom ≫ DerivedCategory.Q.map (F.map bB.hom) at hn
    rw [hn, hc]
    simp only [Functor.map_comp, c, Iso.trans_hom, Functor.mapIso_hom,
      t, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Prod.mkHom, Category.assoc, O, e, F]
  have hh := left_unit_of_models SB SA U.mapDerivedCategory μ
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (O, P)))
    (DerivedCategory.Q.obj (F.obj P)) (DerivedCategory.Q.obj O')
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{s, d, vd} J' R').obj (O', F.obj P)))
    (TB.iso J R SB O P hO hP) (TA.iso J' R' SA O' (F.obj P) hO' hUP)
    (α.app P) (α.app O ≪≫ DerivedCategory.Q.mapIso e) c cB.unitIso cA.unitIso
    (DerivedCategory.Q.map bB.hom) (DerivedCategory.Q.map bA.hom) hm heB heA hf
  simpa only [e, Functor.mapIso_trans, Iso.trans_assoc] using hh

end CategoryTheory.RingedForgetTensorTransposition
