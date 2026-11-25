/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalEvaluationSingleton
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalFiniteProperMate

/-! # Bounded-origin properties of a proper/open strict-system comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
open scoped ZeroObject
namespace AlgebraicGeometry
private instance (priority := 20000) cachedEtaleSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.Etale := Scheme.Etale.essentiallySmall T
private instance (priority := 20000) cachedProSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] exceptionalTransportProEtaleCommRingSheafify
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  exceptionalTransportProEtaleTypeSheafify exceptionalTransportProEtaleRingCompose
  exceptionalTransportProEtaleRingSetCompose exceptionalTransportProEtaleAddCommGrpSetCompose
  strictEtaleRingCompose strictEtaleRingSetCompose strictEtaleAddCommGrpSetCompose
  strictEtaleAddCommGrpSheafify strictEtaleCommRingSheafify strictEtaleTypeSheafify
  strictEtaleAddCommGrpLocal
attribute [local implicit_reducible] ExceptionalProCompactSupport StrictEtaleExceptionalAdjoint
  ExceptionalSystemCompactificationComparison exceptionalProSupport StrictEtaleCompactSupport
attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q
  CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

private instance etaleProperSystemInverseAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c : Compactification f} (S : StrictEtaleCompactSupport O ell c) :
    S.val.properImage.inverse.Additive := S.val.properImage.systemInverseAdditive
private instance etaleProperSystemRightAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c : Compactification f} (S : StrictEtaleCompactSupport O ell c) :
    S.val.properImage.rightSystem.Additive := S.val.properImage.systemRightAdditive
attribute [local instance 20000] strictEtaleProperInverseAdditive strictEtaleProperDirectAdditive

section Abstract
universe a av b bv da db
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]

private def exact_iso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : FD ≅ F.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ FD F.mapDerivedCategory
    (fac ≪≫ F.mapDerivedCategoryFactors.symm)

private theorem exact_bound (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M : DerivedCategory A) (a : ℤ) (hM : M.IsGE a) : (FD.obj M).IsGE a := by
  have := F.isGE_mapDerivedCategory_obj M a
  exact DerivedCategory.TStructure.t.isGE_of_iso (exact_iso F FD fac |>.app M).symm a

end Abstract

section Mate
universe a av b bv c cv d dv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {L : A ⥤ B} {V : B ⥤ A} {L' : C ⥤ D} {V' : D ⥤ C}
  {E : A ⥤ C} {H : B ⥤ D}

private theorem direct_mate (a : L ⊣ V) (b : L' ⊣ V')
    (p : L ⋙ H ≅ E ⋙ L') (q : V ⋙ E ≅ H ⋙ V')
    (hc : ∀ M, p.hom.app (V.obj M) ≫ L'.map (q.hom.app M) ≫
      b.counit.app (H.obj M) = H.map (a.counit.app M)) :
    (mateEquiv a b (.mk _ _ _ _ p.inv)) = q.hom := by
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi (p.hom.app (V.obj M))).mp
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using (hc M).symm

private theorem iso_rectangle {T : Type*} [Category T] {A B C D E F : T}
    (i : A ≅ B) (j : B ≅ C) (k : D ≅ E) (l : E ≅ F)
    (q : A ⟶ D) (r : C ⟶ F)
    (h : q ≫ k.hom ≫ l.hom = i.hom ≫ j.hom ≫ r) :
    j.inv ≫ i.inv ≫ q = r ≫ l.inv ≫ k.inv := by
  apply (cancel_epi j.hom).mp
  apply (cancel_epi i.hom).mp
  apply (cancel_mono k.hom).mp
  apply (cancel_mono l.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.id_comp, Category.comp_id] using h

private theorem support_paste {T : Type*} [Category T]
    {A B C D E F G H I J K L : T}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E} {e : E ⟶ F}
    {c' : B ⟶ G} {b' : G ⟶ D} {z : G ⟶ H} {u : H ⟶ I} {v : I ⟶ F}
    {k : A ⟶ J} {l : J ⟶ K} {m : K ⟶ H} {l' : K ⟶ L} {m' : L ⟶ I}
    (hn : b ≫ c = c' ≫ b') (ho : b' ≫ d ≫ e = z ≫ u ≫ v)
    (hp : a ≫ c' ≫ z = k ≫ l ≫ m) (hl : l' ≫ m' = m ≫ u) :
    a ≫ b ≫ c ≫ d ≫ e = k ≫ l ≫ l' ≫ m' ≫ v := by
  rw [reassoc_of% hn, ho, reassoc_of% hp, ← reassoc_of% hl]

end Mate

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

private theorem etale_evaluation_bound {T : Scheme.{u}}
    (PE : StrictEtaleEvaluation T O ell) (n : ℕ) M (a : ℤ) (hM : M.IsGE a) :
    ((PE.evaluation n).obj M).IsGE a := by
  have := (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).1
  have := (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).2
  exact exact_bound (coefficientEvaluation (J := T.smallEtaleTopology)
    (O := O) (ell := ell) n) _ (PE.evaluationFactors n) M a hM

private theorem pro_evaluation_bound {T : Scheme.{u}}
    (PE : ExceptionalProEvaluation T O ell) (n : ℕ) M (a : ℤ) (hM : M.IsGE a) :
    ((PE.evaluation n).obj M).IsGE a := by
  have := (coefficientEvaluation_exact (J := Scheme.ProEt.topology T)
    (O := O) (ell := ell) n).1
  have := (coefficientEvaluation_exact (J := Scheme.ProEt.topology T)
    (O := O) (ell := ell) n).2
  exact exact_bound (coefficientEvaluation (J := Scheme.ProEt.topology T)
    (O := O) (ell := ell) n) _ (PE.evaluationFactors n) M a hM

private instance siteLevelInverseAdditive {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) : (C.ordinary.lift n).modules.Additive := C.ordinary.inverseAdditive n
private instance siteLevelRightAdditive {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) : (C.ordinary.right n).Additive := C.ordinary.rightAdditive n

private theorem site_level_inverse_bound {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) M (a : ℤ) (hM : M.IsGE a) : ((C.image.level n).inverse.obj M).IsGE a := by
  have := (C.ordinary.inverseExact n).1
  have := (C.ordinary.inverseExact n).2
  exact exact_bound (C.ordinary.lift n).modules _ (C.image.level n).inverseFactors M a hM

private theorem site_level_direct_bound {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) M (a : ℤ) (hM : M.IsGE a) : ((C.image.level n).direct.obj M).IsGE a := by
  have := (C.ordinary.inverseExact n).1
  have := (C.ordinary.inverseExact n).2
  exact exactDerivedAdjunction_isGE (C.ordinary.lift n).modules _
    (C.image.level n).inverseFactors (C.image.level n).adjunction M a

private theorem site_level_counit {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (hC : ExceptionalSystemSiteEquivalence C) (n : ℕ) M (hM : C.levelOrigin n M) :
    IsIso ((C.image.level n).adjunction.counit.app M) := by
  obtain ⟨N, ⟨a, ha⟩, ⟨i⟩⟩ := hM.2
  obtain ⟨K, hK, ⟨e⟩, _⟩ := exceptionalEvaluationSingleton O ell T PE n N a ha
  let L := C.image.system.inverse.obj K
  have hOrigin : C.origin L := hC.inverseOrigin K ⟨a, hK⟩
  let e' := (C.image.inverseEvaluation n).app K ≪≫
    (C.image.level n).inverse.mapIso e ≪≫ i
  have := hC.counit L hOrigin
  have hi : IsIso ((C.image.level n).adjunction.counit.app
      ((C.proEvaluation.evaluation n).obj L)) := by
    have he := C.image.counit n L
    have : IsIso ((C.image.inverseEvaluation n).hom.app (C.image.system.direct.obj L) ≫
        (C.image.level n).inverse.map ((C.image.directEvaluation n).hom.app L) ≫
        (C.image.level n).adjunction.counit.app ((C.proEvaluation.evaluation n).obj L)) := by
      rw [he]
      infer_instance
    rw [← Category.assoc] at this
    exact IsIso.of_isIso_comp_left
      ((C.image.inverseEvaluation n).hom.app (C.image.system.direct.obj L) ≫
        (C.image.level n).inverse.map ((C.image.directEvaluation n).hom.app L)) _
  have : IsIso ((C.image.level n).adjunction.counit.app
      ((C.image.construction.evaluation.system.inverse ⋙
        C.proEvaluation.evaluation n).obj K)) := hi
  have hn := (C.image.level n).adjunction.counit.naturality e'.hom
  have : IsIso (((C.image.level n).direct ⋙ (C.image.level n).inverse).map e'.hom ≫
      (C.image.level n).adjunction.counit.app M) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (((C.image.level n).direct ⋙ (C.image.level n).inverse).map e'.hom) _

private theorem etale_open_bound M (a : ℤ) (hM : M.IsGE a) :
    (S.derivedOpen.obj M).IsGE a := by
  have := S.property.1.1
  have := S.property.1.2
  exact exact_bound S.val.openExtension _ S.val.openFactors M a hM

private theorem etale_level_open_bound (n : ℕ) M (a : ℤ) (hM : M.IsGE a) :
    ((S.levelDerivedOpen n).obj M).IsGE a := by
  obtain ⟨K, hK, ⟨e⟩, _⟩ := exceptionalEvaluationSingleton O ell X S.PX n M a hM
  have hb : ((S.derivedOpen ⋙ S.PZ.evaluation n).obj K).IsGE a :=
    etale_evaluation_bound S.PZ n _ a (etale_open_bound (S := S) K a hK)
  let i := (S.openDerivedEvaluation n).app K ≪≫ (S.levelDerivedOpen n).mapIso e
  exact DerivedCategory.TStructure.t.isGE_of_iso i a

private theorem etale_level_support_bound (n : ℕ) M (a : ℤ) (hM : M.IsGE a) :
    ((S.levelFunctor n).obj M).IsGE a := by
  have := (S.properImage.inverseExact n).1
  have := (S.properImage.inverseExact n).2
  have := etale_level_open_bound (S := S) n M a hM
  exact exactDerivedAdjunction_isGE (S.properImage.lift n).modules _
    (S.properDerived.level n).inverseFactors (S.properDerived.level n).adjunction _ a

-- The cube has eight derived categories; allow elaboration of its concrete instances.
private theorem proper_evaluation
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) (n : ℕ) M :
    (CY.proEvaluation.evaluation n).map
      ((mateEquiv S.properDerived.system.adjunction P.val.properDerived.system.adjunction
        (.mk _ _ _ _ R.properSquare.square.hom)).app M) ≫
      (P.val.properDerived.directEvaluation n).hom.app (CZ.image.system.inverse.obj M) ≫
      (P.val.properDerived.level n).direct.map ((CZ.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.properDerived.system.direct.obj M) ≫
      (CY.image.level n).inverse.map ((S.properDerived.directEvaluation n).hom.app M) ≫
      (mateEquiv (S.properDerived.level n).adjunction
        (P.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).app
          ((S.PZ.evaluation n).obj M) := by
  have hc N := R.properSquare.property.2.2.2.1 n N
  have hf := direct_mate S.properDerived.system.adjunction
    (S.properDerived.level n).adjunction (S.properDerived.inverseEvaluation n)
    (S.properDerived.directEvaluation n) (S.properDerived.counit n)
  have hk := direct_mate P.val.properDerived.system.adjunction
    (P.val.properDerived.level n).adjunction (P.val.properDerived.inverseEvaluation n)
    (P.val.properDerived.directEvaluation n) (P.val.properDerived.counit n)
  have he := exchangeMate_cube S.properDerived.system.adjunction
    P.val.properDerived.system.adjunction (S.properDerived.level n).adjunction
    (P.val.properDerived.level n).adjunction
    (S.PY.evaluation n) (S.PZ.evaluation n)
    (CY.proEvaluation.evaluation n) (CZ.proEvaluation.evaluation n)
    (S.properDerived.inverseEvaluation n) (CY.image.inverseEvaluation n)
    (CZ.image.inverseEvaluation n) (P.val.properDerived.inverseEvaluation n)
    R.properSquare.square.hom (R.properSquare.derivedLevel n).hom (fun N ↦ ?_) M
  · rw [show (mateEquiv S.properDerived.system.adjunction
        (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.inverseEvaluation n).inv)).app M =
        (S.properDerived.directEvaluation n).hom.app M from congr_app hf M,
      show (mateEquiv P.val.properDerived.system.adjunction
        (P.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (P.val.properDerived.inverseEvaluation n).inv)).app
          (CZ.image.system.inverse.obj M) =
        (P.val.properDerived.directEvaluation n).hom.app
          (CZ.image.system.inverse.obj M) from congr_app hk _] at he
    exact he
  · exact iso_rectangle
      ((P.val.properDerived.inverseEvaluation n).app (CY.image.system.inverse.obj N))
      ((P.val.properDerived.level n).inverse.mapIso ((CY.image.inverseEvaluation n).app N))
      ((CZ.image.inverseEvaluation n).app (S.properDerived.system.inverse.obj N))
      ((CZ.image.level n).inverse.mapIso ((S.properDerived.inverseEvaluation n).app N))
      _ _ (hc N)

private theorem comparison_evaluation
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) (n : ℕ) M :
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M) := by
  have hp := proper_evaluation CX CY CZ P R n (S.derivedOpen.obj M)
  have ho := congrArg (P.val.properDerived.level n).direct.map (R.property.2.2 n M)
  have hn := (P.val.properDerived.directEvaluation n).hom.naturality
    (R.openComparison.hom.app M)
  have hl := (mateEquiv (S.properDerived.level n).adjunction
    (P.val.properDerived.level n).adjunction
    (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).naturality
      ((S.openDerivedEvaluation n).hom.app M)
  dsimp only [Functor.comp_map] at hn hl
  simp only [Functor.map_comp] at ho
  change (CY.proEvaluation.evaluation n).map
      (𝟙 _ ≫ (mateEquiv S.properDerived.system.adjunction
        P.val.properDerived.system.adjunction
        (.mk _ _ _ _ R.properSquare.square.hom)).app (S.derivedOpen.obj M) ≫
        𝟙 _ ≫ P.val.properDerived.system.direct.map (R.openComparison.hom.app M) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ (P.val.properDerived.directEvaluation n).hom.app
        (P.val.derivedOpen.obj (CX.image.system.inverse.obj M)) ≫ 𝟙 _ ≫
        (P.val.properDerived.level n).direct.map
          ((P.val.openDerivedEvaluation n).hom.app (CX.image.system.inverse.obj M)) ≫ 𝟙 _) ≫
      (P.val.properDerived.level n).direct.map
        ((P.val.levelDerivedOpen n).map ((CX.image.inverseEvaluation n).hom.app M)) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map
        (𝟙 _ ≫ (S.properDerived.directEvaluation n).hom.app (S.derivedOpen.obj M) ≫ 𝟙 _ ≫
          (S.properDerived.level n).direct.map ((S.openDerivedEvaluation n).hom.app M) ≫
          𝟙 _) ≫
      (𝟙 _ ≫ (mateEquiv (S.properDerived.level n).adjunction
        (P.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).app
          ((S.levelDerivedOpen n).obj ((S.PX.evaluation n).obj M)) ≫ 𝟙 _ ≫
        (P.val.properDerived.level n).direct.map
          ((R.levelOpenComparison n).hom.app ((S.PX.evaluation n).obj M)) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  erw [(CY.image.level n).inverse.map_comp]
  simp only [Category.assoc]
  exact support_paste hn ho hp hl

-- Keep the original interface assumptions; the construction only needs hX.
set_option linter.unusedVariables false in
/-- The canonical proper/open comparison has the bounded-origin properties.
Source: Zheng Construction 5.15 and Lemmas 4.10, 5.16 and 5.22; Stacks 0B65.
(blueprint: lem-sf-exceptional-proper-open-origin-properties).

Proof: the finite proper mate is invertible on bounded-below inputs, and exact
evaluation transports this fact to strict systems.  The site equivalence clauses
transport origins through the open and proper factors.  For a finite origin, the
right etale adjoint is bounded below by the uniform cohomological bound.  Finally,
substituting the proper mate and the open evaluation square into the mate word,
and cancelling the unit and counit identities, gives the displayed equality of
actual derived morphisms. -/
theorem exceptionalProperOpenOriginProperties
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) :
      (∀ M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((exceptionalSystemComparison R).app M)) ∧
      (∀ M, CX.origin M → CY.origin ((exceptionalProSupport P).obj M)) ∧
      (∀ n M, CX.levelOrigin n M → CY.levelOrigin n
        ((P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).obj M)) ∧
      (∀ n M, CX.levelOrigin n M →
        IsIso ((exceptionalSystemLevelOriginComparison R n).app M)) ∧
      (∀ n N, CY.levelOrigin n N →
        ∃ a : ℤ, ((G.levelRight n).obj ((CY.image.level n).direct.obj N)).IsGE a) ∧
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)) := by
  have levelIso (n : ℕ) M (hM : ∃ a : ℤ, M.IsGE a) :
      IsIso ((exceptionalSystemLevelComparison R n).app M) := by
    obtain ⟨a, ha⟩ := hM
    have := exceptionalFiniteProperMate R n ((S.levelDerivedOpen n).obj M)
      ⟨a, etale_level_open_bound (S := S) n M a ha⟩
    change IsIso (𝟙 _ ≫
      (mateEquiv (S.properDerived.level n).adjunction
        (P.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).app
          ((S.levelDerivedOpen n).obj M) ≫
      𝟙 _ ≫ (P.val.properDerived.level n).direct.map
        ((R.levelOpenComparison n).hom.app M) ≫ 𝟙 _)
    infer_instance
  have finiteStable (n : ℕ) M (hM : CX.levelOrigin n M) :
      CY.levelOrigin n
        ((P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).obj M) := by
    obtain ⟨N, ⟨a, ha⟩, ⟨e⟩⟩ := hM.2
    have := levelIso n N ⟨a, ha⟩
    let i := asIso ((exceptionalSystemLevelComparison R n).app N) ≪≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).mapIso e
    have hb := etale_level_support_bound (S := S) n N a ha
    have : ((S.levelFunctor n ⋙ (CY.image.level n).inverse).obj N).IsGE a :=
      site_level_inverse_bound CY n ((S.levelFunctor n).obj N) a hb
    exact ⟨⟨a, DerivedCategory.TStructure.t.isGE_of_iso i a⟩,
      (S.levelFunctor n).obj N, ⟨a, hb⟩, ⟨i⟩⟩
  refine ⟨?_, ?_, finiteStable, ?_, ?_, comparison_evaluation CX CY CZ P R⟩
  · intro M hM
    apply (CY.image.detectsIso _).2
    intro n
    obtain ⟨a, ha⟩ := hM
    have := levelIso n ((S.PX.evaluation n).obj M)
      ⟨a, etale_evaluation_bound S.PX n M a ha⟩
    have hi : IsIso
        ((CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
          (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
          (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
            ((CX.image.inverseEvaluation n).hom.app M)) := by
      rw [comparison_evaluation CX CY CZ P R n M]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
        (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
          ((CX.image.inverseEvaluation n).hom.app M))
  · intro M hM
    obtain ⟨a, ha⟩ := hM.1
    have := P.property.1.1
    have := P.property.1.2
    have hopen := exact_bound P.val.openExtension _ P.val.openFactors M a ha
    refine ⟨P.val.properDerived.boundedBelow _ ⟨a, hopen⟩, ?_⟩
    intro n
    have ho : CX.levelOrigin n ((CX.proEvaluation.evaluation n).obj M) :=
      ⟨⟨a, pro_evaluation_bound CX.proEvaluation n M a ha⟩, hM.2 n⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := (finiteStable n _ ho).2
    exact ⟨N, hN, ⟨e ≪≫ ((exceptionalProSupportEvaluation P n).app M).symm⟩⟩
  · intro n M hM
    obtain ⟨a, ha⟩ := hM.1
    have := levelIso n ((CX.image.level n).direct.obj M)
      ⟨a, site_level_direct_bound CX n M a ha⟩
    have := site_level_counit CX hX n M hM
    change IsIso ((exceptionalSystemLevelComparison R n).app
      ((CX.image.level n).direct.obj M) ≫ 𝟙 _ ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.level n).adjunction.counit.app M) ≫ 𝟙 _)
    infer_instance
  · intro n N hN
    obtain ⟨a, ha⟩ := hN.1
    have hD := site_level_direct_bound CY n N a ha
    obtain ⟨K, hK, ⟨e⟩, _⟩ := exceptionalEvaluationSingleton O ell Y S.PY n
      ((CY.image.level n).direct.obj N) a hD
    obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
    have hG := hd a K hK
    have hb := etale_evaluation_bound S.PX n (G.right.obj K) (a - (d : ℤ)) hG
    have : ((G.right ⋙ S.PX.evaluation n).obj K).IsGE (a - (d : ℤ)) := hb
    let i := (G.evaluation n).app K ≪≫ (G.levelRight n).mapIso e
    exact ⟨a - d, DerivedCategory.TStructure.t.isGE_of_iso i (a - d)⟩

end AlgebraicGeometry
