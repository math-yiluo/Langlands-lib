/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Restricting the finite-type kernel condition

Source: Stacks Project, Modules, Definition 01BV and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

section SiteHelpers

-- The generator-transport argument also appears in QuasicoherentFiniteTypeAffine.
-- Keep it private here to avoid importing unrelated affine and quasi-coherent theory.
open SheafOfModules in
private theorem finiteType_of_data
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

open SheafOfModules in
private theorem finiteType_of_iso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := ⟨fun i ↦ by
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType⟩
  exact finiteType_of_data q'

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules in
private theorem finiteType_pushforward
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type*} [Category* D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  let Q : ((pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
          pushforward (𝟙 _)
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        let e : (pushforward.{u} (F := G') ψ).obj (unit (R.over (P.X i.2.1))) ≅
            unit (S.over i.1) := overS.mapIso η
        letI : PreservesColimitsOfSize.{u, u} (pushforward.{u} (F := G') ψ) := h _ _ _
        exact (P.generators i.2.1).map (pushforward.{u} (F := G') ψ) e.symm }
  have : Q.IsFiniteType := ⟨fun i ↦ by
    have := hP.isFiniteType i.2.1
    dsimp [Q]
    infer_instance⟩
  exact finiteType_of_data Q

open SheafOfModules in
private theorem finiteType_pushforward_leftAdjoint
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type*} [Category* D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  apply +allowSynthFailures finiteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end SiteHelpers

namespace AlgebraicGeometry

private theorem finiteType_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) [M.IsFiniteType] : (M.restrict f).IsFiniteType := by
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app U := (f.appIso U.unop).inv }
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : Y.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj
      X.ringCatSheaf := ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact finiteType_pushforward_leftAdjoint f.opensFunctor φ (Scheme.Modules.restrictUnitIso _)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_equivOver {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsFiniteType] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsFiniteType := by
  let := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : TopologicalSpace.Opens ↥U) : (Over.post U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over V)
      (((Opens.grothendieckTopology X).over U).over
        (U.overEquivalence.symm.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.symm.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv).obj M).IsFiniteType
  exact finiteType_pushforward_leftAdjoint U.overEquivalence.symm.functor _ (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_equivOverInverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFiniteType] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsFiniteType := by
  have (V : Over U) : (Over.post U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv).obj M).IsFiniteType
  exact finiteType_pushforward_leftAdjoint U.overEquivalence.functor _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

private noncomputable def restrictionEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor s.hom)
    (Scheme.Modules.restrictFunctor s.inv)
    ((Scheme.Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel condition alone, without assuming the module is of finite type,
passes to restriction to an open subscheme.
Source: Stacks Project, Modules, Definition 01BV (definition-coherent), Definition 01B5
(definition-finite-type), and Section 01AF (section-kernels).
(blueprint: lem-weil-pbc-coherent-kernel-condition-restriction).

Proof: For an open `V` of `W`, its image is an open `V'` of `X` contained in `W`.
The open-site module equivalences, composed with restriction along the canonical
isomorphism `V.toScheme ≅ V'.toScheme`, identify the restriction of `F|_W` to `V`
with `F.over V'`. This equivalence preserves the structure module,
finite coproducts, and kernels. Transfer the given map from a free module of rank `n`
to a map over `V'`; its kernel is finite type by the hypothesis. Transfer the kernel
back. Finite type is preserved by these site equivalences: each finite family of
local generators and its epimorphism transfers to the same finite family on the
corresponding open neighbourhood, and the corresponding neighbourhoods cover.
This applies also to the empty open and rank zero. -/
theorem coherent_kernel_condition_restriction (X : Scheme.{u}) (F : X.Modules)
    (hK : ∀ (U : X.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶
        F.over U), (kernel f).IsFiniteType)
    (W : X.Opens) (V : W.toScheme.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := W.toScheme.ringCatSheaf.over V)
      (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor W.ι).obj F).over V) :
    (kernel f).IsFiniteType := by
  let U : X.Opens := W.ι ''ᵁ V
  let s : V.toScheme ≅ U.toScheme := W.ι.isoImage V
  let E := ((Scheme.Modules.overEquiv U).trans (restrictionEquivalence s)).trans
    (Scheme.Modules.overEquiv V).symm
  let T := E.functor
  have : T.IsEquivalence := E.isEquivalence_functor
  let eF : T.obj (F.over U) ≅ ((Scheme.Modules.restrictFunctor W.ι).obj F).over V :=
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.restrictFunctor s.hom).mapIso ((Scheme.Modules.overFunctorEquiv U).app F) ≪≫
        ((Scheme.Modules.restrictFunctorComp s.hom U.ι).app F).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (W.ι.isoImage_hom_ι V)).app F ≪≫
        (Scheme.Modules.restrictFunctorComp V.ι W.ι).app F ≪≫
        ((Scheme.Modules.overFunctorEquiv V).app
          ((Scheme.Modules.restrictFunctor W.ι).obj F)).symm) ≪≫
      ((Scheme.Modules.overEquiv V).unitIso.app
        (((Scheme.Modules.restrictFunctor W.ι).obj F).over V)).symm
  let eunit : SheafOfModules.unit (W.toScheme.ringCatSheaf.over V) ≅
      T.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (V.sheafOfModulesEquivOverInverseUnit W.toScheme.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv V).inverse.mapIso
        ((Scheme.Modules.restrictUnitIso s.hom).symm ≪≫
          (Scheme.Modules.restrictFunctor s.hom).mapIso
            (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)
  let efree := SheafOfModules.mapFreeIso T (ULift.{u} (Fin n)) eunit
  let g := T.preimage (efree.inv ≫ f ≫ eF.inv)
  have : (kernel g).IsFiniteType := hK U n g
  have := finiteType_equivOver U (kernel g)
  have := finiteType_restrict s.hom ((Scheme.Modules.overEquiv U).functor.obj (kernel g))
  have : (T.obj (kernel g)).IsFiniteType :=
    finiteType_equivOverInverse V
      ((Scheme.Modules.restrictFunctor s.hom).obj
        ((Scheme.Modules.overEquiv U).functor.obj (kernel g)))
  let ek : T.obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso T g ≪≫
      kernel.mapIso (T.map g) f efree.symm eF (by simp [g])
  exact finiteType_of_iso (R := W.toScheme.ringCatSheaf.over V) ek

end AlgebraicGeometry
