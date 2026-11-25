/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! The ordinary canonical module comparison realizes the canonical derived comparison.

## References

* Stacks 03D8 and 0D6D
-/

@[expose] public section

set_option autoImplicit false
-- Replaying the sectionwise transport tactics for linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleCanonicalPullbackComposition
  proEtaleRingDirectImageMap

-- All data selected below are fixed by the existing normalization: the units fix the
-- adjunctions, the section formula fixes d, conjugation fixes a, and degree maps fix b.
-- The structure only exposes these determined witnesses from the existing theorem.
private structure ComparisonWitnesses
    {AK AH AC D A B : Type*}
    (NK : AK → Prop) (NH : AH → Prop) (NC : AC → Prop)
    (HD : D → Prop) (HA : AK → AH → AC → D → A → Prop)
    (HB : A → B → Prop) (HC : B → Prop) where
  adjk : AK
  adjh : AH
  adjc : AC
  nk : NK adjk
  nh : NH adjh
  nc : NC adjc
  d : D
  hd : HD d
  a : A
  ha : HA adjk adjh adjc d a
  b : B
  hb : HB a b
  hc : HC b

private theorem ComparisonWitnesses.nonempty
    {AK AH AC D A B : Type*}
    (NK : AK → Prop) (NH : AH → Prop) (NC : AC → Prop)
    (HD : D → Prop) (HA : AK → AH → AC → D → A → Prop)
    (HB : A → B → Prop) (HC : B → Prop)
    (h : ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC b) :
    Nonempty (ComparisonWitnesses NK NH NC HD HA HB HC) := by
  obtain ⟨ak, ah, ac, nk, nh, nc, d, hd, a, ha, b, hb, hc⟩ := h
  exact ⟨⟨ak, ah, ac, nk, nh, nc, d, hd, a, ha, b, hb, hc⟩⟩

private theorem ComparisonWitnesses.to_exists
    {AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : B → Prop}
    (p : ComparisonWitnesses NK NH NC HD HA HB HC) :
    ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC b :=
  ⟨p.adjk, p.adjh, p.adjc, p.nk, p.nh, p.nc, p.d, p.hd,
    p.a, p.ha, p.b, p.hb, p.hc⟩

private abbrev UniqueData
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (_t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b) (i : I) :=
  ComparisonWitnesses NK NH NC HD HA HB (HC i)

private theorem UniqueData.exists
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b) :
    Nonempty (UniqueData t (Classical.choose t.exists)) :=
  ComparisonWitnesses.nonempty _ _ _ _ _ _ _ (Classical.choose_spec t.exists)

private theorem UniqueData.unique_of_formula
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b)
    {i j : I} (di : UniqueData t i)
    (h : ∀ b, HB di.a b → HC i b → HC j b) : i = j := by
  apply t.unique di.to_exists
  exact ⟨di.adjk, di.adjh, di.adjc, di.nk, di.nh, di.nc, di.d, di.hd,
    di.a, di.ha, di.b, di.hb, h di.b di.hb di.hc⟩

private abbrev PullbackData
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c)
    (comparison : proEtaleRingDerivedPullback (h ≫ k) RV RZ c ≅
      proEtaleRingDerivedPullback k RV RW ck ⋙ proEtaleRingDerivedPullback h RW RZ ch) :=
  UniqueData (proEtaleCanonicalPullbackComposition_existsUnique
    h k RV RW RZ ck ch c hc.symm) comparison

private theorem pullbackData_exists
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    : Nonempty (PullbackData h k RV RW RZ ck ch
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
      rfl (proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch)) := by
  unfold proEtaleCanonicalPullbackComposition
  exact UniqueData.exists (proEtaleCanonicalPullbackComposition_existsUnique h k RV RW RZ
    ck ch (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl)

private theorem pullbackData_transport
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c) :
    Nonempty (PullbackData h k RV RW RZ ck ch c hc
      (eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) RV RZ) hc.symm) ≪≫
        proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch)) := by
  subst c
  simpa only [eqToIso_refl, Iso.refl_trans] using
    pullbackData_exists h k RV RW RZ ck ch

@[irreducible] private noncomputable def constantData
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    PullbackData h k (proEtaleConstantRing V A) (proEtaleConstantRing W A)
      (proEtaleConstantRing Z A) (proEtaleConstantRingComparison k A)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison (h ≫ k) A)
      (proEtaleConstantRingCompositeCoefficients_eq h k A)
      (proEtaleConstantRingPullbackComposition h k A).symm := by
  apply Classical.choice
  have he : (proEtaleConstantRingPullbackComposition h k A).symm =
      eqToIso (congrArg
        (proEtaleRingDerivedPullback (h ≫ k) (proEtaleConstantRing V A)
          (proEtaleConstantRing Z A))
        (proEtaleConstantRingCompositeCoefficients_eq h k A).symm) ≪≫
          proEtaleCanonicalPullbackComposition h k (proEtaleConstantRing V A)
            (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
            (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A) := by
    rw [proEtaleConstantRingPullbackComposition_eq]
    rfl
  rw [he]
  exact pullbackData_transport h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A)
    (proEtaleConstantRingComparison (h ≫ k) A)
    (proEtaleConstantRingCompositeCoefficients_eq h k A)

@[irreducible] private noncomputable def ordinaryComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (h ≫ k) ≅
      proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h :=
  (constantData h k A).a

@[irreducible] private noncomputable def directComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPushforward A h ⋙ proEtaleConstantRingPushforward A k ≅
      proEtaleConstantRingPushforward A (h ≫ k) :=
  (constantData h k A).d

private theorem mate_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {RF : D ⥤ C} {RG : E ⥤ D} {RH : E ⥤ C}
    (ak ak' : F ⊣ RF) (ah ah' : G ⊣ RG) (ac ac' : H ⊣ RH)
    (hk : ak = ak') (hh : ah = ah') (hc : ac = ac')
    (a : H ≅ F ⋙ G) (d : RG ⋙ RF ≅ RH)
    (ha : conjugateIsoEquiv (ak.comp ah) ac a = d) :
    a = (Adjunction.leftAdjointCompIso ak' ah' ac' d).symm := by
  subst ak'
  subst ah'
  subst ac'
  apply (conjugateIsoEquiv (ak.comp ah) ac).injective
  rw [ha]
  exact ((conjugateIsoEquiv (ak.comp ah) ac).apply_symm_apply d).symm

@[irreducible] private noncomputable def normalizedAdj
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  (constantData f (𝟙 Y) A).adjh

private theorem normalizedAdj_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    (hn : proEtaleRingModuleAdjunctionNormalized f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) adj) :
    adj = normalizedAdj f A := by
  unfold normalizedAdj
  unfold proEtaleRingModuleAdjunctionNormalized at hn
  have nh := (constantData f (𝟙 Y) A).nh
  unfold proEtaleRingModuleAdjunctionNormalized at nh
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (hn M U.unop m).trans (nh M U.unop m).symm

private theorem ordinaryComp_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    ordinaryComp h k A =
      (Adjunction.leftAdjointCompIso (normalizedAdj k A) (normalizedAdj h A)
        (normalizedAdj (h ≫ k) A) (directComp h k A)).symm := by
  unfold ordinaryComp directComp
  exact mate_eq _ _ _ _ _ _
    (normalizedAdj_eq k A _ (constantData h k A).nk)
    (normalizedAdj_eq h A _ (constantData h k A).nh)
    (normalizedAdj_eq (h ≫ k) A _ (constantData h k A).nc)
    (constantData h k A).a (constantData h k A).d (constantData h k A).ha

private theorem derivedFormula_components
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G)
    (b : H.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ))
    (hb : ∀ (K : CochainComplex C ℤ) (n : ℤ), (b.hom.app K).f n = a.hom.app (K.X n))
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (b.hom.app K) =
      (Functor.mapDerivedCategoryNatIso a ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have hbK : b.hom.app K =
      (NatTrans.mapHomologicalComplex a.hom (ComplexShape.up ℤ)).app K := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hb K n
  rw [hbK]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  exact (Functor.mapDerivedCategoryNatIso_fac a K).symm

private theorem pullbackData_comparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c)
    (comparison : proEtaleRingDerivedPullback (h ≫ k) RV RZ c ≅
      proEtaleRingDerivedPullback k RV RW ck ⋙ proEtaleRingDerivedPullback h RW RZ ch)
    (D : PullbackData h k RV RW RZ ck ch c hc comparison) :
    comparison = Functor.mapDerivedCategoryNatIso D.a ≪≫
      (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
        (proEtaleRingModulePullback h RW RZ ch)).symm := by
  apply UniqueData.unique_of_formula (proEtaleCanonicalPullbackComposition_existsUnique
    h k RV RW RZ ck ch c hc.symm) D
  intro b hb hD K hK hflat
  refine ⟨(hD K hK hflat).1, (hD K hK hflat).2.1, ?_⟩
  unfold proEtaleRingDerivedPullbackFactors
  exact derivedFormula_components (proEtaleRingModulePullback k RV RW ck)
    (proEtaleRingModulePullback h RW RZ ch) (proEtaleRingModulePullback (h ≫ k) RV RZ c)
    D.a b hb K

private theorem constantComparison_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    (proEtaleConstantRingPullbackComposition h k A).symm =
      Functor.mapDerivedCategoryNatIso (ordinaryComp h k A) ≪≫
        (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A k)
          (proEtaleConstantRingPullback A h)).symm := by
  unfold ordinaryComp
  exact pullbackData_comparison h k _ _ _ _ _ _ _ _ (constantData h k A)

private theorem directImage_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A]
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    ((eqToIso (congrArg (proEtaleConstantRingPushforward A) e)).hom.app N).val.app
        (Opposite.op U) m =
      N.val.map (eqToHom (congrArg (fun t ↦ (proEtaleBaseChange t).obj U) e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directComp_hom_apply
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (U : V.ProEt)
    (m : ((proEtaleConstantRingPushforward A h ⋙
      proEtaleConstantRingPushforward A k).obj N).val.obj (Opposite.op U)) :
    ((directComp h k A).hom.app N).val.app (Opposite.op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m := by
  unfold directComp
  exact (constantData h k A).hd N U m

/-- The finite-coefficient comparison is the localization of the ordinary module comparison, with
its tensor-unit normalization. -/
theorem proEtaleConstantRingPullbackComposition_eq_mapModuleComparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] [Finite A] :
    (proEtaleConstantRingPullbackComposition h k A).symm =
      Functor.mapDerivedCategoryNatIso
        (proEtaleConstantRingModulePullbackComposition h k A).choose ≪≫
      (Functor.mapDerivedCategoryCompIso
        (proEtaleConstantRingPullback A k) (proEtaleConstantRingPullback A h)).symm := by
  have hn {X Y : Scheme.{u}} (f : X ⟶ Y) :
      proEtaleConstantRingAdjunction A f = normalizedAdj f A :=
    normalizedAdj_eq f A _ (proEtaleRingModuleAdjunction_normalized f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A))
  have ha : (proEtaleConstantRingModulePullbackComposition h k A).choose =
      ordinaryComp h k A := by
    obtain ⟨d, hd, he⟩ :=
      (proEtaleConstantRingModulePullbackComposition h k A).choose_spec
    have hde : d = directComp h k A := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      exact (hd N U.unop m).trans (directComp_hom_apply h k A N U.unop m).symm
    rw [ordinaryComp_eq, ← hn k, ← hn h, ← hn (h ≫ k)]
    apply (conjugateIsoEquiv ((proEtaleConstantRingAdjunction A k).comp
      (proEtaleConstantRingAdjunction A h))
      (proEtaleConstantRingAdjunction A (h ≫ k))).injective
    rw [he, hde]
    exact ((conjugateIsoEquiv ((proEtaleConstantRingAdjunction A k).comp
      (proEtaleConstantRingAdjunction A h))
      (proEtaleConstantRingAdjunction A (h ≫ k))).apply_symm_apply
        (directComp h k A)).symm
  rw [constantComparison_eq, ha]

end AlgebraicGeometry.Scheme
