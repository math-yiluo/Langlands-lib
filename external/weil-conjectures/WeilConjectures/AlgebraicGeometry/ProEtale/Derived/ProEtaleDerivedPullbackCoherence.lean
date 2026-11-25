/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Associativity of canonical finite-coefficient derived pro-etale pullback comparisons

## References

* Stacks Project, Tag 0D6D, its K-flat representative computation and the associativity of
  inverse-image comparisons
* Stacks Tags 05V1 and 0D6D
* Stacks, Modules on Sites
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

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable instance (priority := 10000) fixedAbelianStalkSite (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

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

private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

private theorem site_pasting
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z W : C} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (U : P.Over Q X) :
    (MorphismProperty.Over.pullbackComp j (h ≫ k)).hom.app U ≫
        (MorphismProperty.Over.pullback P Q j).map
          ((MorphismProperty.Over.pullbackComp h k).hom.app U) =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.assoc j h k).symm) ≫
        (MorphismProperty.Over.pullbackComp (j ≫ h) k).hom.app U ≫
        (MorphismProperty.Over.pullbackComp j h).hom.app
          ((MorphismProperty.Over.pullback P Q k).obj U) := by
  have hp := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := Q) j h k)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [pasting_transport (j ≫ h) k (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
  simpa only [Category.assoc] using hp

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

private theorem directImage_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    {N N' : proEtaleRingModules X (proEtaleConstantRing X A)} (a : N ⟶ N') (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    (((proEtaleConstantRingPushforward A f).map a).val.app (Opposite.op U)) m =
      a.val.app (Opposite.op ((proEtaleBaseChange f).obj U)) m := rfl

private theorem directImage_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (N : proEtaleRingModules X (proEtaleConstantRing X A))
    {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op V)) :
    (((proEtaleConstantRingPushforward A f).obj N).val.map a.op) m =
      N.val.map ((proEtaleBaseChange f).map a).op m := rfl

private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules R)
    {U V T U' V' : C} (a : U ⟶ V) (b : V ⟶ T)
    (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (Opposite.op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directImage_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] :
    Functor.isoWhiskerLeft (proEtaleConstantRingPushforward A j) (directComp h k A) ≪≫
        (directComp j (h ≫ k) A) =
      (Functor.associator (proEtaleConstantRingPushforward A j)
          (proEtaleConstantRingPushforward A h)
          (proEtaleConstantRingPushforward A k)).symm ≪≫
        Functor.isoWhiskerRight (directComp j h A)
          (proEtaleConstantRingPushforward A k) ≪≫
        (directComp (j ≫ h) k A) ≪≫
        eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply k A ((directComp j h A).hom.app N) U]
  erw [directComp_hom_apply j h A N ((proEtaleBaseChange k).obj U)]
  erw [directComp_hom_apply (j ≫ h) k A N U]
  conv_rhs => erw [directImage_transport (Category.assoc j h k) A N U]
  conv_lhs => erw [directComp_hom_apply h k A
    ((proEtaleConstantRingPushforward A j).obj N) U m]
  conv_lhs => erw [directComp_hom_apply j (h ≫ k) A N U]
  conv_lhs => erw [directImage_obj_map_apply j A N
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  exact restriction_pasting N.val _ _ _ _ _
    (site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U) m

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

private theorem ordinary_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (ordinaryComp j (h ≫ k) A).hom.app M ≫
        (proEtaleConstantRingPullback A j).map ((ordinaryComp h k A).hom.app M) =
      (eqToIso (congrArg (proEtaleConstantRingPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (ordinaryComp (j ≫ h) k A).hom.app M ≫
        (ordinaryComp j h A).hom.app ((proEtaleConstantRingPullback A k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (normalizedAdj k A) (normalizedAdj h A) (normalizedAdj j A)
    (normalizedAdj (h ≫ k) A) (normalizedAdj (j ≫ h) A)
    (normalizedAdj (j ≫ h ≫ k) A)
    (directComp h k A) (directComp j h A)
    ((directComp (j ≫ h) k A) ≪≫
      eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)))
    (directComp j (h ≫ k) A) (directImage_coherence j h k A)
  have ht := mate_transport (proEtaleConstantRingPullback A)
    (proEtaleConstantRingPushforward A) (fun f ↦ normalizedAdj f A)
    (normalizedAdj k A) (normalizedAdj (j ≫ h) A) (Category.assoc j h k)
    (directComp (j ≫ h) k A)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [ordinaryComp_eq, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

private theorem descend_coherence
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (F02 : C ⥤ E) (F13 : D ⥤ B) (F03 F03' : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [F02.Additive] [F13.Additive]
    [F03.Additive] [F03'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F02] [PreservesFiniteColimits F02]
    [PreservesFiniteLimits F13] [PreservesFiniteColimits F13]
    [PreservesFiniteLimits F03] [PreservesFiniteColimits F03]
    [PreservesFiniteLimits F03'] [PreservesFiniteColimits F03']
    (a02 : F02 ≅ F ⋙ G) (a13 : F13 ≅ G ⋙ H)
    (a0 : F03 ≅ F02 ⋙ H) (a1 : F03' ≅ F ⋙ F13) (e : F03 ≅ F03')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    (Functor.mapDerivedCategoryNatIso a0).hom ≫
        (Functor.mapDerivedCategoryCompIso F02 H).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a02).hom
          H.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).inv
          H.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso a1).hom ≫
        (Functor.mapDerivedCategoryCompIso F F13).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso a13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).inv := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hR := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a02 H
  have hL := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F a13
  have hC := Functor.mapDerivedCategoryCompIso_assoc F G H
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F02 H).inv,
    ← hR, Category.assoc, ← hC]
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso G H).inv) hd
  calc
    _ = ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryNatIso a1).hom ≫
          (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F a13)).hom) ≫
        (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H).inv := by
            simpa only [Category.assoc] using ht
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F a13)).hom, hL]
      simp only [Category.assoc]

private theorem derived_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (proEtaleConstantRingPullback A) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem moduleAdj_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized f R S c (proEtaleRingModuleAdjunction f R S c) := by
  let : (proEtaleModelBaseChange f).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) := proEtaleModelBaseChange_isContinuous f
  unfold proEtaleRingModuleAdjunctionNormalized
  intro M U m
  have hp := (Classical.choose_spec (proEtaleRingModuleAdjunction_existsUnique f R S c)).1
  obtain ⟨g, hg, hf⟩ := hp M _ (𝟙 _)
  have h := hf (op U) m
  rw [Adjunction.homEquiv_id] at h
  rw [Adjunction.homEquiv_unit] at h
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at h
  erw [hg] at h
  unfold proEtaleRingModuleAdjunction proEtaleRingModuleUnitSection
  exact h

private theorem ordinaryComp_unit
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    ((proEtaleConstantRingAdjunction A f).comp
      (proEtaleConstantRingAdjunction A h)).unit.app M ≫
        (directComp h f A).hom.app
          (((proEtaleConstantRingPullback A f) ⋙ proEtaleConstantRingPullback A h).obj M) =
      (proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M ≫
        (proEtaleConstantRingPushforward A (h ≫ f)).map
          ((ordinaryComp h f A).hom.app M) := by
  have hk := normalizedAdj_eq f A (proEtaleConstantRingAdjunction A f)
    (moduleAdj_normalized f _ _ _)
  have hh := normalizedAdj_eq h A (proEtaleConstantRingAdjunction A h)
    (moduleAdj_normalized h _ _ _)
  have hc := normalizedAdj_eq (h ≫ f) A (proEtaleConstantRingAdjunction A (h ≫ f))
    (moduleAdj_normalized (h ≫ f) _ _ _)
  rw [hk, hh, hc, ordinaryComp_eq]
  have q := unit_conjugateEquiv ((normalizedAdj f A).comp (normalizedAdj h A))
    (normalizedAdj (h ≫ f) A)
    (Adjunction.leftAdjointCompIso (normalizedAdj f A) (normalizedAdj h A)
      (normalizedAdj (h ≫ f) A) (directComp h f A)).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at q
  exact q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ordinaryComp_unit_section
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
    (a : M.val.obj (op U)) :
    (((ordinaryComp h f A).hom.app M).val.app
      (op ((proEtaleBaseChange (h ≫ f)).obj U)))
        ((((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app (op U)) a) =
      (((proEtaleConstantRingPullback A h).obj
        ((proEtaleConstantRingPullback A f).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) h f).hom.app
              U).op)
        ((((proEtaleConstantRingAdjunction A h).unit.app
          ((proEtaleConstantRingPullback A f).obj M)).val.app
            (op ((proEtaleBaseChange f).obj U)))
          ((((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op U)) a)) := by
  have q := congrArg (fun k ↦ k.val.app (op U) a) (ordinaryComp_unit h f A M)
  rw [Adjunction.comp_unit_app] at q
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at q
  erw [directComp_hom_apply, directImage_map_apply] at q
  exact q.symm

/-- The canonical derived compositor is induced by an ordinary pullback isomorphism
whose unit sections restrict along fibre-product pasting. This packages the normalization
without exposing its chosen witnesses. -/
theorem proEtaleConstantRingPullbackComposition_ordinary
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (A : Type u) [CommRing A] :
    ∃ a : proEtaleConstantRingPullback A (h ≫ f) ≅
        proEtaleConstantRingPullback A f ⋙ proEtaleConstantRingPullback A h,
      (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
        (z : M.val.obj (Opposite.op U)),
        ((a.hom.app M).val.app (Opposite.op ((proEtaleBaseChange (h ≫ f)).obj U)))
          ((((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app
            (Opposite.op U)) z) =
        (((proEtaleConstantRingPullback A h).obj
          ((proEtaleConstantRingPullback A f).obj M)).val.map
            ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) h f).hom.app
              U).op)
          ((((proEtaleConstantRingAdjunction A h).unit.app
            ((proEtaleConstantRingPullback A f).obj M)).val.app
              (Opposite.op ((proEtaleBaseChange f).obj U)))
            ((((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U)) z))) ∧
      Functor.mapDerivedCategoryNatIso a ≪≫
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A f)
            (proEtaleConstantRingPullback A h)).symm =
        (proEtaleConstantRingPullbackComposition h f A).symm := by
  exact ⟨ordinaryComp h f A, ordinaryComp_unit_section h f A,
    (constantComparison_eq h f A).symm⟩

/-- Forgetting the constant coefficient action identifies the module-pullback unit
with an invertible underlying abelian inverse-image comparison. -/
theorem proEtaleConstantRingPullback_underlyingUnit_isIso
    (A : Type u) [CommRing A] {T S : Scheme.{u}} (t : T ⟶ S)
    (M : proEtaleRingModules S (proEtaleConstantRing S A)) :
    IsIso (((proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj ((proEtaleConstantRingPullback A t).obj M))).symm
        ((SheafOfModules.toSheaf _).map
          ((proEtaleConstantRingAdjunction A t).unit.app M))) := by
  exact ringUnitComparison t (proEtaleConstantRing S A) (proEtaleConstantRing T A)
    (proEtaleConstantRingComparison t A) (proEtaleConstantRingAdjunction A t) M

end AlgebraicGeometry.Scheme
