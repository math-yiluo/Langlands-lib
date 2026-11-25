/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# The explicit pro-etale tensor comparison and its adjunction units

Source: Stacks Project, Modules on Sites, Tag 03D3, lemma-adjoint-push-pull-modules;
Sites, Tag 03CB, lemma-composition-morphisms-sites; Categories, Tag 0B65
(auxiliary; not a blueprint node).

The generator formulas use the coprojections of the inverse-image colimits, followed by
sheafification. All test objects and all indexing arrows are quantified. Thus the formulas
specify the tensor maps before using the adjunction-unit equation to characterize them.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The local tensor generator `m ⊗ r`, indexed by `p : T ⟶ B_f U`.
The specified module adjunction sends `m` to the sheafification of `m ⊗ 1`;
restriction along `p`, followed by multiplication by `r`, is the general generator.
This uses the uniquely tensor-normalized adjunction, not an arbitrary adjunction.
Source: Stacks, Tag 03D3 and the inverse-image colimit of Sites, Tag 00VC
(auxiliary; not a blueprint node). -/
def proEtalePullbackTensorGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (U : Y.ProEt) (T : X.ProEt)
    (p : T ⟶ (proEtaleBaseChange f).obj U)
    (m : M.val.obj (op U)) (r : S.obj.obj (op T)) :
    ((proEtaleRingModulePullback f R S c).obj M).val.obj (op T) :=
  r • (((proEtaleRingModulePullback f R S c).obj M).val.restrictₛₗ p.op
    (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) m))

/-- The image of a local scalar in the source coefficient sheaf: apply the ring map
adjoint to `c`, then restrict along the inverse-image index arrow. Under the canonical
inverse-image identifications this is `c(a)`.
Source: Stacks, Tag 03D3 and Sites, Tag 00VC
(auxiliary; not a blueprint node). -/
def proEtalePullbackTensorScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (U : Y.ProEt) (T : X.ProEt) (p : T ⟶ (proEtaleBaseChange f).obj U)
    (a : R.obj.obj (op U)) : S.obj.obj (op T) :=
  (S.obj.map p.op).hom
    (((proEtaleRingDirectImageMap f R S c).hom.app (op U)).hom a)

attribute [local irreducible] proEtaleRingModulePullbackObj
  proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency false in
private theorem unit_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (U : Y.ProEt)
    (a : R.obj.obj (op U)) (m : M.val.obj (op U)) :
    ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) (a • m) =
      @SMul.smul (S.obj.obj (op ((proEtaleBaseChange f).obj U)))
        (((proEtaleRingModulePullback f R S c).obj M).val.obj
          (op ((proEtaleBaseChange f).obj U))) inferInstance
        (((proEtaleRingDirectImageMap f R S c).hom.app (op U)).hom a)
        (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) m) :=
  (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U)).hom.map_smul a m

private theorem unit_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) {U T : Y.ProEt} (p : T ⟶ U)
    (m : M.val.obj (op U)) :
    ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op T)
        (M.val.map p.op m) =
      ((proEtaleRingModulePullback f R S c).obj M).val.map
        ((proEtaleBaseChange f).map p).op
          (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) m) :=
  PresheafOfModules.naturality_apply
    ((proEtaleRingModuleAdjunction f R S c).unit.app M).val p.op m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_comp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = (proEtaleRingInverseImageComp h k).app R_V ≪≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c_k ≪≫ c_h) :
    proEtaleRingDirectImageMap (h ≫ k) R_V R_Z c_hk ≫
      (Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp h k).symm) CommRingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology W) (ProEt.topology Z)).inv.app R_Z =
      proEtaleRingDirectImageMap k R_V R_W c_k ≫
        (proEtaleSheafDirectImage k CommRingCat.{u + 1}).map
          (proEtaleRingDirectImageMap h R_W R_Z c_h) := by
  let adj := proEtaleSheafAdjunction (h ≫ k) CommRingCat.{u + 1}
  let adjk := proEtaleSheafAdjunction k CommRingCat.{u + 1}
  let adjh := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp h k).symm) CommRingCat.{u + 1}
    (ProEt.topology V) (ProEt.topology W) (ProEt.topology Z)
  have hu := unit_conjugateEquiv_symm (adjk.comp adjh) adj e.hom R_V
  change (adjk.comp adjh).unit.app R_V ≫ e.hom.app _ =
    adj.unit.app R_V ≫ _ at hu
  change (adjk.comp adjh).unit.app R_V ≫ e.hom.app _ =
    adj.unit.app R_V ≫ (proEtaleSheafDirectImage (h ≫ k) CommRingCat.{u + 1}).map
      ((proEtaleRingInverseImageComp h k).hom.app R_V) at hu
  subst c_hk
  unfold proEtaleRingDirectImageMap
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    ← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  dsimp only [proEtaleSheafDirectImage, ProEtale.lowerStar] at *
  rw [← e.hom.naturality_assoc, ← e.hom.naturality_assoc]
  dsimp only [e] at *
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  rw [Adjunction.comp_unit_app]
  have hn := adjh.unit.naturality c_k.hom
  have hn' := congrArg (fun z ↦ adjk.unit.app R_V ≫
    (proEtaleSheafDirectImage k CommRingCat.{u + 1}).map
      (z ≫ (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map c_h.hom)) hn.symm
  dsimp only [adjk, adjh, proEtaleSheafDirectImage, ProEtale.lowerStar] at hn' ⊢
  simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map, Category.assoc] using hn'

private theorem adjunction_map_injective {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {M : C} {N : D}
    {f g : F.obj M ⟶ N}
    (h : a.unit.app M ≫ G.map f = a.unit.app M ≫ G.map g) : f = g :=
  (a.homEquiv M N).injective h

private theorem composite_unit_map {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (a : F ⊣ G) (b : H ⊣ I) (M : C) {N : E} (f : (F ⋙ H).obj M ⟶ N) :
    (a.comp b).unit.app M ≫ (I ⋙ G).map f =
      a.unit.app M ≫ G.map (b.unit.app (F.obj M)) ≫ (I ⋙ G).map f := by
  rw [Adjunction.comp_unit_app, Category.assoc]

private theorem comp_iso_map_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X : C} {Y Z : D} (e : Y ≅ F.obj X) (p : Z ⟶ Y) :
    (p ≫ e.hom) ≫ F.map (𝟙 X) ≫ e.inv = p := by
  rw [F.map_id, Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem iso_inv_hom_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    e.inv.val.app U (e.hom.val.app U m) = m :=
  congrArg (fun z : M ⟶ M ↦ z.val.app U m) e.hom_inv_id

private theorem mate_iso {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (d : R₁ ≅ R₂) : ∃ t : L₂ ≅ L₁, ∀ M : C,
      b.unit.app M ≫ R₂.map (t.hom.app M) = a.unit.app M ≫ d.hom.app _ := by
  refine ⟨(conjugateIsoEquiv a b).symm d, ?_⟩
  intro M
  exact (unit_conjugateEquiv_symm a b d.hom M).symm

attribute [local irreducible] proEtaleRingModulePullback

/-- The tensor formulas define inverse natural module maps, preserving the specified
composite adjunction unit, and uniquely characterized by that unit equation.
Source: Stacks, Tags 03D3, 03CB and 0B65; the explicit tensor calculation is the agent
deduction recorded in the blueprint (auxiliary; not a blueprint node).

The equality `hc_hk` only names the prescribed composite coefficient identification.
`Over.pullbackComp.hom` goes from composite base change to iterated base change;
its inverse is the paper's `q`. The two generator clauses are respectively
`(m ⊗ a) ⊗ b ↦ m ⊗ c_h(a)b` and `m ⊗ b ↦ (m ⊗ 1) ⊗ b`.
The colimit and sheafification universal properties make these clauses equivalent to
those formulas for arbitrary local inverse-image sections: one can check maps on every
indexing coprojection, and pure tensors generate the sectionwise tensor products.

Proof:
1. The ring inverse-image comparison is the mate of the fibre-product pushforward
comparison. Its unit equation and naturality with the coefficient identifications give
compatibility of the direct-image coefficient maps with composition.
2. Apply the module pushforward comparison along the fibre-product isomorphism, followed
by the comparison with successive pushforwards, to obtain d. Its section maps are exactly
restriction along the specified inverse fibre-product comparison. Let t be its adjunction
mate. The mate unit equation is the asserted composite-unit equation.
3. Evaluate that equation on a section m. Expand the generators as scalar multiples of
restrictions of units. The units are linear through their coefficient maps, and units and
t commute with restrictions. Move the two scalars outside t and apply the evaluated unit
equation. Functoriality of restrictions and multiplication of scalars give the forward
formula for every pair of indexing arrows.
4. Specialize the forward formula to the identity first indexing arrow and intermediate
scalar 1. Ring maps preserve 1 and the fibre-product comparisons cancel. Apply t.inv to
obtain the inverse formula. Finally the injectivity of the composite adjunction Hom
correspondence proves uniqueness among all natural transformations. -/
theorem proEtale_tensor_composition_unit
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = (proEtaleRingInverseImageComp h k).app R_V ≪≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c_k ≪≫ c_h) :
    ∃ (d : proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk ≅
          proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k)
      (t : proEtaleRingModulePullback k R_V R_W c_k ⋙
          proEtaleRingModulePullback h R_W R_Z c_h ≅
            proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk),
      (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
        (m : ((proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk).obj N).val.obj
          (op U)),
        (d.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).inv.app U).op m) ∧
      (∀ (M : proEtaleRingModules V R_V) (U : V.ProEt) (T : W.ProEt) (P : Z.ProEt)
        (p : T ⟶ (proEtaleBaseChange k).obj U)
        (q : P ⟶ (proEtaleBaseChange h).obj T)
        (m : M.val.obj (op U)) (a : R_W.obj.obj (op T)) (b : R_Z.obj.obj (op P)),
        (t.hom.app M).val.app (op P)
          (proEtalePullbackTensorGenerator h R_W R_Z c_h
            ((proEtaleRingModulePullback k R_V R_W c_k).obj M) T P q
            (proEtalePullbackTensorGenerator k R_V R_W c_k M U T p m a) b) =
          proEtalePullbackTensorGenerator (h ≫ k) R_V R_Z c_hk M U P
            (q ≫ (proEtaleBaseChange h).map p ≫
              (MorphismProperty.Over.pullbackComp h k).inv.app U) m
            (proEtalePullbackTensorScalar h R_W R_Z c_h T P q a * b)) ∧
      (∀ (M : proEtaleRingModules V R_V) (U : V.ProEt) (P : Z.ProEt)
        (p : P ⟶ (proEtaleBaseChange (h ≫ k)).obj U)
        (m : M.val.obj (op U)) (b : R_Z.obj.obj (op P)),
        (t.inv.app M).val.app (op P)
          (proEtalePullbackTensorGenerator (h ≫ k) R_V R_Z c_hk M U P p m b) =
          proEtalePullbackTensorGenerator h R_W R_Z c_h
            ((proEtaleRingModulePullback k R_V R_W c_k).obj M)
            ((proEtaleBaseChange k).obj U) P
            (p ≫ (MorphismProperty.Over.pullbackComp h k).hom.app U)
            (proEtalePullbackTensorGenerator k R_V R_W c_k M U
              ((proEtaleBaseChange k).obj U) (𝟙 _) m 1) b) ∧
      (∀ M : proEtaleRingModules V R_V,
        (proEtaleRingModuleAdjunction k R_V R_W c_k).unit.app M ≫
          (proEtaleRingModuleDirectImage k R_V R_W c_k).map
            ((proEtaleRingModuleAdjunction h R_W R_Z c_h).unit.app
              ((proEtaleRingModulePullback k R_V R_W c_k).obj M)) ≫
          (proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k).map (t.hom.app M) =
        (proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk).unit.app M ≫
          d.hom.app ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M)) ∧
      (∀ t' : proEtaleRingModulePullback k R_V R_W c_k ⋙
          proEtaleRingModulePullback h R_W R_Z c_h ⟶
            proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk,
        (∀ M : proEtaleRingModules V R_V,
          ((proEtaleRingModuleAdjunction k R_V R_W c_k).comp
            (proEtaleRingModuleAdjunction h R_W R_Z c_h)).unit.app M ≫
            (proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).map (t'.app M) =
          (proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk).unit.app M ≫
            d.hom.app ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M)) →
        t' = t.hom) := by
  let : HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify (ProEt.topology V) CommRingCat.{u + 1} := inferInstance
  let ρk := (show (sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_V ⟶
      ((proEtaleBaseChange k).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology W)).obj
          ((sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_W) from
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap k R_V R_W c_k).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  let ρh := (show (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_W ⟶
      ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology W) (ProEt.topology Z)).obj
          ((sheafCompose (ProEt.topology Z)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Z) from
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap h R_W R_Z c_h).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  let ρhk := (show (sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_V ⟶
      ((proEtaleBaseChange (h ≫ k)).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology Z)).obj
          ((sheafCompose (ProEt.topology Z)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Z) from
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap (h ≫ k) R_V R_Z c_hk).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  let : (proEtaleBaseChange k ⋙ proEtaleBaseChange h).IsContinuous
      (ProEt.topology V) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (ProEt.topology V) (ProEt.topology W)
      (ProEt.topology Z)
  let ρiter := ρk ≫ ((proEtaleBaseChange k).sheafPushforwardContinuous
    RingCat.{u + 1} (ProEt.topology V) (ProEt.topology W)).map ρh
  have he : ρhk ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackComp h k).inv RingCat.{u + 1}
      (ProEt.topology V) (ProEt.topology Z)).app
        ((sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Z) = ρiter := by
    ext U r
    exact congrArg (fun z ↦ (z.hom.app U).hom r)
      (coefficient_comp h k R_V R_W R_Z c_k c_h c_hk hc_hk)
  let d : proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk ≅
      proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
        proEtaleRingModuleDirectImage k R_V R_W c_k :=
    SheafOfModules.pushforwardCongr₂
      (F := proEtaleBaseChange k ⋙ proEtaleBaseChange h)
      (G := proEtaleBaseChange (h ≫ k))
      (J := ProEt.topology V) (K := ProEt.topology Z) (φ := ρhk) (ψ := ρiter)
      (MorphismProperty.Over.pullbackComp h k).symm he ≪≫
        (SheafOfModules.pushforwardComp ρk ρh).symm
  let adj := proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk
  let adjiter := (proEtaleRingModuleAdjunction k R_V R_W c_k).comp
    (proEtaleRingModuleAdjunction h R_W R_Z c_h)
  obtain ⟨t, ht⟩ := mate_iso adj adjiter d
  have hforward : ∀ (M : proEtaleRingModules V R_V)
        (U : V.ProEt) (T : W.ProEt) (P : Z.ProEt)
        (p : T ⟶ (proEtaleBaseChange k).obj U)
        (q : P ⟶ (proEtaleBaseChange h).obj T)
        (m : M.val.obj (op U)) (a : R_W.obj.obj (op T)) (b : R_Z.obj.obj (op P)),
        (t.hom.app M).val.app (op P)
          (proEtalePullbackTensorGenerator h R_W R_Z c_h
            ((proEtaleRingModulePullback k R_V R_W c_k).obj M) T P q
            (proEtalePullbackTensorGenerator k R_V R_W c_k M U T p m a) b) =
          proEtalePullbackTensorGenerator (h ≫ k) R_V R_Z c_hk M U P
            (q ≫ (proEtaleBaseChange h).map p ≫
              (MorphismProperty.Over.pullbackComp h k).inv.app U) m
            (proEtalePullbackTensorScalar h R_W R_Z c_h T P q a * b) := by
    intro M U T P p q m a b
    have hu := congrArg (fun z ↦ z.val.app (op U) m) (ht M)
    change (t.hom.app M).val.app (op ((proEtaleBaseChange h).obj
        ((proEtaleBaseChange k).obj U)))
        (((proEtaleRingModuleAdjunction h R_W R_Z c_h).unit.app
          ((proEtaleRingModulePullback k R_V R_W c_k).obj M)).val.app
            (op ((proEtaleBaseChange k).obj U))
              (((proEtaleRingModuleAdjunction k R_V R_W c_k).unit.app M).val.app
                (op U) m)) =
      ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h k).inv.app U).op
          (((proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk).unit.app M).val.app
            (op U) m) at hu
    unfold proEtalePullbackTensorGenerator
    simp only [PresheafOfModules.restrictₛₗ_apply]
    rw [unit_smul]
    erw [PresheafOfModules.map_smul]
    rw [map_smul, map_smul, unit_restrict]
    have hnq := PresheafOfModules.naturality_apply (t.hom.app M).val q.op
      (((proEtaleRingModulePullback h R_W R_Z c_h).obj
        ((proEtaleRingModulePullback k R_V R_W c_k).obj M)).val.map
          ((proEtaleBaseChange h).map p).op
        (((proEtaleRingModuleAdjunction h R_W R_Z c_h).unit.app
          ((proEtaleRingModulePullback k R_V R_W c_k).obj M)).val.app
            (op ((proEtaleBaseChange k).obj U))
          (((proEtaleRingModuleAdjunction k R_V R_W c_k).unit.app M).val.app
            (op U) m)))
    dsimp only [Functor.comp_obj] at hnq
    have hnp := PresheafOfModules.naturality_apply (t.hom.app M).val
      ((proEtaleBaseChange h).map p).op
      (((proEtaleRingModuleAdjunction h R_W R_Z c_h).unit.app
        ((proEtaleRingModulePullback k R_V R_W c_k).obj M)).val.app
          (op ((proEtaleBaseChange k).obj U))
        (((proEtaleRingModuleAdjunction k R_V R_W c_k).unit.app M).val.app
          (op U) m))
    have heq := hnq.trans (congrArg (fun z ↦
      ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M).val.map q.op z)
        (hnp.trans (congrArg (fun z ↦
          ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M).val.map
            ((proEtaleBaseChange h).map p).op z) hu)))
    have hs := congrArg (fun z ↦
      b • (proEtalePullbackTensorScalar h R_W R_Z c_h T P q a • z)) heq
    have hscalar :
        (((sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Z).obj.map q.op)
            (((proEtaleRingDirectImageMap h R_W R_Z c_h).hom.app (op T)).hom a) =
          proEtalePullbackTensorScalar h R_W R_Z c_h T P q a := rfl
    simp only [hscalar, op_comp,
      PresheafOfModules.map_comp_apply, ← mul_smul, mul_comm] at hs ⊢
    convert hs using 1
  refine ⟨d, t, ?_, hforward, ?_, ?_, ?_⟩
  · intro N U m
    rfl
  · intro M U P p m b
    have hf := hforward M U ((proEtaleBaseChange k).obj U) P (𝟙 _)
      (p ≫ (MorphismProperty.Over.pullbackComp h k).hom.app U) m 1 b
    simp only [proEtalePullbackTensorScalar, map_one, one_mul] at hf
    have hp : (p ≫ (MorphismProperty.Over.pullbackComp h k).hom.app U) ≫
        (proEtaleBaseChange h).map (𝟙 ((proEtaleBaseChange k).obj U)) ≫
          (MorphismProperty.Over.pullbackComp h k).inv.app U = p :=
      comp_iso_map_id (proEtaleBaseChange h)
        ((MorphismProperty.Over.pullbackComp h k).app U) p
    rw [hp] at hf
    let ti := (t.inv.app M).val.app (op P)
    change ti _ = _
    exact (congrArg ti hf).symm.trans
      (iso_inv_hom_apply (t.app M) (op P) _)
  · intro M
    exact (composite_unit_map (proEtaleRingModuleAdjunction k R_V R_W c_k)
      (proEtaleRingModuleAdjunction h R_W R_Z c_h) M (t.hom.app M)).symm.trans (ht M)
  · intro t' ht'
    apply NatTrans.ext
    funext M
    exact adjunction_map_injective adjiter ((ht' M).trans (ht M).symm)

end AlgebraicGeometry.Scheme
