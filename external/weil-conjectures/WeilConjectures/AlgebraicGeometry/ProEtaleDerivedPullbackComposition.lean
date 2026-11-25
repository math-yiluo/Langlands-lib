/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Composition of derived pro-etale module pullbacks

Source: Stacks Project, sites-cohomology.tex, Lemma 0D6D
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The induced identification on the composite, with no independent third choice.
Source: Stacks, Tags 03D8 and 0D6D
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingCompositeCoefficients
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z) :
    (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z :=
  (proEtaleRingInverseImageComp h k).app R_V ≪≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c_k ≪≫ c_h

/-- Section of the canonical module unit: the model-site inverse-image unit followed
by the sheafification of `1 ⊗ m`. The model only enlarges the Hom universe.
Source: Stacks, Tags 03D2, 03EK and 03D8
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingModuleUnitSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (Opposite.op U)) :
    ((proEtaleRingModuleDirectImage f R S c).obj
      ((proEtaleRingModulePullback f R S c).obj M)).val.obj (Opposite.op U) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheaf c.hom
      ((proEtaleModuleInverseImage f R).obj M)).presheaf).app
        (Opposite.op ((proEtaleBaseChange f).obj U))
    ((1 : S.obj.obj (Opposite.op ((proEtaleBaseChange f).obj U))) ⊗ₜ[
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj
        (Opposite.op ((proEtaleBaseChange f).obj U)),
      (c.hom.hom.app (Opposite.op ((proEtaleBaseChange f).obj U))).hom]
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
            (Opposite.op (AsSmall.up.obj U)) m))

/-- Normalization of the module adjunction by its constructed unit on every section.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
def proEtaleRingModuleAdjunctionNormalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c) :
    Prop :=
  ∀ (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (Opposite.op U)),
    (adj.unit.app M).val.app (Opposite.op U) m = proEtaleRingModuleUnitSection f R S c M U m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalAdjunction_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized f R S c
      (proEtaleRingModuleAdjunction f R S c) := by
  intro M U m
  obtain ⟨g, hg, he⟩ :=
    (Classical.choose_spec (proEtaleRingModuleAdjunction_existsUnique f R S c)).1 M _ (𝟙 _)
  rw [Adjunction.homEquiv_id] at he
  exact (he (Opposite.op U) m).trans
    (hg (Opposite.op (AsSmall.up.obj ((proEtaleBaseChange f).obj U)))
      ((((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
            (Opposite.op (AsSmall.up.obj U)) m)))

private theorem inverse_restriction
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (N : SheafOfModules.{u} R) {U T : C} (e : U ≅ T)
    (x : N.val.obj (Opposite.op U)) :
    N.val.map e.hom.op (N.val.map e.inv.op x) = x := by
  exact congrArg (fun f : N.val.presheaf.obj (Opposite.op U) ⟶
    N.val.presheaf.obj (Opposite.op U) ↦ f.hom x) (N.val.presheaf.mapIso e.op).inv_hom_id

private theorem derived_formula
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
    H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (b.hom.app K) =
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

-- Comparing the nested derived and termwise functors unfolds several sheaf transports.
/-- The canonical composition isomorphism, including its K-flat representative formula.
The existential adjunctions have their units fixed sectionwise by the construction;
`d` is fixed by fibre-product pasting, `a` by conjugation, and `b` degree by degree.
Thus these witnesses express the ordinary canonical comparison, not arbitrary isomorphisms.
Source: Stacks, sites-cohomology.tex, Lemma 0D6D and Modules on Sites, Lemma 03D8
(auxiliary; not a blueprint node).
Proof: (1) On each test object the fibre-product pasting isomorphism identifies the two
module direct images. The induced coefficient identification makes it linear. The
module adjunctions have the displayed tensor units; form their composite using
`def-weil-pbc-composite-adjunction`. Apply `situation-conventions`
to obtain `a`. In inverse-image/tensor coordinates its forward map sends `m ⊗ r` to
`(m ⊗ 1) ⊗ r`; its inverse sends `(m ⊗ s) ⊗ r` to `m ⊗ c_h(s)r`. Balancing proves
the inverse identities and compatibility with restrictions and morphisms.
(2) Apply this comparison termwise to obtain `b`. All three module pullbacks are exact
by `prose-03-02`. Their termwise functors invert quasi-isomorphisms.
Use `lem-weil-pbc-localization-universal-property` to descend `b`, with the stated
factorization isomorphisms, to the unique compatible derived comparison `c`.
(3) Use `lem-pc-kflat-resolution` to represent an input by a K-flat complex with flat
terms. By `lem-weil-pbc-ringed-pullback-preserves-kflat`, its pullback along `k` remains
K-flat with flat terms, so the iterated pullback computes the iterated derived functor.
The factorization equation is exactly the class of the termwise comparison. For an
input already K-flat with flat terms use the identity resolution. No boundedness,
properness, or flatness of either scheme morphism enters. -/
theorem proEtaleRingDerivedPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h) :
    ∃ (adj_k : proEtaleRingModulePullback k R_V R_W c_k ⊣
          proEtaleRingModuleDirectImage k R_V R_W c_k)
      (adj_h : proEtaleRingModulePullback h R_W R_Z c_h ⊣
          proEtaleRingModuleDirectImage h R_W R_Z c_h)
      (adj_hk : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ⊣
          proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
      proEtaleRingModuleAdjunctionNormalized k R_V R_W c_k adj_k ∧
      proEtaleRingModuleAdjunctionNormalized h R_W R_Z c_h adj_h ∧
      proEtaleRingModuleAdjunctionNormalized (h ≫ k) R_V R_Z c_hk adj_hk ∧
      ∃ (d : proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k ≅
              proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
        (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
            (m : ((proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) ∧
        ∃ (a : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ≅
              proEtaleRingModulePullback k R_V R_W c_k ⋙
                proEtaleRingModulePullback h R_W R_Z c_h),
          conjugateIsoEquiv (adj_k.comp adj_h) adj_hk a = d ∧
          ∃ (b : (proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                (ComplexShape.up ℤ) ⋙
              (proEtaleRingModulePullback h R_W R_Z c_h).mapHomologicalComplex
                (ComplexShape.up ℤ)),
            (∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ) (n : ℤ),
              (b.hom.app K).f n = a.hom.app (K.X n)) ∧
            ∃ (c : proEtaleRingDerivedPullback (h ≫ k) R_V R_Z c_hk ≅
                proEtaleRingDerivedPullback k R_V R_W c_k ⋙
                  proEtaleRingDerivedPullback h R_W R_Z c_h),
              ∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ),
                CochainComplex.IsKFlatTensor K →
                (∀ n : ℤ,
                  SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R_V) (K.X n)) →
                CochainComplex.IsKFlatTensor
                  (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K) ∧
                (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R_W)
                  ((((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K).X n)) ∧
                (proEtaleRingDerivedPullbackFactors (h ≫ k) R_V R_Z c_hk).hom.app K ≫
                    DerivedCategory.Q.map (b.hom.app K) =
                  c.hom.app (DerivedCategory.Q.obj K) ≫
                    (proEtaleRingDerivedPullback h R_W R_Z c_h).map
                      ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
                    (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
                      (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K) := by
  classical
  let adjk := proEtaleRingModuleAdjunction k R_V R_W c_k
  let adjh := proEtaleRingModuleAdjunction h R_W R_Z c_h
  let adjhk := proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk
  refine ⟨adjk, adjh, adjhk, canonicalAdjunction_normalized k R_V R_W c_k,
    canonicalAdjunction_normalized h R_W R_Z c_h,
    canonicalAdjunction_normalized (h ≫ k) R_V R_Z c_hk, ?_⟩
  obtain ⟨d₀, _, hd₀, _⟩ :=
    proEtale_tensor_composition_unit h k R_V R_W R_Z c_k c_h c_hk hc_hk
  let d := d₀.symm
  refine ⟨d, ?_, (conjugateIsoEquiv (adjk.comp adjh) adjhk).symm d,
    (conjugateIsoEquiv (adjk.comp adjh) adjhk).apply_symm_apply d, ?_⟩
  · intro N U m
    have hx := hd₀ N U ((d₀.inv.app N).val.app (Opposite.op U) m)
    have hi := congrArg (fun z ↦ z.val.app (Opposite.op U) m) (d₀.inv_hom_id_app N)
    have hr := congrArg
      (fun x ↦ N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op x)
      (hx.symm.trans hi)
    exact (inverse_restriction N ((MorphismProperty.Over.pullbackComp h k).app U)
      ((d₀.inv.app N).val.app (Opposite.op U) m)).symm.trans
        (by simpa only [Iso.app_hom, Iso.app_inv, SheafOfModules.id_val,
          PresheafOfModules.id_app,
          ModuleCat.id_apply] using hr)
  · let a := (conjugateIsoEquiv (adjk.comp adjh) adjhk).symm d
    let F := proEtaleRingModulePullback k R_V R_W c_k
    let G := proEtaleRingModulePullback h R_W R_Z c_h
    let H := proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk
    let b := NatIso.mapHomologicalComplex a (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).symm
    refine ⟨b, ?_, ?_⟩
    · intro K n
      change a.hom.app (K.X n) ≫ 𝟙 _ = a.hom.app (K.X n)
      exact Category.comp_id _
    · let c := Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm
      refine ⟨c, ?_⟩
      intro K hK hflat
      obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists k R_V
      have : PreservesFiniteLimits (proEtaleSheafInverseImage k (Type (u + 1))) :=
        (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage k (𝟙 V)).2.2.2.1
      let T := I.modules ⋙ proEtaleRingExtension k R_V R_W c_k
      have hT : T = F := by dsimp only [T]; rw [hI]; rfl
      have : T.Additive := by rw [hT]; infer_instance
      have hobj (M) : T.obj M =
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c_k.hom (I.modules.obj M) := rfl
      have hmap : ∀ {M N} (f : M ⟶ N), T.map f = eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c_k.hom
            (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
        intro M N f
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      have hp₀ := SheafOfModules.isKFlat_ringedToposPullback
        (proEtaleSheafInverseImage k (Type (u + 1)))
        (proEtaleSheafDirectImage k (Type (u + 1)))
        (proEtaleSheafAdjunction k (Type (u + 1))) I c_k.hom T hobj hmap K hK hflat
      simp only [T, hI] at hp₀
      have hp := hp₀
      refine ⟨hp.1, hp.2, ?_⟩
      exact derived_formula F G H a b
        (fun K n ↦ by
          change a.hom.app (K.X n) ≫ 𝟙 _ = a.hom.app (K.X n)
          exact Category.comp_id _) K

end AlgebraicGeometry.Scheme
