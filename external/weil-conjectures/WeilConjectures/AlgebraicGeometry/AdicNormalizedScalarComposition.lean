/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition

/-! # Normalized scalar composition and uniqueness of adjoints

Source: Stacks Project, Tags 03CZ and 06YY.
(auxiliary; not a blueprint node).

The private transition calculations also compare ordinary scalar insertion with the
transpose of the reduced counit, for the explicit tensor successor square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] derivedExtension
attribute [local implicit_reducible] SheafOfModules.restrictScalars change
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  extend extendComparison
  SheafOfModules.unit PresheafOfModules.unit CategoryTheory.sheafCompose
variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
  {R S V : Sheaf T CommRingCat.{w}}

private theorem normalized_homEquiv (f : R ⟶ S) (adj : extend f ⊣ dres f)
    (ha : adj.unit = adicFiniteUnit f) (P : Cx R) (hP : P.IsKFlatTensor)
    (K : Cx S) (a : ((change f).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    adj.homEquiv ((Q R).obj P) ((Q S).obj K)
        ((extendComparison f).app P ≫ (Q S).map a) =
      (Q R).map (((adicFiniteAdjunction f).mapHomologicalComplex (.up ℤ)).homEquiv P K a) ≫
        (resFactors f).hom.app K := by
  have hu := (adicFiniteUnit_existsUnique f).exists.choose_spec P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
  change (adicFiniteUnit f).app ((Q R).obj P) ≫ _ = _ at hu
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc, ha, hu]
  have hn := (resFactors f).hom.naturality a
  change (Q R).map (((res f).mapHomologicalComplex (.up ℤ)).map a) ≫
      (resFactors f).hom.app K =
    (resFactors f).hom.app _ ≫ (dres f).map ((Q S).map a) at hn
  rw [Category.assoc, ← hn]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 2
  rw [Adjunction.homEquiv_unit]
  congr 1
  ext q
  simp only [Adjunction.mapHomologicalComplex_unit_app_f, adicFiniteAdjunction_unit]
  rfl

private theorem ordinary_comp_unit (f : R ⟶ S) (g : S ⟶ V) (P : Cx R) :
    adicFiniteOrdinaryUnitComplex f P ≫
      ((res f).mapHomologicalComplex (.up ℤ)).map
        (adicFiniteOrdinaryUnitComplex g (((change f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (NatIso.mapHomologicalComplex (adicFiniteResComp f g) (.up ℤ)).hom.app
        (((change g).mapHomologicalComplex (.up ℤ)).obj
          (((change f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ((res (f ≫ g)).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g)
          (.up ℤ)).hom.app P) = adicFiniteOrdinaryUnitComplex (f ≫ g) P := by
  have hr : adicFiniteResComp f g = resCompIso f g (f ≫ g) rfl := by
    apply (adicFiniteResComp_existsUnique f g).unique
    · exact (adicFiniteResComp_existsUnique f g).exists.choose_spec
    · intro M
      ext W x
      exact resCompIso_hom_apply f g (f ≫ g) rfl M W x
  rw [hr]
  apply HomologicalComplex.hom_ext
  intro q
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hu (B D : Sheaf T CommRingCat.{w}) (k : B ⟶ D) (N : Mod B) (z : N.val.obj W) :
      ((adicFiniteOrdinaryUnit k).app N).val.app W z = tensorSection k N W 1 z := by
    exact (congrArg (fun a ↦ a.hom.app W z)
      ((adicFiniteOrdinaryUnit_existsUnique k).exists.choose_spec N)).trans
        (adicFiniteInsertion_apply k N W z)
  change ((adicFiniteChangeComp f g).hom.app (P.X q)).val.app W
    (((resCompIso f g (f ≫ g) rfl).hom.app
        ((change g).obj ((change f).obj (P.X q)))).val.app W
      (((adicFiniteOrdinaryUnit g).app _).val.app W
        (((adicFiniteOrdinaryUnit f).app _).val.app W x))) =
      ((adicFiniteOrdinaryUnit (f ≫ g)).app _).val.app W x
  rw [hu, hu, resCompIso_hom_apply, hu]
  simpa only [adicFiniteChangeComp, map_one, mul_one] using
    (adicFiniteChangeComp_existsUnique f g).exists.choose_spec (P.X q) W 1 1 x

private theorem scalar_composition_representative
    (f : R ⟶ S) (g : S ⟶ V)
    (af : extend f ⊣ dres f) (ag : extend g ⊣ dres g)
    (ah : extend (f ≫ g) ⊣ dres (f ≫ g))
    (hf : af.unit = adicFiniteUnit f) (hg : ag.unit = adicFiniteUnit g)
    (hh : ah.unit = adicFiniteUnit (f ≫ g))
    (P : Cx R) (hP : P.IsKFlatTensor) :
    (((af.comp ag).ofNatIsoRight (adicFiniteDresComp f g)).leftAdjointUniq ah).hom.app
        ((Q R).obj P) ≫ (extendComparison (f ≫ g)).app P =
      (extend g).map ((extendComparison f).app P) ≫
        (extendComparison g).app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q V).map ((Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g)
          (.up ℤ)).hom.app P) := by
  let F := (change f).mapHomologicalComplex (.up ℤ)
  let G := (change g).mapHomologicalComplex (.up ℤ)
  let H := (change (f ≫ g)).mapHomologicalComplex (.up ℤ)
  let δ := (Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g) (.up ℤ)).hom.app P
  have hFP : CochainComplex.IsKFlatTensor (F.obj P) := by
    apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
    exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients f P
      (change f) (fun _ ↦ rfl) (by intros; simp only [eqToHom_refl,
        Category.id_comp, Category.comp_id]; rfl)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
  let a := ((af.comp ag).ofNatIsoRight (adicFiniteDresComp f g))
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change ah.homEquiv _ _ ((extendComparison (f ≫ g)).app P) = _
  have hn := normalized_homEquiv (f ≫ g) ah hh P hP (H.obj P) (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hn
  erw [hn]
  dsimp only [a]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change _ = af.homEquiv _ _ (ag.homEquiv _ _
    ((extend g).map ((extendComparison f).app P) ≫
      (extendComparison g).app (F.obj P) ≫ (Q V).map δ)) ≫ _
  rw [Adjunction.homEquiv_naturality_left]
  erw [normalized_homEquiv g ag hg (F.obj P) hFP (H.obj P) δ]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rw [normalized_homEquiv f af hf P hP]
  simp only [Category.assoc]
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  let := (siteRestrictScalars_exact g).1
  let := (siteRestrictScalars_exact g).2
  let := (siteRestrictScalars_exact (f ≫ g)).1
  let := (siteRestrictScalars_exact (f ≫ g)).2
  have hc := Functor.exactDerivedRestrictionComposition_inv_factors
    (res g) (res f) (res (f ≫ g)) (adicFiniteResComp f g) (H.obj P)
  change (resFactors f).hom.app
        (((res g).mapHomologicalComplex (.up ℤ)).obj (H.obj P)) ≫
      (dres f).map ((resFactors g).hom.app (H.obj P)) ≫
      (adicFiniteDresComp f g).hom.app ((Q V).obj (H.obj P)) =
    (Q R).map ((NatIso.mapHomologicalComplex (adicFiniteResComp f g) (.up ℤ)).hom.app
      (H.obj P)) ≫ (resFactors (f ≫ g)).hom.app (H.obj P) at hc
  erw [hc]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  congr 2
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
  have hu (B D : Sheaf T CommRingCat.{w}) (k : B ⟶ D) (N : Cx B) :
      ((adicFiniteAdjunction k).mapHomologicalComplex (.up ℤ)).unit.app N =
        adicFiniteOrdinaryUnitComplex k N := by
    ext q
    simp only [Adjunction.mapHomologicalComplex_unit_app_f, adicFiniteAdjunction_unit]
    rfl
  rw [hu, hu, hu]
  have hn := (NatIso.mapHomologicalComplex (adicFiniteResComp f g) (.up ℤ)).hom.naturality δ
  change ((res f).mapHomologicalComplex (.up ℤ)).map
      (((res g).mapHomologicalComplex (.up ℤ)).map δ) ≫ _ = _ at hn
  erw [hn]
  exact (ordinary_comp_unit f g P).symm

/-- The normalized scalar-composition comparison is the uniqueness comparison of left adjoints.
Source: Stacks Project, Tags 03CZ and 06YY.
(auxiliary; not a blueprint node).

Proof: the normalized derived unit computes the Hom equivalence on a K-flat representative
by the ordinary tensor adjunction followed by resFactors. Apply this twice, using
preservation of K-flatness by scalar extension and the compatibility of resFactors with
exact restriction composition. Ordinary balancing preserves insertion of one on pure
tensors, so these Hom equivalences identify the uniqueness comparison with the K-flat
normalization defining the chosen balancing. Its uniqueness gives the asserted equality. -/
theorem adicFiniteExtendComp_leftAdjointUniq (f : R ⟶ S) (g : S ⟶ V)
    (af : extend f ⊣ dres f) (ag : extend g ⊣ dres g)
    (ah : extend (f ≫ g) ⊣ dres (f ≫ g))
    (hf : af.unit = adicFiniteUnit f) (hg : ag.unit = adicFiniteUnit g)
    (hh : ah.unit = adicFiniteUnit (f ≫ g)) :
    ((af.comp ag).ofNatIsoRight (adicFiniteDresComp f g)).leftAdjointUniq ah =
      (adicFiniteExtendComp_existsUnique f g).exists.choose := by
  apply (adicFiniteExtendComp_existsUnique f g).unique
  · intro P hP
    exact scalar_composition_representative f g af ag ah hf hg hh P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
  · exact (adicFiniteExtendComp_existsUnique f g).exists.choose_spec

private theorem ordinary_transition_factor (f : R ⟶ S) (g : S ⟶ V) (M : Mod R) :
    (scalarTransition f g (f ≫ g) rfl).app M =
      (res f).map ((adicFiniteOrdinaryUnit g).app ((change f).obj M)) ≫
        (adicFiniteResComp f g).hom.app ((change g).obj ((change f).obj M)) ≫
        (res (f ≫ g)).map ((adicFiniteChangeComp f g).hom.app M) := by
  apply restrictedTensor_hom_ext f M
  intro W s x
  erw [scalarTransition_tmul]
  have hu := congrArg (fun a ↦ a.hom.app W (tensorSection f M W s x))
    ((adicFiniteOrdinaryUnit_existsUnique g).exists.choose_spec ((change f).obj M))
  have hr := congrArg (fun a ↦ a.hom.app W
      (tensorSection g ((change f).obj M) W 1 (tensorSection f M W s x)))
    ((adicFiniteResComp_existsUnique f g).exists.choose_spec
      ((change g).obj ((change f).obj M)))
  change _ = ((adicFiniteChangeComp f g).hom.app M).val.app W
    (((adicFiniteResComp f g).hom.app ((change g).obj ((change f).obj M))).val.app W
      (((adicFiniteOrdinaryUnit g).app _).val.app W (tensorSection f M W s x)))
  change ((adicFiniteOrdinaryUnit g).app ((change f).obj M)).val.app W
    (tensorSection f M W s x) = _ at hu
  erw [hu, adicFiniteInsertion_apply]
  change ((adicFiniteResComp f g).hom.app ((change g).obj ((change f).obj M))).val.app W
    (tensorSection g ((change f).obj M) W 1 (tensorSection f M W s x)) = _ at hr
  rw [hr]
  change tensorSection (f ≫ g) M W (g.hom.app W s) x =
    ((adicFiniteChangeComp f g).hom.app M).val.app W
      (tensorSection g ((change f).obj M) W 1 (tensorSection f M W s x))
  symm
  simpa only [adicFiniteChangeComp, one_mul] using
    (adicFiniteChangeComp_existsUnique f g).exists.choose_spec M W s 1 x

private theorem normalized_adjoint_step (f : R ⟶ S) (g : S ⟶ V)
    (af : extend f ⊣ dres f) (ag : extend g ⊣ dres g)
    (ah : extend (f ≫ g) ⊣ dres (f ≫ g))
    (hf : af.unit = adicFiniteUnit f) (hg : ag.unit = adicFiniteUnit g)
    (hh : ah.unit = adicFiniteUnit (f ≫ g)) (M : D R) :
    let e := (adicFiniteExtendComp_existsUnique f g).exists.choose
    ah.homEquiv _ _
        (e.inv.app ((dres f).obj ((extend f).obj M)) ≫
          (extend g).map (af.counit.app ((extend f).obj M)) ≫ e.hom.app M) =
      (dres f).map ((adicFiniteUnit g).app ((extend f).obj M)) ≫
        (adicFiniteDresComp f g).hom.app ((extend g).obj ((extend f).obj M)) ≫
        (dres (f ≫ g)).map (e.hom.app M) := by
  dsimp only
  rw [← adicFiniteExtendComp_leftAdjointUniq f g af ag ah hf hg hh]
  let a := (af.comp ag).ofNatIsoRight (adicFiniteDresComp f g)
  let e := a.leftAdjointUniq ah
  have ht {Z : D R} {K : D V} (k : (extend g).obj ((extend f).obj Z) ⟶ K) :
      ah.homEquiv Z K (e.inv.app Z ≫ k) = a.homEquiv Z K k := by
    have hu : a.unit.app Z ≫ (dres (f ≫ g)).map (e.hom.app Z) = ah.unit.app Z :=
      Adjunction.unit_leftAdjointUniq_hom_app a ah Z
    rw [Adjunction.homEquiv_unit, ← hu, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [ht]
  dsimp only [a]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change af.homEquiv _ _ (ag.homEquiv _ _
    ((extend g).map (af.counit.app ((extend f).obj M)) ≫ e.hom.app M)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hε : af.homEquiv _ _ (af.counit.app ((extend f).obj M)) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id]
    exact (af.homEquiv _ _).apply_symm_apply _
  rw [hε, Category.id_comp, Adjunction.homEquiv_unit, hg, CategoryTheory.Functor.map_comp]
  have hn := (adicFiniteDresComp f g).hom.naturality (e.hom.app M)
  change (dres f).map ((dres g).map (e.hom.app M)) ≫ _ = _ at hn
  rw [Category.assoc, hn]
  rfl

private theorem scalar_transition_comparison (f : R ⟶ S) (g : S ⟶ V)
    (P : Cx R) (hP : P.IsKFlatTensor) :
    let F := (change f).mapHomologicalComplex (.up ℤ)
    let H := (change (f ≫ g)).mapHomologicalComplex (.up ℤ)
    let e := (adicFiniteExtendComp_existsUnique f g).exists.choose
    let p := (extendComparison f).app P
    let r := (extendComparison (f ≫ g)).app P
    letI : IsIso p := (derivedExtension f).computation P hP
    letI : IsIso r := (derivedExtension (f ≫ g)).computation P hP
    (Q R).map ((NatTrans.mapHomologicalComplex (scalarTransition f g (f ≫ g) rfl)
      (.up ℤ)).app P) ≫ (resFactors (f ≫ g)).hom.app (H.obj P) ≫
        (dres (f ≫ g)).map (inv r) =
    (resFactors f).hom.app (F.obj P) ≫ (dres f).map (inv p) ≫
      (dres f).map ((adicFiniteUnit g).app ((extend f).obj ((Q R).obj P))) ≫
      (adicFiniteDresComp f g).hom.app
        ((extend g).obj ((extend f).obj ((Q R).obj P))) ≫
      (dres (f ≫ g)).map (e.hom.app ((Q R).obj P)) := by
  dsimp only
  let F := (change f).mapHomologicalComplex (.up ℤ)
  let G := (change g).mapHomologicalComplex (.up ℤ)
  let H := (change (f ≫ g)).mapHomologicalComplex (.up ℤ)
  let p := (extendComparison f).app P
  let q := (extendComparison g).app (F.obj P)
  let r := (extendComparison (f ≫ g)).app P
  let e := (adicFiniteExtendComp_existsUnique f g).exists.choose
  let c := adicFiniteDresComp f g
  let δ := (Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g) (.up ℤ)).hom.app P
  have hp : IsIso p := (derivedExtension f).computation P hP
  have hr : IsIso r := (derivedExtension (f ≫ g)).computation P hP
  have hFP : CochainComplex.IsKFlatTensor (F.obj P) := by
    apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
    exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients f P
      (change f) (fun _ ↦ rfl) (by intros; simp only [eqToHom_refl,
        Category.id_comp, Category.comp_id]; rfl)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
  have he : e.hom.app ((Q R).obj P) ≫ r =
      (extend g).map p ≫ q ≫ (Q V).map δ :=
    (adicFiniteExtendComp_existsUnique f g).exists.choose_spec P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
  have hu := (adicFiniteUnit_existsUnique g).exists.choose_spec (F.obj P)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr hFP)
  change (adicFiniteUnit g).app ((Q S).obj (F.obj P)) ≫ (dres g).map q =
    (Q S).map (adicFiniteOrdinaryUnitComplex g (F.obj P)) ≫
      (resFactors g).hom.app (G.obj (F.obj P)) at hu
  have ho : (NatTrans.mapHomologicalComplex (scalarTransition f g (f ≫ g) rfl)
      (.up ℤ)).app P =
    ((res f).mapHomologicalComplex (.up ℤ)).map (adicFiniteOrdinaryUnitComplex g (F.obj P)) ≫
      (NatIso.mapHomologicalComplex (adicFiniteResComp f g) (.up ℤ)).hom.app
        (G.obj (F.obj P)) ≫
      ((res (f ≫ g)).mapHomologicalComplex (.up ℤ)).map δ := by
    apply HomologicalComplex.hom_ext
    intro i
    exact ordinary_transition_factor f g (P.X i)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  let := (siteRestrictScalars_exact g).1
  let := (siteRestrictScalars_exact g).2
  let := (siteRestrictScalars_exact (f ≫ g)).1
  let := (siteRestrictScalars_exact (f ≫ g)).2
  have hc := Functor.exactDerivedRestrictionComposition_inv_factors
    (res g) (res f) (res (f ≫ g)) (adicFiniteResComp f g) (G.obj (F.obj P))
  change (resFactors f).hom.app
        (((res g).mapHomologicalComplex (.up ℤ)).obj (G.obj (F.obj P))) ≫
      (dres f).map ((resFactors g).hom.app (G.obj (F.obj P))) ≫
      c.hom.app ((Q V).obj (G.obj (F.obj P))) =
    (Q R).map ((NatIso.mapHomologicalComplex (adicFiniteResComp f g) (.up ℤ)).hom.app
      (G.obj (F.obj P))) ≫ (resFactors (f ≫ g)).hom.app (G.obj (F.obj P)) at hc
  have hcn := c.hom.naturality ((extend g).map p)
  change (dres f).map ((dres g).map ((extend g).map p)) ≫
      c.hom.app ((extend g).obj ((Q S).obj (F.obj P))) =
    c.hom.app ((extend g).obj ((extend f).obj ((Q R).obj P))) ≫
      (dres (f ≫ g)).map ((extend g).map p) at hcn
  have hun := (adicFiniteUnit g).naturality p
  change p ≫ (adicFiniteUnit g).app ((Q S).obj (F.obj P)) =
    (adicFiniteUnit g).app ((extend f).obj ((Q R).obj P)) ≫
      (dres g).map ((extend g).map p) at hun
  apply (cancel_mono ((dres (f ≫ g)).map r)).mp
  simp only [Category.assoc]
  erw [← (dres (f ≫ g)).map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← (dres (f ≫ g)).map_comp, he]
  simp only [CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% hcn]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [← hun]
  erw [IsIso.inv_hom_id_assoc]
  have hcq := c.hom.naturality q
  change (dres f).map ((dres g).map q) ≫
      c.hom.app ((Q V).obj (G.obj (F.obj P))) =
    c.hom.app ((extend g).obj ((Q S).obj (F.obj P))) ≫ (dres (f ≫ g)).map q at hcq
  rw [← reassoc_of% hcq, ← CategoryTheory.Functor.map_comp_assoc, hu]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [← (resFactors f).hom.naturality_assoc]
  erw [reassoc_of% hc]
  erw [← (resFactors (f ≫ g)).hom.naturality δ]
  simp only [CategoryTheory.Functor.comp_map]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Category.assoc, ← ho]

private theorem canonical_step_naturality (f : R ⟶ S) (g : S ⟶ V)
    {M N : D R} (a : M ⟶ N) :
    let e := (adicFiniteExtendComp_existsUnique f g).exists.choose
    (dres f).map ((extend f).map a) ≫
        (dres f).map ((adicFiniteUnit g).app ((extend f).obj N)) ≫
        (adicFiniteDresComp f g).hom.app ((extend g).obj ((extend f).obj N)) ≫
        (dres (f ≫ g)).map (e.hom.app N) =
      (dres f).map ((adicFiniteUnit g).app ((extend f).obj M)) ≫
        (adicFiniteDresComp f g).hom.app ((extend g).obj ((extend f).obj M)) ≫
        (dres (f ≫ g)).map (e.hom.app M) ≫ (dres (f ≫ g)).map ((extend (f ≫ g)).map a) := by
  dsimp only
  let e := (adicFiniteExtendComp_existsUnique f g).exists.choose
  have hu := (adicFiniteUnit g).naturality ((extend f).map a)
  change (extend f).map a ≫ (adicFiniteUnit g).app ((extend f).obj N) =
    (adicFiniteUnit g).app ((extend f).obj M) ≫
      (dres g).map ((extend g).map ((extend f).map a)) at hu
  have hc := (adicFiniteDresComp f g).hom.naturality ((extend g).map ((extend f).map a))
  change (dres f).map ((dres g).map ((extend g).map ((extend f).map a))) ≫ _ = _ at hc
  have he := e.hom.naturality a
  change (extend g).map ((extend f).map a) ≫ e.hom.app N =
    e.hom.app M ≫ (extend (f ≫ g)).map a at he
  rw [← CategoryTheory.Functor.map_comp_assoc, hu]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  rw [← CategoryTheory.Functor.map_comp, he]
  rw [CategoryTheory.Functor.map_comp]

private theorem scalar_transition_adjoint (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V)
    (eh : h = f ≫ g) (af : extend f ⊣ dres f) (ag : extend g ⊣ dres g)
    (ah : extend h ⊣ dres h)
    (hf : af.unit = adicFiniteUnit f) (hg : ag.unit = adicFiniteUnit g)
    (hh : ah.unit = adicFiniteUnit h)
    (P : Cx R) (hP : P.IsKFlatTensor) (M : D R) (eP : (Q R).obj P ≅ M) :
    let F := (change f).mapHomologicalComplex (.up ℤ)
    let H := (change h).mapHomologicalComplex (.up ℤ)
    let e := adicFiniteExtendComp f g h eh
    letI : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
    letI : IsIso ((extendComparison h).app P) := (derivedExtension h).computation P hP
    (Q R).map ((NatTrans.mapHomologicalComplex (scalarTransition f g h eh.symm)
      (.up ℤ)).app P) ≫ (resFactors h).hom.app (H.obj P) ≫
        (dres h).map (inv ((extendComparison h).app P)) ≫
        (dres h).map ((extend h).map eP.hom) =
    (resFactors f).hom.app (F.obj P) ≫
      (dres f).map (inv ((extendComparison f).app P)) ≫
      (dres f).map ((extend f).map eP.hom) ≫
      ah.homEquiv _ _ (e.inv.app ((dres f).obj ((extend f).obj M)) ≫
        (extend g).map (af.counit.app ((extend f).obj M)) ≫ e.hom.app M) := by
  subst h
  simp only [adicFiniteExtendComp, Iso.trans_hom, Iso.trans_inv, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp]
  have hpf : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  have hph : IsIso ((extendComparison (f ≫ g)).app P) :=
    (derivedExtension (f ≫ g)).computation P hP
  rw [normalized_adjoint_step f g af ag ah hf hg hh M]
  rw [reassoc_of% (scalar_transition_comparison f g P hP)]
  rw [← canonical_step_naturality f g eP.hom]

end AlgebraicGeometry.Scheme
