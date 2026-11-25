/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.Topology.Sheaves.CechComparison
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechFlat

/-!
# The Čech resolution of a sheaf of modules

Let `U : ι → X.Opens` be a finite open cover of a scheme `X` and `ℱ` an `𝒪_X`-module. Write
`j_V : V ⟶ X` for the inclusion of an open. The sheafified Čech complex `Č(U, ℱ)` has in
degree `k` the module `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, where
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)`; it is Mathlib's Čech complex
(`CategoryTheory.cechComplexFunctor`) of the presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules.

## Main results

- `AlgebraicGeometry.Scheme.Modules.cechResolution`: the complex `Č(U, ℱ)`, and its
  augmentation `AlgebraicGeometry.Scheme.Modules.cechResolutionι : ℱ ⟶ Č(U, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.quasiIso_cechResolutionι`: the augmented Čech complex
  `0 ⟶ ℱ ⟶ Č⁰(U, ℱ) ⟶ Č¹(U, ℱ) ⟶ ⋯` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {Z : C} {K L : CochainComplex C ℕ}
  (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι] [∀ n, Injective (L.X n)]

/-- An auxiliary definition for `CochainComplex.homotopyZeroOfQuasiIso`. -/
noncomputable def homotopyZeroOfQuasiIsoZero (φ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.X 1 ⟶ L.X 0 :=
  (exact₀_of_quasiIso_single₀ ι).descToInjective (φ.f 0) comm

@[reassoc (attr := simp)]
lemma comp_homotopyZeroOfQuasiIsoZero (φ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 0 1 ≫ homotopyZeroOfQuasiIsoZero ι φ comm = φ.f 0 :=
  (exact₀_of_quasiIso_single₀ ι).comp_descToInjective _ _

/-- An auxiliary definition for `CochainComplex.homotopyZeroOfQuasiIso`. -/
noncomputable def homotopyZeroOfQuasiIsoOne (φ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.X 2 ⟶ L.X 1 :=
  (exact_succ_of_quasiIso_single₀ ι 0).descToInjective
    (φ.f 1 - homotopyZeroOfQuasiIsoZero ι φ comm ≫ L.d 0 1)
    (by rw [Preadditive.comp_sub, comp_homotopyZeroOfQuasiIsoZero_assoc, φ.comm, sub_self])

@[reassoc (attr := simp)]
lemma comp_homotopyZeroOfQuasiIsoOne (φ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 1 2 ≫ homotopyZeroOfQuasiIsoOne ι φ comm =
      φ.f 1 - homotopyZeroOfQuasiIsoZero ι φ comm ≫ L.d 0 1 :=
  (exact_succ_of_quasiIso_single₀ ι 0).comp_descToInjective _ _

/-- An auxiliary definition for `CochainComplex.homotopyZeroOfQuasiIso`. -/
noncomputable def homotopyZeroOfQuasiIsoSucc (φ : K ⟶ L) (n : ℕ) (g : K.X (n + 1) ⟶ L.X n)
    (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.X (n + 3) ⟶ L.X (n + 2) :=
  (exact_succ_of_quasiIso_single₀ ι (n + 1)).descToInjective (φ.f (n + 2) - g' ≫ L.d _ _) (by
    dsimp
    rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
      Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero, add_zero,
      sub_self])

@[reassoc (attr := simp)]
lemma comp_homotopyZeroOfQuasiIsoSucc (φ : K ⟶ L) (n : ℕ) (g : K.X (n + 1) ⟶ L.X n)
    (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroOfQuasiIsoSucc ι φ n g g' w =
      φ.f (n + 2) - g' ≫ L.d _ _ :=
  (exact_succ_of_quasiIso_single₀ ι (n + 1)).comp_descToInjective _ _

/-- A morphism from a resolution `ι : single₀ Z ⟶ K` to a complex of injective objects which
vanishes on `Z` is homotopic to zero. This generalises `InjectiveResolution.descHomotopyZero`,
where the source is an injective resolution and the target is exact. -/
noncomputable def homotopyZeroOfQuasiIso (φ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    Homotopy φ 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroOfQuasiIsoZero ι φ comm) (by simp)
    (homotopyZeroOfQuasiIsoOne ι φ comm) (by simp) (fun n ⟨g, g', w⟩ ↦
      ⟨homotopyZeroOfQuasiIsoSucc ι φ n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two morphisms from a resolution `ι : single₀ Z ⟶ K` to a complex of injective objects which
agree on `Z` are homotopic. -/
noncomputable def homotopyOfQuasiIso (φ ψ : K ⟶ L) (comm : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ ψ.f 0) :
    Homotopy φ ψ :=
  Homotopy.equivSubZero.symm
    (homotopyZeroOfQuasiIso ι (φ - ψ) (by simp [Preadditive.comp_sub, comm]))

end CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section ExtendRestrict

lemma ι_image_preimage (V T : X.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ T = V ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma ι_image_preimage_mono {V W : X.Opens} (h : W ≤ V) (T : X.Opens) :
    W.ι ''ᵁ W.ι ⁻¹ᵁ T ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ T := by
  rw [ι_image_preimage, ι_image_preimage]
  exact inf_le_inf_right T h

/-- The functor `ℱ ↦ j_* (ℱ|_V)` for the inclusion `j : V ⟶ X` of an open `V`. -/
noncomputable abbrev extendRestrictFunctor (V : X.Opens) : X.Modules ⥤ X.Modules :=
  restrictFunctor V.ι ⋙ pushforward V.ι

/-- The restriction `j_{V,*} (ℱ|_V) ⟶ j_{W,*} (ℱ|_W)` for opens `W ≤ V`. -/
noncomputable def extendRestrictMap {V W : X.Opens} (h : W ≤ V) :
    extendRestrictFunctor V ⟶ extendRestrictFunctor W :=
  let a : restrictFunctor V.ι ⋙ pushforward V.ι ⟶
      (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
        (pushforward (X.homOfLE h) ⋙ pushforward V.ι) :=
    Functor.whiskerLeft (restrictFunctor V.ι)
      (Functor.whiskerRight (restrictAdjunction (X.homOfLE h)).unit (pushforward V.ι))
  let b : (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
      (pushforward (X.homOfLE h) ⋙ pushforward V.ι) ⟶
        restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) :=
    (restrictFunctorComp (X.homOfLE h) V.ι).inv ◫ (pushforwardComp (X.homOfLE h) V.ι).hom
  let c : restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) ⟶
      restrictFunctor W.ι ⋙ pushforward W.ι :=
    (restrictFunctorCongr (X.homOfLE_ι h)).hom ◫ (pushforwardCongr (X.homOfLE_ι h)).hom
  a ≫ b ≫ c

lemma extendRestrictMap_app_app {V W : X.Opens} (h : W ≤ V) (ℱ : X.Modules) (T : X.Opens) :
    ((extendRestrictMap h).app ℱ).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono h T)).op :
        Γ(ℱ, V.ι ''ᵁ V.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.ι ''ᵁ W.ι ⁻¹ᵁ T)) := by
  simp only [extendRestrictMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.hcomp_app, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app, restrictFunctorComp_inv_app_app,
    pushforwardCongr_hom_app_app, restrictFunctorCongr_hom_app_app, restrict_map,
    ← Functor.map_comp]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end ExtendRestrict

section ExactSections

/-- The sections over `W` of an `𝒪_X`-module, as an abelian group. -/
noncomputable abbrev sectionsAb (W : X.Opens) : X.Modules ⥤ Ab.{u} :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op W)

instance (W : X.Opens) : (sectionsAb W).Additive where
  map_add := rfl

/-- **Exactness from sections over small opens.** A short complex of `𝒪_X`-modules is exact if
every point has arbitrarily small open neighbourhoods over which its sections are exact. -/
theorem exact_of_exact_sectionsAb (S : ShortComplex X.Modules)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (S.map (sectionsAb W)).Exact) : S.Exact := by
  rw [exact_iff_stalkFunctor]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.presheaf a
  have ha' : S.X₃.presheaf.germ V x hxV (S.g.app V s) = S.X₃.presheaf.germ V x hxV 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV S.g.mapPresheaf s).symm.trans ha
  obtain ⟨V', hxV', i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ ha'
  rw [map_zero] at e
  obtain ⟨W, hxW, hWV', hW⟩ := h x V' hxV'
  rw [ShortComplex.ab_exact_iff] at hW
  obtain ⟨t, ht⟩ := hW (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) (by
    change S.g.app W (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) = 0
    rw [Hom.app_presheaf_map, show S.X₃.presheaf.map (homOfLE (hWV'.trans i₁.le)).op =
      S.X₃.presheaf.map i₁.op ≫ S.X₃.presheaf.map (homOfLE hWV').op by
        rw [← Functor.map_comp]; rfl, ConcreteCategory.comp_apply, e, map_zero])
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor Ab x).map S.f.mapPresheaf _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change S.X₂.presheaf.germ W x hxW (S.f.app W t) = _
  rw [show S.f.app W t = _ from ht, TopCat.Presheaf.germ_res_apply]

/-- **Exactness from sections over small opens**, for homological complexes. -/
theorem exactAt_of_exactAt_sectionsAb {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (i : ι)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (((sectionsAb W).mapHomologicalComplex c).obj K).ExactAt i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_exact_sectionsAb _ fun x V hxV ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hxV
  exact ⟨W, hxW, hWV, (HomologicalComplex.exactAt_iff _ _).mp hW⟩

end ExactSections

section Complex

variable (X) in
/-- The presheaf of functors `V ↦ (ℱ ↦ j_{V,*} (ℱ|_V))` on the opens of `X`. -/
noncomputable def extendRestrictPresheaf : X.Opensᵒᵖ ⥤ X.Modules ⥤ X.Modules where
  obj V := extendRestrictFunctor V.unop
  map i := extendRestrictMap (leOfHom i.unop)
  map_id V := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [extendRestrictMap_app_app]
    exact ℱ.presheaf.map_id _)
  map_comp i j := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [NatTrans.comp_app, Hom.comp_app, extendRestrictMap_app_app, extendRestrictMap_app_app,
      extendRestrictMap_app_app, ← Functor.map_comp]
    rfl)

/-- The presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules. -/
noncomputable abbrev cechPresheaf (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ X.Modules :=
  (extendRestrictPresheaf X).flip.obj ℱ

lemma cechPresheaf_map_app (ℱ : X.Modules) {V W : X.Opensᵒᵖ} (i : V ⟶ W) (T : X.Opens) :
    ((cechPresheaf ℱ).map i).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono (leOfHom i.unop) T)).op :
        Γ(ℱ, V.unop.ι ''ᵁ V.unop.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.unop.ι ''ᵁ W.unop.ι ⁻¹ᵁ T)) :=
  extendRestrictMap_app_app _ ℱ T

variable {ι : Type u} (U : ι → X.Opens)

/-- The **sheafified Čech complex** `Č(U, ℱ)` of an `𝒪_X`-module `ℱ` for a family `U` of opens,
as a functor of `ℱ`: in degree `k` it is `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, with
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)` and the alternating sum of the restrictions as differential. -/
noncomputable def cechResolutionFunctor : X.Modules ⥤ CochainComplex X.Modules ℕ :=
  (extendRestrictPresheaf X).flip ⋙ cechComplexFunctor U

/-- The sheafified Čech complex `Č(U, ℱ)`. -/
noncomputable abbrev cechResolution (ℱ : X.Modules) : CochainComplex X.Modules ℕ :=
  (cechResolutionFunctor U).obj ℱ

/-- The augmentation `ℱ ⟶ Č⁰(U, ℱ) = ∏ᵢ j_{U i,*} (ℱ|_{U i})`, the product of the units of the
restrictions. -/
noncomputable def cechResolutionAugmentation (ℱ : X.Modules) : ℱ ⟶ (cechResolution U ℱ).X 0 :=
  (restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ ≫
    cechAugmentation U isTerminalTop (cechPresheaf ℱ)

@[reassoc (attr := simp)]
lemma cechResolutionAugmentation_d (ℱ : X.Modules) :
    cechResolutionAugmentation U ℱ ≫ (cechResolution U ℱ).d 0 1 = 0 := by
  rw [cechResolutionAugmentation, Category.assoc]
  erw [cechAugmentation_d]
  rw [comp_zero]

/-- The augmentation `ℱ ⟶ Č(U, ℱ)`, as a morphism of complexes from `ℱ` in degree `0`. -/
noncomputable def cechResolutionι (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ cechResolution U ℱ :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨cechResolutionAugmentation U ℱ, cechResolutionAugmentation_d U ℱ⟩

@[simp]
lemma cechResolutionι_f_zero (ℱ : X.Modules) :
    (cechResolutionι U ℱ).f 0 = cechResolutionAugmentation U ℱ := by
  simp [cechResolutionι, CochainComplex.fromSingle₀Equiv]

end Complex

section Exactness

/-- A complex `K` augmented by `ε : Z ⟶ K⁰` is a resolution of `Z` as soon as `ε` is a
monomorphism, `Z ⟶ K⁰ ⟶ K¹` is exact and `K` is exact in positive degrees. -/
lemma quasiIso_fromSingle₀Equiv_symm {C : Type*} [Category* C] [Abelian C] {Z : C}
    {K : CochainComplex C ℕ} (ε : Z ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)
    (h₀ : (ShortComplex.mk ε (K.d 0 1) hε).Exact) [Mono ε] (hK : ∀ n, K.ExactAt (n + 1)) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K Z).symm ⟨ε, hε⟩) := ⟨fun n ↦ by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h₀, by dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [CochainComplex.fromSingle₀Equiv]) (by simp)
    all_goals first | rfl | exact HomologicalComplex.shape _ _ _ (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact hK n
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

variable {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)

/-- The sections over `W` of an `𝒪_X`-module, as a module over `Γ(X, W)`. -/
noncomputable abbrev sectionsModuleFunctor (W : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op W)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op W)

instance (W : X.Opens) : (sectionsModuleFunctor W).Additive where
  map_add := rfl

instance (W : X.Opens) (J : Type u) :
    PreservesLimitsOfShape (Discrete J) (sectionsModuleFunctor W) :=
  inferInstanceAs
    (PreservesLimitsOfShape (Discrete J) (SheafOfModules.evaluation X.ringCatSheaf (op W)))

/-- The sections over `W` of the Čech complex: the Čech complex of the presheaf
`V ↦ Γ(W, j_{V,*} (ℱ|_V))`, with explicit cochains. -/
noncomputable def sectionsCechResolutionIso (W : X.Opens) :
    ((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ) ≅
      (TopCat.Presheaf.cechComplex U).obj
        (cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u}) :=
  ((forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex _).mapIso
      (cechComplexFunctorMapIso U (sectionsModuleFunctor W) (cechPresheaf ℱ)) ≪≫
    TopCat.Presheaf.cechComplexFunctorIso U (cechPresheaf ℱ ⋙ sectionsModuleFunctor W)

/-- Over an open `W` contained in a member of the family, the sections of the Čech complex are
exact in positive degrees. -/
lemma exactAt_sectionsAb_cechResolution {W : X.Opens} {j : ι} (hW : W ≤ U j) (n : ℕ) :
    (((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ)).ExactAt (n + 1) := by
  refine (ShortComplex.exact_iff_of_iso ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).mapIso
    (sectionsCechResolutionIso U ℱ W))).mpr ?_
  refine TopCat.Presheaf.exactAt_cechComplex_of_bijective U _ (j := j) (fun k y ↦ ?_) n
  have hle : ((⨅ l, U (y l)) ⊓ U j).ι ''ᵁ ((⨅ l, U (y l)) ⊓ U j).ι ⁻¹ᵁ W ≥
      (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W := by
    rw [ι_image_preimage, ι_image_preimage, inf_assoc, inf_eq_right.mpr hW]
  have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_mono
    (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)) hle
  have e : (cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u}).map
      (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op =
      ℱ.presheaf.map (homOfLE (ι_image_preimage_mono
        (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)).op :=
    cechPresheaf_map_app ℱ (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op W
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

/-- Restricting twice is restricting once. -/
lemma presheaf_map_map_apply_eq (M : X.Modules) {A B C : X.Opensᵒᵖ} (i : A ⟶ B) (j : B ⟶ C)
    (k : A ⟶ C) (x : M.presheaf.obj A) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map k x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma ι_image_preimage_le_self (V W : X.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := by
  rw [ι_image_preimage]
  exact inf_le_right

/-- The augmentation of the Čech complex on sections, in explicit cochains: the restrictions. -/
lemma sectionsCechResolutionIso_augmentation (W : X.Opens) (s : Γ(ℱ, W)) (y : Fin 1 → ι) :
    (sectionsCechResolutionIso U ℱ W).hom.f 0 ((cechResolutionAugmentation U ℱ).app W s) y =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_le_self (⨅ l, U (y l)) W)).op :
        Γ(ℱ, W) ⟶ Γ(ℱ, (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W)) s := by
  let G := sectionsModuleFunctor (X := X) W
  let P := cechPresheaf ℱ
  have h1 : (G.map (cechResolutionAugmentation U ℱ) ≫
      (cechComplexFunctorMapIso U G P).hom.f 0) =
      G.map ((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ) ≫
        cechAugmentation U isTerminalTop (P ⋙ G) := by
    rw [cechResolutionAugmentation, G.map_comp, Category.assoc, map_cechAugmentation_comp]
  have h2 := congrArg (fun φ ↦ TopCat.Presheaf.cechComplexFunctorXAddEquiv U (P ⋙ G) 0
    (φ s) y) h1
  dsimp only at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · rfl
  have h3 := ConcreteCategory.congr_hom (cechAugmentation_π U isTerminalTop (P ⋙ G) y)
    (G.map ((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ) s)
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply, ConcreteCategory.comp_apply,
    TopCat.Presheaf.cechComplexFunctorπ]
  erw [h3]
  have key : ∀ {A B : X.Opensᵒᵖ} (i₁ : op ⊤ ⟶ A) (i₂ : A ⟶ B)
      (h : B.unop.ι ''ᵁ B.unop.ι ⁻¹ᵁ W ≤ W),
      ((cechPresheaf ℱ).map i₂).app W (((cechPresheaf ℱ).map i₁).app W
        (((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ).app W s)) =
      (ℱ.presheaf.map (homOfLE h).op : Γ(ℱ, W) ⟶ Γ(ℱ, B.unop.ι ''ᵁ B.unop.ι ⁻¹ᵁ W)) s := by
    intro A B i₁ i₂ h
    rw [cechPresheaf_map_app, cechPresheaf_map_app, restrictAdjunction_unit_app_app]
    exact (congrArg _ (presheaf_map_map_apply_eq ℱ _ _
      (homOfLE (ι_image_preimage_le_self A.unop W)).op s)).trans
      (presheaf_map_map_apply_eq ℱ _ _ (homOfLE h).op s)
  exact key (A := op (∏ᶜ fun l ↦ U (y l))) (isTerminalTop.from _).op
    (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op (ι_image_preimage_le_self _ W)

lemma bijective_sectionsCechResolutionIso_hom_f (W : X.Opens) (k : ℕ) :
    Function.Bijective ((sectionsCechResolutionIso U ℱ W).hom.f k) :=
  ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.eval _ _ k).mapIso (sectionsCechResolutionIso U ℱ W)).hom

lemma sectionsCechResolutionIso_d (W : X.Opens) (k : ℕ) (x : Γ((cechResolution U ℱ).X k, W)) :
    (sectionsCechResolutionIso U ℱ W).hom.f (k + 1) (((cechResolution U ℱ).d k (k + 1)).app W x) =
      ((TopCat.Presheaf.cechComplex U).obj
        (cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u})).d k (k + 1)
        ((sectionsCechResolutionIso U ℱ W).hom.f k x) :=
  (ConcreteCategory.congr_hom ((sectionsCechResolutionIso U ℱ W).hom.comm k (k + 1)) x).symm

/-- Over an open `W` contained in a member `U j` of the family, the augmented Čech complex is
exact on sections in degree `0`, and the augmentation is injective on sections. -/
lemma injective_and_exact_sectionsAb_cechResolution_zero {W : X.Opens} {j : ι} (hW : W ≤ U j) :
    Function.Injective ((cechResolutionAugmentation U ℱ).app W) ∧
      ((ShortComplex.mk _ _ (cechResolutionAugmentation_d U ℱ)).map (sectionsAb W)).Exact := by
  set E := sectionsCechResolutionIso U ℱ W
  let Q := cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u}
  have hQ {A B : X.Opens} (h : A ≤ B) (x : Q.obj (op B)) :
      Q.map (homOfLE h).op x = (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono h W)).op :
        Γ(ℱ, B.ι ''ᵁ B.ι ⁻¹ᵁ W) ⟶ Γ(ℱ, A.ι ''ᵁ A.ι ⁻¹ᵁ W)) x :=
    ConcreteCategory.congr_hom (cechPresheaf_map_app ℱ (homOfLE h).op W) x
  -- the open `(⨅ l, U (y l)) ⊓ W` for the constant tuple `j`
  have hj : (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ''ᵁ
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ⁻¹ᵁ W = W := by
    rw [ι_image_preimage, iInf_const, inf_eq_right.mpr hW]
  have hinj : Function.Injective (ℱ.presheaf.map (homOfLE (ι_image_preimage_le_self
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)) W)).op) := by
    have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_le_self
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)) W)) hj.ge
    exact (ConcreteCategory.bijective_of_isIso _).1
  refine ⟨fun s t hst ↦ hinj ?_, ?_⟩
  · have h := congrArg (fun x ↦ E.hom.f 0 x (fun _ ↦ j)) hst
    simp only [E, sectionsCechResolutionIso_augmentation] at h
    exact h
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  change ((cechResolution U ℱ).d 0 1).app W x = 0 at hx
  have hc : ((TopCat.Presheaf.cechComplex U).obj Q).d 0 1 (E.hom.f 0 x) = 0 := by
    have := sectionsCechResolutionIso_d (U := U) (ℱ := ℱ) W 0 x
    rw [hx, map_zero] at this
    exact this.symm
  set c := E.hom.f 0 x with hc_def
  let s : Γ(ℱ, W) := (ℱ.presheaf.map (homOfLE hj.ge).op :
    Γ(ℱ, (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ''ᵁ (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ⁻¹ᵁ W) ⟶
      Γ(ℱ, W)) (c (fun _ ↦ j))
  refine ⟨s, (bijective_sectionsCechResolutionIso_hom_f (U := U) (ℱ := ℱ) W 0).1 ?_⟩
  change E.hom.f 0 ((cechResolutionAugmentation U ℱ).app W s) = c
  funext y
  rw [sectionsCechResolutionIso_augmentation]
  -- the cocycle condition at the tuple `(y 0, j)`
  let z : Fin 2 → ι := Fin.cons (y 0) (fun _ ↦ j)
  have hz0 : z ∘ (0 : Fin 2).succAbove = fun _ ↦ j := by
    funext l
    fin_cases l
    rfl
  have hz1 : z ∘ (1 : Fin 2).succAbove = y := by
    funext l
    fin_cases l
    rfl
  have h0 := congrFun hc z
  rw [TopCat.Presheaf.cechComplex_d_apply, Fin.sum_univ_two] at h0
  have hzj : ⨅ l, U (z l) ≤ ⨅ l, U ((fun _ : Fin 1 ↦ j) l) := le_iInf fun _ ↦ iInf_le _ 1
  have hzy : ⨅ l, U (z l) ≤ ⨅ l, U (y l) := le_iInf fun l ↦ by
    rw [show l = 0 from Fin.ext (Nat.lt_one_iff.mp l.isLt)]
    exact iInf_le _ 0
  rw [TopCat.Presheaf.map_homOfLE_apply_congr U Q c hz0 _ hzj,
    TopCat.Presheaf.map_homOfLE_apply_congr U Q c hz1 _ hzy] at h0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h0
  have h0' := sub_eq_zero.mp ((sub_eq_add_neg _ _).trans h0)
  have hge : (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W ≤
      (⨅ l, U (z l)).ι ''ᵁ (⨅ l, U (z l)).ι ⁻¹ᵁ W := by
    rw [ι_image_preimage, ι_image_preimage]
    refine le_inf (le_iInf fun l ↦ ?_) inf_le_right
    refine Fin.cases ?_ (fun l ↦ ?_) l
    · exact inf_le_left.trans (iInf_le _ 0)
    · exact inf_le_right.trans hW
  have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_mono hzy W)) hge
  apply (ConcreteCategory.bijective_of_isIso
    (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono hzy W)).op)).1
  refine Eq.trans ?_ ((hQ hzj _).symm.trans (h0'.trans (hQ hzy (c y))))
  exact (congrArg _ (presheaf_map_map_apply_eq ℱ _ _
    (homOfLE ((ι_image_preimage_le_self _ W).trans hj.ge)).op _)).trans
    (presheaf_map_map_apply_eq ℱ _ _ _ _)

/-- The Čech complex of a cover is exact in positive degrees. -/
theorem exactAt_cechResolution (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechResolution U ℱ).ExactAt (n + 1) := by
  refine exactAt_of_exactAt_sectionsAb _ _ fun x V hxV ↦ ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ i, U i)
  exact ⟨V ⊓ U j, ⟨hxV, hj⟩, inf_le_left,
    exactAt_sectionsAb_cechResolution U ℱ inf_le_right n⟩


lemma exists_le_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (x : X) (V : X.Opens) (hxV : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ ∃ j, W ≤ U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ i, U i)
  exact ⟨V ⊓ U j, ⟨hxV, hj⟩, inf_le_left, j, inf_le_right⟩

/-- **The Čech resolution.** For an open cover `U` of `X` and an `𝒪_X`-module `ℱ`, the augmented
sheafified Čech complex `0 ⟶ ℱ ⟶ Č⁰(U, ℱ) ⟶ Č¹(U, ℱ) ⟶ ⋯` is exact: the augmentation
`ℱ ⟶ Č(U, ℱ)` is a quasi-isomorphism from `ℱ` placed in degree `0`.

Exactness is checked on the sections over the opens `W` contained in some member `U j` of the
cover; there, inserting the index `j` contracts the Čech complex of sections.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem quasiIso_cechResolutionι (hU : ⨆ i, U i = ⊤) : QuasiIso (cechResolutionι U ℱ) := by
  have hmono : Mono (cechResolutionAugmentation U ℱ) := by
    refine (exact_of_exact_sectionsAb
      (ShortComplex.mk (0 : 0 ⟶ ℱ) (cechResolutionAugmentation U ℱ) zero_comp)
      fun x V hxV ↦ ?_).mono_g rfl
    obtain ⟨W, hxW, hWV, j, hWj⟩ := exists_le_of_iSup_eq_top U hU x V hxV
    refine ⟨W, hxW, hWV, ?_⟩
    rw [ShortComplex.ab_exact_iff]
    intro s hs
    refine ⟨0, ?_⟩
    refine (injective_and_exact_sectionsAb_cechResolution_zero U ℱ hWj).1 ?_
    exact (map_zero _).trans hs.symm
  exact quasiIso_fromSingle₀Equiv_symm _ _
    (exact_of_exact_sectionsAb _ fun x V hxV ↦ by
      obtain ⟨W, hxW, hWV, j, hWj⟩ := exists_le_of_iSup_eq_top U hU x V hxV
      exact ⟨W, hxW, hWV, (injective_and_exact_sectionsAb_cechResolution_zero U ℱ hWj).2⟩)
    (exactAt_cechResolution U ℱ hU)

end Exactness

section Acyclic

instance preservesFiniteLimits_pushforward {Y Z : Scheme.{u}} (h : Y ⟶ Z) :
    PreservesFiniteLimits (pushforward h) :=
  have := (pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **Direct images along a composite.** If `R^q h_* G = 0` and `R^q (h ≫ f)_* G = 0` for all
`q > 0`, then `h_* G` is `f_*`-acyclic: an injective resolution `G ⟶ J` pushes forward to a
resolution `h_* G ⟶ h_* J` by flasque modules, and `f_* h_* J = (h ≫ f)_* J`. -/
theorem rightAcyclic_pushforward_obj_of_isZero {Y Z S : Scheme.{u}} (h : Y ⟶ Z) (f : Z ⟶ S)
    [HasInjectiveResolutions Y.Modules] [HasInjectiveResolutions Z.Modules] (G : Y.Modules)
    (hh : ∀ q, IsZero ((higherDirectImage h (q + 1)).obj G))
    (hhf : ∀ q, IsZero ((higherDirectImage (h ≫ f) (q + 1)).obj G)) :
    (pushforward f).rightAcyclic ((pushforward h).obj G) := by
  let J := injectiveResolution G
  let K := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hε : (pushforward h).map (J.ι.f 0) ≫ K.d 0 1 = 0 := by
    change (pushforward h).map (J.ι.f 0) ≫ (pushforward h).map (J.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero]
  have : Mono ((pushforward h).map (J.ι.f 0)) := inferInstance
  have h0 : (ShortComplex.mk _ _ hε).Exact :=
    J.exact₀.map_of_mono_of_preservesKernel (pushforward h) inferInstance inferInstance
  have hK (n : ℕ) : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hh n).of_iso (J.isoRightDerivedObj (pushforward h) (n + 1)).symm
  have := quasiIso_fromSingle₀Equiv_symm _ hε h0 hK
  have hI (n : ℕ) : (pushforward f).rightAcyclic (K.X n) :=
    rightAcyclic_pushforward_of_isFlasque f _
      (isFlasque_pushforward h _ (isFlasque_of_injective _))
  intro q
  refine IsZero.of_iso ?_ ((pushforward f).rightDerivedObjIsoOfResolution
    ((CochainComplex.fromSingle₀Equiv K _).symm ⟨_, hε⟩) hI (q + 1))
  exact (hhf q).of_iso (HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (pushforwardComp h f) _).app J.cocomplex) (q + 1) ≪≫
      (J.isoRightDerivedObj (pushforward (h ≫ f)) (q + 1)).symm)

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- For an affine open `V` of a scheme `X` separated over an affine scheme `S` and a
quasi-coherent `ℱ`, the module `j_* (ℱ|_V)` is `f_*`-acyclic: the inclusion `j : V ⟶ X` and the
composite `V ⟶ S` are affine morphisms. -/
theorem rightAcyclic_extendRestrict [IsAffine S] [IsSeparated f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) : (pushforward f).rightAcyclic ((extendRestrictFunctor V).obj ℱ) := by
  have : IsAffine V := hV
  have := isGrothendieckAbelian V
  have : IsAffineHom V.ι := IsAffineHom.of_comp V.ι f
  exact rightAcyclic_pushforward_obj_of_isZero V.ι f _
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)

variable {ι : Type u} (U : ι → X.Opens)

lemma piObj_eq_iInf {k : ℕ} (y : Fin (k + 1) → ι) : ∏ᶜ (fun l ↦ U (y l)) = ⨅ l, U (y l) :=
  le_antisymm (TopCat.Presheaf.piObj_le_iInf U y) (TopCat.Presheaf.iInf_le_piObj U y)

/-- **The terms of the Čech complex are `f_*`-acyclic**, for a finite cover by affine opens of a
scheme separated over an affine scheme and a quasi-coherent module.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem rightAcyclic_cechResolution_X [IsAffine S] [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (k : ℕ) : (pushforward f).rightAcyclic ((cechResolution U ℱ).X k) := by
  have : (pushforward f).rightAcyclic.IsClosedUnderFiniteProducts := .mk'
  change (pushforward f).rightAcyclic
    (∏ᶜ fun y : Fin (k + 1) → ι ↦ (cechPresheaf ℱ).obj (op (∏ᶜ fun l ↦ U (y l))))
  refine ObjectProperty.prop_product _ fun y ↦ ?_
  exact rightAcyclic_extendRestrict f ℱ
    ((piObj_eq_iInf U y).symm ▸ isAffineOpen_iInf_of_isSeparated f U hU k y)

/-- **The Čech resolution computes the higher direct images.** Let `f : X ⟶ S` be separated with
`S` affine, `U` a finite cover of `X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module.
Then `R^q f_* ℱ` is the `q`-th cohomology sheaf of the complex `f_* Č(U, ℱ)` of
`𝒪_S`-modules: the augmented Čech complex is a resolution of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.quasiIso_cechResolutionι`) by `f_*`-acyclic modules
(`AlgebraicGeometry.Scheme.Modules.rightAcyclic_cechResolution_X`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
noncomputable def higherDirectImageIsoCechResolution [IsAffine S] [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i)) (hU' : ⨆ i, U i = ⊤)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (q : ℕ) :
    (higherDirectImage f q).obj ℱ ≅
      (((pushforward f).mapHomologicalComplex _).obj (cechResolution U ℱ)).homology q :=
  have := quasiIso_cechResolutionι U ℱ hU'
  (pushforward f).rightDerivedObjIsoOfResolution (cechResolutionι U ℱ)
    (rightAcyclic_cechResolution_X f U hU ℱ) q

/-- The augmentation of the Čech complex is natural in the module. -/
@[reassoc]
lemma cechResolutionAugmentation_naturality {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    cechResolutionAugmentation U ℱ ≫ ((cechResolutionFunctor U).map φ).f 0 =
      φ ≫ cechResolutionAugmentation U 𝒢 := by
  rw [cechResolutionAugmentation, cechResolutionAugmentation, Category.assoc]
  erw [cechAugmentation_naturality]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact ((restrictAdjunction (⊤ : X.Opens).ι).unit.naturality φ).symm

/-- **The identification of `R^q f_* ℱ` with the cohomology of `f_* Č(U, ℱ)` is natural** in the
quasi-coherent module `ℱ`. -/
lemma higherDirectImageIsoCechResolution_hom_naturality [IsAffine S] [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i)) (hU' : ⨆ i, U i = ⊤)
    {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (φ : ℱ ⟶ 𝒢) (q : ℕ) :
    (higherDirectImage f q).map φ ≫ (higherDirectImageIsoCechResolution f U hU hU' 𝒢 q).hom =
      (higherDirectImageIsoCechResolution f U hU hU' ℱ q).hom ≫
        HomologicalComplex.homologyMap
          (((pushforward f).mapHomologicalComplex _).map ((cechResolutionFunctor U).map φ)) q := by
  have := quasiIso_cechResolutionι U ℱ hU'
  have := quasiIso_cechResolutionι U 𝒢 hU'
  let cℱ := InjectiveResolution.descOfQuasiIso (𝟙 ℱ) (injectiveResolution ℱ)
    (cechResolutionι U ℱ)
  let c𝒢 := InjectiveResolution.descOfQuasiIso (𝟙 𝒢) (injectiveResolution 𝒢)
    (cechResolutionι U 𝒢)
  let d := InjectiveResolution.desc φ (injectiveResolution 𝒢) (injectiveResolution ℱ)
  have hcℱ := InjectiveResolution.descOfQuasiIso_commutes (𝟙 ℱ) (injectiveResolution ℱ)
    (cechResolutionι U ℱ)
  have hc𝒢 := InjectiveResolution.descOfQuasiIso_commutes (𝟙 𝒢) (injectiveResolution 𝒢)
    (cechResolutionι U 𝒢)
  have hd := InjectiveResolution.desc_commutes φ (injectiveResolution 𝒢) (injectiveResolution ℱ)
  have ho : Homotopy ((cechResolutionFunctor U).map φ ≫ c𝒢) (cℱ ≫ d) :=
    CochainComplex.homotopyOfQuasiIso (cechResolutionι U ℱ) _ _ (by
      have e1 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hc𝒢
      have e2 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hcℱ
      have e3 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hd
      simp only [HomologicalComplex.comp_f, cechResolutionι_f_zero] at e1 e2 e3 ⊢
      calc _ = φ ≫ cechResolutionAugmentation U 𝒢 ≫ c𝒢.f 0 := by
            erw [cechResolutionAugmentation_naturality_assoc]
        _ = φ ≫ (injectiveResolution 𝒢).ι.f 0 := by erw [e1]; simp
        _ = (injectiveResolution ℱ).ι.f 0 ≫ d.f 0 := by erw [e3]; simp
        _ = _ := by erw [reassoc_of% e2]; simp)
  have : QuasiIso (((pushforward f).mapHomologicalComplex _).map c𝒢) :=
    (pushforward f).quasiIso_map_of_rightAcyclic_nat c𝒢
      (rightAcyclic_cechResolution_X f U hU 𝒢) fun _ ↦ Functor.rightAcyclic_of_injective _
  have hH := ((pushforward f).mapHomotopy ho).homologyMap_eq q
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hH
  have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality φ (injectiveResolution ℱ)
    (injectiveResolution 𝒢) d (congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hd) (pushforward f) q
  dsimp only [higherDirectImageIsoCechResolution, Functor.rightDerivedObjIsoOfResolution,
    InjectiveResolution.isoRightDerivedObjOfQuasiIso]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv,
    ← cancel_mono (HomologicalComplex.homologyMap
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).map c𝒢) q)]
  simp only [Category.assoc]
  erw [IsIso.inv_hom_id, Category.comp_id]
  rw [hH, IsIso.inv_hom_id_assoc]
  exact hnat


end Acyclic

end AlgebraicGeometry.Scheme.Modules
