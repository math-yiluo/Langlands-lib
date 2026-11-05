import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom

/-!
# Naturality of the Čech comparison in the module

For a morphism `φ : M ⟶ N` of `𝒪_X`-modules and an ordered affine cover `𝒰` of `X`, this file
builds the induced maps of sheafified Čech complexes and of alternating Čech cochain complexes,
and proves that the identification `cechCohomologyIso` of Čech cohomology with actual
`R`-module cohomology commutes with the maps induced by `φ`. As a consequence, an inclusion of
kernels of maps on actual cohomology in positive degree follows from a statement about Čech
cocycles and coboundaries.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
  Langlands.AlgebraicGeometry.Modules.DerivedSections

section Sheaf

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)

/-- The map `sheafOn M W ⟶ sheafOn N W` induced by `φ`. -/
def sheafOnMap (W : X.Opens) : sheafOn M W ⟶ sheafOn N W :=
  (Scheme.Modules.pushforward W.ι).map ((Scheme.Modules.restrictFunctor W.ι).map φ)

lemma sheafOnMap_app (W V : X.Opens) :
    (sheafOnMap φ W).app V = φ.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) := rfl

@[reassoc]
lemma res_sheafOnMap {W W' : X.Opens} (h : W' ≤ W) :
    res M h ≫ sheafOnMap φ W' = sheafOnMap φ W ≫ res N h := by
  ext V : 1
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, res_app, res_app,
    sheafOnMap_app, sheafOnMap_app]
  exact φ.mapPresheaf.naturality _

@[reassoc]
lemma unit_sheafOnMap (W : X.Opens) : unit M W ≫ sheafOnMap φ W = φ ≫ unit N W :=
  ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality φ).symm

variable (𝒰 : X.OrderedAffineCover)

/-- The map of `p`-th sheafified Čech terms induced by `φ`. -/
def cechTermMap (p : ℕ) : cechTerm 𝒰 M p ⟶ cechTerm 𝒰 N p :=
  biproduct.map (f := fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s))
    (g := fun s : 𝒰.Idx p => sheafOn N (𝒰.inter s)) fun s => sheafOnMap φ (𝒰.inter s)

@[reassoc]
lemma cechTermMap_π (p : ℕ) (s : 𝒰.Idx p) :
    cechTermMap φ 𝒰 p ≫ biproduct.π (fun s : 𝒰.Idx p => sheafOn N (𝒰.inter s)) s =
      biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s ≫ sheafOnMap φ (𝒰.inter s) :=
  biproduct.map_π (f := fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s))
    (g := fun s : 𝒰.Idx p => sheafOn N (𝒰.inter s)) (fun s => sheafOnMap φ (𝒰.inter s)) s

lemma cechD_cechTermMap (p : ℕ) :
    cechD 𝒰 M p ≫ cechTermMap φ 𝒰 (p + 1) = cechTermMap φ 𝒰 p ≫ cechD 𝒰 N p := by
  refine biproduct.hom_ext _ _ fun t => ?_
  rw [Category.assoc, Category.assoc, cechTermMap_π, cechD_π_assoc, cechD_π,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc, res_sheafOnMap,
    cechTermMap_π_assoc]

/-- The map of sheafified Čech complexes induced by `φ`. -/
def cechComplexMap : cechComplex 𝒰 M ⟶ cechComplex 𝒰 N :=
  CochainComplex.ofHom (cechTermMap φ 𝒰) fun p => by
    have h₁ : (cechComplex 𝒰 M).d p (p + 1) = cechD 𝒰 M p :=
      CochainComplex.of_d (cechTerm 𝒰 M) (cechD 𝒰 M) p
    have h₂ : (cechComplex 𝒰 N).d p (p + 1) = cechD 𝒰 N p :=
      CochainComplex.of_d (cechTerm 𝒰 N) (cechD 𝒰 N) p
    rw [h₁, h₂]
    exact (cechD_cechTermMap φ 𝒰 p).symm

lemma cechComplexMap_f (p : ℕ) : (cechComplexMap φ 𝒰).f p = cechTermMap φ 𝒰 p := rfl

lemma augmentation_cechTermMap :
    augmentation 𝒰 M ≫ cechTermMap φ 𝒰 0 = φ ≫ augmentation 𝒰 N := by
  refine biproduct.hom_ext _ _ fun s => ?_
  rw [Category.assoc, Category.assoc, cechTermMap_π, augmentation_π_assoc, augmentation_π,
    unit_sheafOnMap]

lemma cechAug_cechComplexMap :
    cechAug 𝒰 M ≫ cechComplexMap φ 𝒰 =
      (CochainComplex.single₀ X.Modules).map φ ≫ cechAug 𝒰 N := by
  ext : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    cechComplexMap_f]
  have hM : (cechAug 𝒰 M).f 0 = augmentation 𝒰 M :=
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
  have hN : (cechAug 𝒰 N).f 0 = augmentation 𝒰 N :=
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
  rw [hM, hN]
  exact augmentation_cechTermMap φ 𝒰

lemma toCochainFun_cechTermMap {p : ℕ} (x : Γ(cechTerm 𝒰 M p, ⊤)) (s : 𝒰.Idx p) :
    toCochainFun 𝒰 N ((cechTermMap φ 𝒰 p).app ⊤ x) s =
      φ.app (𝒰.inter s) (toCochainFun 𝒰 M x s) := by
  simp only [toCochainFun, cr_def, toSec]
  rw [← comp_app_apply, cechTermMap_π, comp_app_apply]
  exact (app_map_apply φ (inter_le_cechOpen 𝒰 s) _).symm

end Sheaf

section Cochains

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {M N : X.Modules}
  (φ : M ⟶ N)

/-- A morphism of `𝒪_X`-modules as a morphism of the FLT presheaves of sections. -/
def ofModulesHom :
    OModulePresheaf.Hom (OModulePresheaf.ofModules π M) (OModulePresheaf.ofModules π N) where
  app U :=
    { toFun := fun x => (show (OModulePresheaf.ofModules π N).obj U from φ.app U x)
      map_add' := fun x y => map_add (φ.app U).hom x y
      map_smul' := fun r x => by
        rw [OModulePresheaf.ofModules_algebraMap_smul, OModulePresheaf.ofModules_algebraMap_smul]
        exact Scheme.Modules.Hom.app_smul φ _ x }
  app_smul U a x := Scheme.Modules.Hom.app_smul φ a x
  naturality h := LinearMap.ext fun x => app_map_apply φ h x

lemma ofModulesHom_app_apply (U : X.Opens) (x : Γ(M, U)) :
    (ofModulesHom π φ).app U x = φ.app U x := rfl

variable (𝒰 : X.OrderedAffineCover)

/-- The `R`-linear map of alternating Čech cochains induced by `φ`: `c ↦ (s ↦ φ (c s))`. -/
def cochainMap (p : ℕ) :
    (OModulePresheaf.ofModules π M).cochain 𝒰 p →ₗ[R]
      (OModulePresheaf.ofModules π N).cochain 𝒰 p :=
  LinearMap.pi fun s => ((ofModulesHom π φ).app (𝒰.inter s)).comp (LinearMap.proj s)

lemma cochainMap_apply (p : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 p)
    (s : 𝒰.Idx p) : cochainMap π φ 𝒰 p c s = (ofModulesHom π φ).app (𝒰.inter s) (c s) := rfl

lemma cochainMap_comp_d (p : ℕ) :
    cochainMap π φ 𝒰 (p + 1) ∘ₗ (OModulePresheaf.ofModules π M).d 𝒰 p =
      (OModulePresheaf.ofModules π N).d 𝒰 p ∘ₗ cochainMap π φ 𝒰 p := by
  refine LinearMap.ext fun c => funext fun s => ?_
  simp only [LinearMap.comp_apply, cochainMap_apply, OModulePresheaf.d_apply, map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg _
    ((ofModulesHom π φ).naturality_apply (𝒰.inter_le_inter_face s j) _)

/-- The map of alternating Čech cochain complexes induced by `φ`. -/
def cechCochainMap : cechCochainComplex π 𝒰 M ⟶ cechCochainComplex π 𝒰 N :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (cochainMap π φ 𝒰 p)) fun p => by
    have h₁ : (cechCochainComplex π 𝒰 M).d p (p + 1) =
        ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 p) :=
      CochainComplex.of_d (V := ModuleCat.{u} R)
        (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
        (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) p
    have h₂ : (cechCochainComplex π 𝒰 N).d p (p + 1) =
        ModuleCat.ofHom ((OModulePresheaf.ofModules π N).d 𝒰 p) :=
      CochainComplex.of_d (V := ModuleCat.{u} R)
        (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π N).cochain 𝒰 i))
        (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π N).d 𝒰 i)) p
    rw [h₁, h₂]
    ext1
    exact (cochainMap_comp_d π φ 𝒰 p).symm

lemma cechCochainMap_f_apply (p : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 p) :
    (cechCochainMap π φ 𝒰).f p c = cochainMap π φ 𝒰 p c := rfl

lemma cechCochainComplex_d (p : ℕ) :
    (cechCochainComplex π 𝒰 M).d p (p + 1) =
      ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 p) :=
  CochainComplex.of_d (V := ModuleCat.{u} R)
    (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
    (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) p

lemma sectionsComplexIso_hom_naturality :
    (sectionsComplexIso π 𝒰 M).hom ≫ cechCochainMap π φ 𝒰 =
      ((relativeGlobalSections π).mapHomologicalComplex _).map (cechComplexMap φ 𝒰) ≫
        (sectionsComplexIso π 𝒰 N).hom := by
  ext p x : 3
  funext s
  exact (toCochainFun_cechTermMap φ 𝒰 x s).symm

lemma sectionsComplexIso_inv_naturality :
    cechCochainMap π φ 𝒰 ≫ (sectionsComplexIso π 𝒰 N).inv =
      (sectionsComplexIso π 𝒰 M).inv ≫
        ((relativeGlobalSections π).mapHomologicalComplex _).map (cechComplexMap φ 𝒰) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, sectionsComplexIso_hom_naturality]

end Cochains

section Naturality

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  (𝒰 : X.OrderedAffineCover) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (φ : M ⟶ N)

/-- The identification of Čech cohomology with actual `R`-module cohomology is natural in the
quasi-coherent module. -/
@[reassoc]
theorem cechCohomologyIso_hom_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (cechCochainMap π φ 𝒰) n ≫ (cechCohomologyIso π 𝒰 N n).hom =
      (cechCohomologyIso π 𝒰 M n).hom ≫ (relativeCohomology π n).map φ := by
  have := quasiIso_cechAug 𝒰 N
  have := quasiIso_cechAug 𝒰 M
  have key := resolutionComparison_naturality (relativeGlobalSections π) (cechAug 𝒰 M)
    (cechAug 𝒰 N) φ (cechComplexMap φ 𝒰) (cechAug_cechComplexMap φ 𝒰) n
  have h₁ : HomologicalComplex.homologyMap (cechCochainMap π φ 𝒰) n ≫
      HomologicalComplex.homologyMap (sectionsComplexIso π 𝒰 N).inv n =
    HomologicalComplex.homologyMap (sectionsComplexIso π 𝒰 M).inv n ≫
      HomologicalComplex.homologyMap
        (((relativeGlobalSections π).mapHomologicalComplex _).map (cechComplexMap φ 𝒰)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      sectionsComplexIso_inv_naturality]
  exact (Category.assoc _ _ _).symm.trans <|
    (h₁ =≫ resolutionComparison (relativeGlobalSections π) (cechAug 𝒰 N) n).trans <|
      (Category.assoc _ _ _).trans <|
        (HomologicalComplex.homologyMap (sectionsComplexIso π 𝒰 M).inv n ≫= key).trans
          (Category.assoc _ _ _).symm

end Naturality

section Kernels

variable {R : Type u} [CommRing R]

/-- In a cochain complex of modules, a cycle whose homology class vanishes is a boundary. -/
lemma exists_toCycles_eq_of_homologyπ_eq_zero (K : CochainComplex (ModuleCat.{u} R) ℕ) (p : ℕ)
    (w : K.cycles (p + 1)) (hw : K.homologyπ (p + 1) w = 0) :
    ∃ y : K.X p, K.toCycles p (p + 1) y = w := by
  have hS : (ShortComplex.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1))
      (K.toCycles_comp_homologyπ p (p + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel p (p + 1) (by simp))
  have h := hS.moduleCat_range_eq_ker
  have hmem : w ∈ LinearMap.ker (K.homologyπ (p + 1)).hom := hw
  rw [← h] at hmem
  exact hmem

/-- An inclusion of kernels of maps on cohomology in positive degree `p + 1` follows from the
corresponding statement on cocycles: whenever `a z` is a coboundary, so is `b z`. -/
theorem ker_homologyMap_le {C D E : CochainComplex (ModuleCat.{u} R) ℕ} (a : C ⟶ D) (b : C ⟶ E)
    (p : ℕ)
    (h : ∀ z : C.X (p + 1), C.d (p + 1) (p + 1 + 1) z = 0 →
      (∃ y : D.X p, D.d p (p + 1) y = a.f (p + 1) z) → ∃ y : E.X p, E.d p (p + 1) y = b.f (p + 1) z) :
    LinearMap.ker (HomologicalComplex.homologyMap a (p + 1)).hom ≤
      LinearMap.ker (HomologicalComplex.homologyMap b (p + 1)).hom := by
  intro x hx
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ (p + 1))).1 inferInstance x
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    ModuleCat.comp_apply] at hx ⊢
  obtain ⟨y, hy⟩ := exists_toCycles_eq_of_homologyπ_eq_zero D p _ hx
  have hz : C.d (p + 1) (p + 1 + 1) (C.iCycles (p + 1) c) = 0 := by
    rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  have hay : D.d p (p + 1) y = a.f (p + 1) (C.iCycles (p + 1) c) := by
    rw [← HomologicalComplex.toCycles_i, ModuleCat.comp_apply, hy, ← ModuleCat.comp_apply,
      HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
  obtain ⟨y', hy'⟩ := h _ hz ⟨y, hay⟩
  have hc : E.toCycles p (p + 1) y' = HomologicalComplex.cyclesMap b (p + 1) c := by
    apply (ModuleCat.mono_iff_injective (E.iCycles (p + 1))).1 inferInstance
    rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i, hy', ← ModuleCat.comp_apply,
      ← HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
  rw [← hc, ← ModuleCat.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

end Kernels

section Relative

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  (𝒰 : X.OrderedAffineCover) {M N N' : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  [N'.IsQuasicoherent]

/-- An inclusion of kernels of maps on actual `R`-module cohomology in degree `p + 1` follows
from the corresponding statement on alternating Čech cocycles: whenever `a z` is a Čech
coboundary, so is `b z`. -/
theorem ker_relativeCohomology_map_le (a : M ⟶ N) (b : M ⟶ N') (p : ℕ)
    (h : ∀ z : (OModulePresheaf.ofModules π M).cochain 𝒰 (p + 1),
      (OModulePresheaf.ofModules π M).d 𝒰 (p + 1) z = 0 →
      (∃ y, (OModulePresheaf.ofModules π N).d 𝒰 p y = cochainMap π a 𝒰 (p + 1) z) →
        ∃ y, (OModulePresheaf.ofModules π N').d 𝒰 p y = cochainMap π b 𝒰 (p + 1) z) :
    LinearMap.ker ((relativeCohomology π (p + 1)).map a).hom ≤
      LinearMap.ker ((relativeCohomology π (p + 1)).map b).hom := by
  have hK := ker_homologyMap_le (cechCochainMap π a 𝒰) (cechCochainMap π b 𝒰) p
    (fun z hz hy => by
      rw [cechCochainComplex_d] at hz
      obtain ⟨y, hy⟩ := hy
      rw [cechCochainComplex_d] at hy
      obtain ⟨y', hy'⟩ := h z hz ⟨y, hy⟩
      refine ⟨y', ?_⟩
      rw [cechCochainComplex_d]
      exact hy')
  intro x hx
  have ea : (relativeCohomology π (p + 1)).map a =
      (cechCohomologyIso π 𝒰 M (p + 1)).inv ≫
        HomologicalComplex.homologyMap (cechCochainMap π a 𝒰) (p + 1) ≫
          (cechCohomologyIso π 𝒰 N (p + 1)).hom := by
    rw [cechCohomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  have eb : (relativeCohomology π (p + 1)).map b =
      (cechCohomologyIso π 𝒰 M (p + 1)).inv ≫
        HomologicalComplex.homologyMap (cechCochainMap π b 𝒰) (p + 1) ≫
          (cechCohomologyIso π 𝒰 N' (p + 1)).hom := by
    rw [cechCohomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [LinearMap.mem_ker, ea] at hx
  rw [LinearMap.mem_ker, eb]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx ⊢
  have hx' : HomologicalComplex.homologyMap (cechCochainMap π a 𝒰) (p + 1)
      ((cechCohomologyIso π 𝒰 M (p + 1)).inv x) = 0 := by
    have := congrArg (cechCohomologyIso π 𝒰 N (p + 1)).inv.hom hx
    rwa [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, map_zero] at this
  have := hK hx'
  rw [LinearMap.mem_ker] at this
  rw [this, map_zero]

end Relative

end Langlands.AlgebraicGeometry.Modules.CechResolution
