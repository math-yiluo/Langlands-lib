import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Langlands.Cohomology.AcyclicResolution.DerivedComparison
import Langlands.Cohomology.AcyclicResolution.ComparisonProof

/-!
# Čech cochains compute actual derived `R`-module sections

Let `π : X ⟶ Spec R` be separated, `𝒰` an ordered affine cover of `X` and `M` a quasi-coherent
`𝒪_X`-module. The `R`-module global sections of the sheafified Čech complex `cechComplex 𝒰 M`
form the complex of alternating Čech cochains `OModulePresheaf.cochain` of the Anthropic FLT
port, and since `cechComplex 𝒰 M` is a resolution of `M` by `Γ_R`-acyclic modules, the image of
the Čech cochain complex in the derived category of `R`-modules is isomorphic to the actual
right derived complex of `R`-module global sections at `M`.
-/

universe w w' v v' u₁ u₂ u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

section Abstract

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- For a right resolution `ε : A[0] ⟶ K` by `F`-acyclic objects, the canonical derived
comparison from `F K` to the right derived complex of `F` at `A` is an isomorphism. -/
theorem isIso_derivedResolutionComparison {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
    (hK : ∀ i n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i))) :
    IsIso (derivedResolutionComparison F ε) := by
  let I := injectiveResolution A
  let φ := lift ε (𝟙 A) I.ι
  have hq : QuasiIso ((F.mapHomologicalComplex _).map φ) :=
    AcyclicComparison.quasiIso_map F ε hK I φ (comp_lift_id ε I)
  have h₁ : QuasiIso (HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ)
      ComplexShape.embeddingUpNat) := by
    rw [HomologicalComplex.quasiIso_extendMap_iff]
    exact hq
  have h₂ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (extendMapIso _ F K) (extendMapIso _ F I.cocomplex)
        (extendMapIso_hom_naturality _ F φ).symm)).2 h₁
  have : IsIso ((derivedResolutionFunctor F).map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h₂
  change IsIso ((derivedResolutionFunctor F).map φ ≫ (derivedResolutionIso F I).inv)
  infer_instance

end Abstract

section Sections

variable {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (M : X.Modules)

lemma inter_le_cechOpen {p : ℕ} (s : 𝒰.Idx p) : 𝒰.inter s ≤ cechOpen 𝒰 s ⊤ := by
  rw [cechOpen_eq, inf_top_eq]

lemma cechOpen_le_inter {p : ℕ} (s : 𝒰.Idx p) : cechOpen 𝒰 s ⊤ ≤ 𝒰.inter s := by
  rw [cechOpen_eq, inf_top_eq]

variable {M} in
lemma map_map_of_le_of_le {U V : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ U) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    show (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 (op U) from rfl, M.presheaf.map_id]
  rfl

/-- The global sections of the `p`-th Čech term as a family of sections of `M` over the opens
`𝒰.inter s`. -/
def toCochainFun {p : ℕ} (x : Γ(cechTerm 𝒰 M p, ⊤)) (s : 𝒰.Idx p) : Γ(M, 𝒰.inter s) :=
  cr (toSec M ⊤ x) s (inter_le_cechOpen 𝒰 s)

lemma toCochainFun_injective (p : ℕ) :
    Function.Injective (fun x : Γ(cechTerm 𝒰 M p, ⊤) => toCochainFun 𝒰 M x) := by
  intro x y h
  refine toSec_injective M ⊤ (funext fun s => ?_)
  have hs : M.presheaf.map (homOfLE (inter_le_cechOpen 𝒰 s)).op (toSec M ⊤ x s) =
      M.presheaf.map (homOfLE (inter_le_cechOpen 𝒰 s)).op (toSec M ⊤ y s) := congrFun h s
  rw [← map_map_of_le_of_le (cechOpen_le_inter 𝒰 s) (inter_le_cechOpen 𝒰 s) (toSec M ⊤ x s), hs,
    map_map_of_le_of_le]

lemma toCochainFun_surjective (p : ℕ) :
    Function.Surjective (fun x : Γ(cechTerm 𝒰 M p, ⊤) => toCochainFun 𝒰 M x) := by
  intro c
  obtain ⟨x, hx⟩ := toSec_surjective (𝒰 := 𝒰) (p := p) M ⊤
    (fun s => M.presheaf.map (homOfLE (cechOpen_le_inter 𝒰 s)).op (c s))
  refine ⟨x, funext fun s => ?_⟩
  change M.presheaf.map (homOfLE (inter_le_cechOpen 𝒰 s)).op (toSec M ⊤ x s) = c s
  rw [hx]
  exact map_map_of_le_of_le _ _ (c s)

lemma toCochainFun_cechD {p : ℕ} (x : Γ(cechTerm 𝒰 M p, ⊤)) (t : 𝒰.Idx (p + 1)) :
    toCochainFun 𝒰 M ((cechD 𝒰 M p).app ⊤ x) t =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        M.presheaf.map (homOfLE (𝒰.inter_le_inter_face t j)).op
          (toCochainFun 𝒰 M x (𝒰.face t j)) := by
  simp only [toCochainFun, cr_def]
  rw [toSec_cechD]
  simp only [dSec, map_sum, map_zsmul, cr_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    ← M.presheaf.map_comp]
  rfl

lemma toCochainFun_add {p : ℕ} (x y : Γ(cechTerm 𝒰 M p, ⊤)) :
    toCochainFun 𝒰 M (x + y) = toCochainFun 𝒰 M x + toCochainFun 𝒰 M y := by
  funext s
  simp only [toCochainFun, cr_def, toSec, map_add, Pi.add_apply]
  exact map_add _ _ _

lemma toCochainFun_smul {p : ℕ} (r : Γ(X, ⊤)) (x : Γ(cechTerm 𝒰 M p, ⊤)) (s : 𝒰.Idx p) :
    toCochainFun 𝒰 M (r • x) s =
      X.presheaf.map (homOfLE (inter_le_cechOpen 𝒰 s)).op
          (((𝒰.inter s).ι.app ⊤ ≫ ((𝒰.inter s).ι.appIso ((𝒰.inter s).ι ⁻¹ᵁ ⊤)).inv) r) •
        toCochainFun 𝒰 M x s := by
  have h : (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s).app ⊤ (r • x) =
      r • (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s).app ⊤ x :=
    Scheme.Modules.Hom.app_smul _ r x
  simp only [toCochainFun, cr_def, toSec]
  rw [h, smul_eq]
  exact Scheme.Modules.map_smul M _ _ _

end Sections

section Relative

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) (𝒰 : X.OrderedAffineCover)
  (M : X.Modules)

lemma relativeGlobalSections_smul (N : X.Modules) (r : R)
    (x : (DerivedSections.relativeGlobalSections π).obj N) :
    r • x = (show (DerivedSections.relativeGlobalSections π).obj N from
      ((DerivedSections.structureRingHom π).hom r • (show Γ(N, ⊤) from x))) :=
  rfl

lemma relativeGlobalSections_map_apply {N N' : X.Modules} (f : N ⟶ N')
    (x : (DerivedSections.relativeGlobalSections π).obj N) :
    (DerivedSections.relativeGlobalSections π).map f x =
      (show (DerivedSections.relativeGlobalSections π).obj N' from f.app ⊤ x) :=
  rfl

lemma structureRingHom_comp {p : ℕ} (s : 𝒰.Idx p) :
    DerivedSections.structureRingHom π ≫
        ((𝒰.inter s).ι.app ⊤ ≫ ((𝒰.inter s).ι.appIso ((𝒰.inter s).ι ⁻¹ᵁ ⊤)).inv) ≫
          X.presheaf.map (homOfLE (inter_le_cechOpen 𝒰 s)).op =
      (Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ (𝒰.inter s) le_top := by
  rw [Scheme.Hom.app_appIso_inv]
  simp only [DerivedSections.structureRingHom, Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact (X.presheaf.map_comp _ _).symm

/-- The `R`-linear map from the `R`-module global sections of the `p`-th Čech term to the
alternating Čech cochains of the FLT port. -/
def toCochain (p : ℕ) :
    (DerivedSections.relativeGlobalSections π).obj (cechTerm 𝒰 M p) →ₗ[R]
      (OModulePresheaf.ofModules π M).cochain 𝒰 p where
  toFun x := toCochainFun 𝒰 M x
  map_add' x y := toCochainFun_add 𝒰 M x y
  map_smul' r x := by
    funext s
    rw [relativeGlobalSections_smul]
    refine (toCochainFun_smul 𝒰 M _ x s).trans ?_
    change _ = ((Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ (𝒰.inter s) le_top).hom r •
      toCochainFun 𝒰 M x s
    rw [← structureRingHom_comp π 𝒰 s]
    rfl

lemma d_toCochainFun {p : ℕ} (x : Γ(cechTerm 𝒰 M p, ⊤)) :
    (OModulePresheaf.ofModules π M).d 𝒰 p (toCochainFun 𝒰 M x) =
      toCochainFun 𝒰 M ((cechD 𝒰 M p).app ⊤ x) := by
  funext t
  rw [toCochainFun_cechD]
  exact (OModulePresheaf.d_apply _ 𝒰 p _ t).trans rfl

/-- The `R`-module global sections of the `p`-th Čech term are the alternating Čech cochains. -/
def sectionsIso (p : ℕ) :
    (DerivedSections.relativeGlobalSections π).obj (cechTerm 𝒰 M p) ≅
      ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 p) :=
  (LinearEquiv.ofBijective (toCochain π 𝒰 M p)
    ⟨toCochainFun_injective 𝒰 M p, toCochainFun_surjective 𝒰 M p⟩).toModuleIso

/-- The complex of alternating Čech cochains of the FLT port, as an `ℕ`-indexed complex of
`R`-modules. -/
def cechCochainComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
    (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) (fun i => by
      apply ModuleCat.hom_ext
      exact OModulePresheaf.d_comp_d _ 𝒰 i)

/-- `R`-module global sections of the sheafified Čech complex are the Čech cochain complex. -/
def sectionsComplexIso :
    ((DerivedSections.relativeGlobalSections π).mapHomologicalComplex _).obj (cechComplex 𝒰 M) ≅
      cechCochainComplex π 𝒰 M :=
  HomologicalComplex.Hom.isoOfComponents (fun p => sectionsIso π 𝒰 M p) (by
    rintro p _ rfl
    rw [Functor.mapHomologicalComplex_obj_d]
    have h₁ : (cechComplex 𝒰 M).d p (p + 1) = cechD 𝒰 M p :=
      CochainComplex.of_d (cechTerm 𝒰 M) (cechD 𝒰 M) p
    have h₂ : (cechCochainComplex π 𝒰 M).d p (p + 1) =
        ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 p) :=
      CochainComplex.of_d (V := ModuleCat.{u} R)
        (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
        (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) p
    rw [h₁, h₂]
    ext x : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact d_toCochainFun π 𝒰 M x)

end Relative

section Derived

attribute [local instance] HasDerivedCategory.standard

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

/-- The Čech cochain complex of a quasi-coherent module on `X` separated over `Spec R` is
isomorphic, in the derived category of `R`-modules, to the actual right derived complex of
`R`-module global sections. -/
theorem nonempty_cechCochainComplex_iso (R : CommRingCat.{u}) (X : Scheme.{u})
    (π : X ⟶ Spec R) [IsSeparated π] (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] :
    Nonempty (DerivedCategory.Q.obj ((cechCochainComplex π 𝒰 M).extend
        ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex
        (DerivedSections.relativeGlobalSections π)).obj M)) := by
  let F := DerivedSections.relativeGlobalSections π
  have hK : ∀ i n : ℕ, IsZero ((F.rightDerived (n + 1)).obj ((cechComplex 𝒰 M).X i)) :=
    fun i n => isZero_relativeCohomology_cechTerm π 𝒰 M i n
  have := quasiIso_cechAug 𝒰 M
  have hiso := isIso_derivedResolutionComparison F (cechAug 𝒰 M) hK
  exact ⟨DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso (sectionsComplexIso π 𝒰 M).symm ≪≫
        (extendMapIso _ F _).symm) ≪≫ @asIso _ _ _ _ _ hiso⟩

end Derived

end Langlands.AlgebraicGeometry.Modules.CechResolution
