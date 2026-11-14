import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso

/-!
# Ordered Čech cochains over all tuples compute actual cohomology

Let `π : X ⟶ Spec R` be separated, `U : ι → X.Opens` a finite covering family of affine opens
and `M` a quasi-coherent `𝒪_X`-module. The `R`-module global sections of the sheafified ordered
Čech complex `AllSeq.complex U M` are the ordered Čech cochains `AllSeq.cochain π U M p`, the
families `σ ↦ c σ ∈ M(inter U σ)` indexed by all maps `σ : Fin (p + 1) → ι`. Its terms are
acyclic, so the cohomology of the ordered cochain complex is the actual `R`-module cohomology
`(relativeCohomology π n).obj M` (`AllSeq.cohomologyIso`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
  Langlands.AlgebraicGeometry.Modules.DerivedSections

section Acyclic

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  {ι : Type u} {U : ι → X.Opens}

include π in
/-- Over a separated base, every finite intersection of a family of affine opens is affine. -/
lemma isAffineOpen_inter (hAff : ∀ i, IsAffineOpen (U i)) {p : ℕ} (σ : Fin (p + 1) → ι) :
    IsAffineOpen (inter U σ) :=
  InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
    (fun _ h _ h' => isAffineOpen_inf π h h') (fun j => hAff (σ j))

variable [Fintype ι]

/-- The terms of the sheafified ordered Čech complex of a quasi-coherent module are acyclic for
`R`-module global sections. -/
theorem isZero_relativeCohomology_term (hAff : ∀ i, IsAffineOpen (U i)) (M : X.Modules)
    [M.IsQuasicoherent] (p n : ℕ) :
    IsZero ((relativeCohomology π (n + 1)).obj (term U M p)) :=
  haveI : (relativeCohomology π (n + 1)).Additive :=
    rightDerived_additive (relativeGlobalSections π) (n + 1)
  isZero_obj_biproduct _ _ fun σ =>
    isZero_relativeCohomology_sheafOn π M (isAffineOpen_inter π hAff σ) n

end Acyclic

section Sections

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι] (U : ι → X.Opens) (M : X.Modules)

omit [Fintype ι] in
lemma inter_le_secOpen {p : ℕ} (σ : Fin (p + 1) → ι) : inter U σ ≤ secOpen U σ ⊤ := by
  rw [secOpen_eq, inf_top_eq]

omit [Fintype ι] in
lemma secOpen_le_inter {p : ℕ} (σ : Fin (p + 1) → ι) : secOpen U σ ⊤ ≤ inter U σ := by
  rw [secOpen_eq, inf_top_eq]

/-- The global sections of the `p`-th term as a family of sections of `M` over the opens
`inter U σ`. -/
def toCochainFun {p : ℕ} (x : Γ(term U M p, ⊤)) (σ : Fin (p + 1) → ι) : Γ(M, inter U σ) :=
  cr (toSec ⊤ x) σ (inter_le_secOpen U σ)

lemma toCochainFun_injective (p : ℕ) :
    Function.Injective (fun x : Γ(term U M p, ⊤) => toCochainFun U M x) := by
  intro x y h
  refine toSec_injective ⊤ (funext fun σ => ?_)
  have hs : M.presheaf.map (homOfLE (inter_le_secOpen U σ)).op (toSec ⊤ x σ) =
      M.presheaf.map (homOfLE (inter_le_secOpen U σ)).op (toSec ⊤ y σ) := congrFun h σ
  rw [← map_map_of_le_of_le (secOpen_le_inter U σ) (inter_le_secOpen U σ) (toSec ⊤ x σ), hs,
    map_map_of_le_of_le]

lemma toCochainFun_surjective (p : ℕ) :
    Function.Surjective (fun x : Γ(term U M p, ⊤) => toCochainFun U M x) := by
  intro c
  obtain ⟨x, hx⟩ := toSec_surjective (U := U) (M := M) (p := p) ⊤
    (fun σ => M.presheaf.map (homOfLE (secOpen_le_inter U σ)).op (c σ))
  refine ⟨x, funext fun σ => ?_⟩
  change M.presheaf.map (homOfLE (inter_le_secOpen U σ)).op (toSec ⊤ x σ) = c σ
  rw [hx]
  exact map_map_of_le_of_le _ _ (c σ)

lemma toCochainFun_d {p : ℕ} (x : Γ(term U M p, ⊤)) (τ : Fin (p + 2) → ι) :
    toCochainFun U M ((d U M p).app ⊤ x) τ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        M.presheaf.map (homOfLE (inter_le_comp τ j.succAbove)).op
          (toCochainFun U M x (τ ∘ j.succAbove)) := by
  simp only [toCochainFun, cr_def]
  rw [toSec_d]
  simp only [dSec, map_sum, map_zsmul, cr_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    ← M.presheaf.map_comp]
  rfl

lemma toCochainFun_add {p : ℕ} (x y : Γ(term U M p, ⊤)) :
    toCochainFun U M (x + y) = toCochainFun U M x + toCochainFun U M y := by
  funext σ
  simp only [toCochainFun, cr_def, toSec, map_add, Pi.add_apply]
  exact map_add _ _ _

lemma toCochainFun_smul {p : ℕ} (r : Γ(X, ⊤)) (x : Γ(term U M p, ⊤)) (σ : Fin (p + 1) → ι) :
    toCochainFun U M (r • x) σ =
      X.presheaf.map (homOfLE (inter_le_secOpen U σ)).op
          (((inter U σ).ι.app ⊤ ≫ ((inter U σ).ι.appIso ((inter U σ).ι ⁻¹ᵁ ⊤)).inv) r) •
        toCochainFun U M x σ := by
  have h : (biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) σ).app ⊤ (r • x) =
      r • (biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) σ).app ⊤ x :=
    Scheme.Modules.Hom.app_smul _ r x
  simp only [toCochainFun, cr_def, toSec]
  rw [h, smul_eq]
  exact Scheme.Modules.map_smul M _ _ _

end Sections

section Relative

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (M : X.Modules)

omit [Fintype ι] in
lemma structureRingHom_comp_inter {p : ℕ} (σ : Fin (p + 1) → ι) :
    structureRingHom π ≫
        ((inter U σ).ι.app ⊤ ≫ ((inter U σ).ι.appIso ((inter U σ).ι ⁻¹ᵁ ⊤)).inv) ≫
          X.presheaf.map (homOfLE (inter_le_secOpen U σ)).op =
      (Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ (inter U σ) le_top := by
  rw [Scheme.Hom.app_appIso_inv]
  simp only [structureRingHom, Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact (X.presheaf.map_comp _ _).symm

/-- Ordered Čech `p`-cochains of `M` over all tuples, as an `R`-module: families
`σ ↦ c σ ∈ M(inter U σ)` with the `R`-module structure of `OModulePresheaf.ofModules π M`. -/
abbrev cochain (p : ℕ) : Type u :=
  ∀ σ : Fin (p + 1) → ι, (OModulePresheaf.ofModules π M).obj (inter U σ)

/-- The ordered Čech differential on `R`-module cochains. -/
def dCochain (p : ℕ) : cochain π U M p →ₗ[R] cochain π U M (p + 1) :=
  LinearMap.pi fun τ => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((OModulePresheaf.ofModules π M).res (inter_le_comp τ j.succAbove)).comp
      (LinearMap.proj (τ ∘ j.succAbove))

omit [Fintype ι] in
lemma dCochain_apply (p : ℕ) (c : cochain π U M p) (τ : Fin (p + 2) → ι) :
    dCochain π U M p c τ = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (OModulePresheaf.ofModules π M).res (inter_le_comp τ j.succAbove) (c (τ ∘ j.succAbove)) := by
  simp only [dCochain, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- The `R`-linear map from the `R`-module global sections of the `p`-th term to ordered
cochains. -/
def toCochain (p : ℕ) : (relativeGlobalSections π).obj (term U M p) →ₗ[R] cochain π U M p where
  toFun x := toCochainFun U M x
  map_add' x y := toCochainFun_add U M x y
  map_smul' r x := by
    funext σ
    rw [relativeGlobalSections_smul]
    refine (toCochainFun_smul U M _ x σ).trans ?_
    change _ = ((Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ (inter U σ) le_top).hom r •
      toCochainFun U M x σ
    rw [← structureRingHom_comp_inter π U σ]
    rfl

lemma dCochain_toCochainFun {p : ℕ} (x : Γ(term U M p, ⊤)) :
    dCochain π U M p (toCochainFun U M x) = toCochainFun U M ((d U M p).app ⊤ x) := by
  funext τ
  refine (dCochain_apply π U M p _ τ).trans ?_
  rw [toCochainFun_d]
  rfl

lemma dCochain_comp_dCochain (p : ℕ) :
    (dCochain π U M (p + 1)).comp (dCochain π U M p) = 0 := by
  ext c : 1
  obtain ⟨x, rfl⟩ := toCochainFun_surjective U M p c
  change dCochain π U M (p + 1) (dCochain π U M p (toCochainFun U M x)) = 0
  rw [dCochain_toCochainFun, dCochain_toCochainFun]
  have h := congrArg (fun f => f.app ⊤ x) (d_comp_d U M p)
  simp only [comp_app_apply] at h
  rw [h]
  exact (toCochain π U M (p + 1 + 1)).map_zero

/-- The `R`-module global sections of the `p`-th term are the ordered cochains. -/
def sectionsIso (p : ℕ) :
    (relativeGlobalSections π).obj (term U M p) ≅ ModuleCat.of R (cochain π U M p) :=
  (LinearEquiv.ofBijective (toCochain π U M p)
    ⟨toCochainFun_injective U M p, toCochainFun_surjective U M p⟩).toModuleIso

/-- The complex of ordered Čech cochains of `M` over all tuples, as an `ℕ`-indexed complex of
`R`-modules. -/
def cochainComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (cochain π U M p))
    (fun p => ModuleCat.ofHom (dCochain π U M p)) (fun p => by
      apply ModuleCat.hom_ext
      exact dCochain_comp_dCochain π U M p)

lemma cochainComplex_d (p : ℕ) :
    (cochainComplex π U M).d p (p + 1) = ModuleCat.ofHom (dCochain π U M p) :=
  CochainComplex.of_d (V := ModuleCat.{u} R) (fun p => ModuleCat.of R (cochain π U M p))
    (fun p => ModuleCat.ofHom (dCochain π U M p)) p

/-- `R`-module global sections of the sheafified ordered Čech complex are the ordered cochain
complex. -/
def sectionsComplexIso :
    ((relativeGlobalSections π).mapHomologicalComplex _).obj (complex U M) ≅
      cochainComplex π U M :=
  HomologicalComplex.Hom.isoOfComponents (fun p => sectionsIso π U M p) (by
    rintro p _ rfl
    rw [Functor.mapHomologicalComplex_obj_d]
    have h₁ : (complex U M).d p (p + 1) = d U M p :=
      CochainComplex.of_d (term U M) (d U M) p
    rw [h₁, cochainComplex_d]
    ext x : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact dCochain_toCochainFun π U M x)

end Relative

section CohomologyIso

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  {ι : Type u} [Fintype ι] (U : ι → X.Opens) (M : X.Modules) [M.IsQuasicoherent]
  (hU : ⨆ i, U i = ⊤) (hAff : ∀ i, IsAffineOpen (U i))

include hAff in
/-- The comparison map from the ordered Čech resolution to the actual right derived functors
of `R`-module global sections is an isomorphism in every degree. -/
theorem isIso_resolutionComparison_aug (n : ℕ) :
    haveI := quasiIso_aug U M hU
    IsIso (resolutionComparison (relativeGlobalSections π) (aug U M) n) := by
  have := quasiIso_aug U M hU
  exact (acyclicResolutionComparisonStatement _ _ (relativeGlobalSections π) M
    (complex U M) (aug U M) inferInstance
    (fun i n => isZero_relativeCohomology_term π hAff M i n) (injectiveResolution M) _
    (comp_lift_id _ _)).2 n

/-- The cohomology of the ordered Čech cochain complex over all tuples of a quasi-coherent
module on a scheme separated over `Spec R`, for a finite covering family of affine opens, is
its actual `R`-module cohomology. -/
def cohomologyIso (n : ℕ) :
    (cochainComplex π U M).homology n ≅ (relativeCohomology π n).obj M :=
  haveI := quasiIso_aug U M hU
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (sectionsComplexIso π U M).symm ≪≫
    @asIso _ _ _ _ _ (isIso_resolutionComparison_aug π U M hU hAff n)

end CohomologyIso

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
