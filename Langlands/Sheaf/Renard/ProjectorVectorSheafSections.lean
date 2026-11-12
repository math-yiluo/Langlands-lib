import Langlands.Sheaf.Renard.ProjectorVectorSheaf
import Langlands.Sheaf.CompactSupport

/-!
# Sections of Renard's complex vector sheaf and the original-vector sections

Renard (9 July 2026), II.2.5, proof of the Theorem, printed pp.39–40 / PDF pp.45–46:
an explicit interface for sections of `ProjectorVectorSheaf.sheaf` as compatible projector
families, Renard's original-vector sections `m ↦ (χ_U · m)_U`, and their compactly supported
global version, the complex-linear core of the module-side comparison `M → ℳ_c(X)`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace Langlands.Sheaf.Renard.ProjectorVectorSheaf

open ProjectorBasisSheaf

section General

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)

section Sections

variable {M : Type (max u v)} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- A section over an actual open from a compatible family of projector values. -/
def sectionMk (V : Opens X)
    (s : ∀ U : BasisAllOpen.Inside (compactOpenBasis hX) V, Value hX M U.val)
    (hs : ∀ (U W : BasisAllOpen.Inside (compactOpenBasis hX) V)
      (h : W.val.obj ≤ U.val.obj), restrict hX M h (s U) = s W) :
    (presheaf hX hM).obj (op V) :=
  ⟨s, hs⟩

@[simp] theorem sectionMk_val (V : Opens X)
    (s : ∀ U : BasisAllOpen.Inside (compactOpenBasis hX) V, Value hX M U.val)
    (hs : ∀ (U W : BasisAllOpen.Inside (compactOpenBasis hX) V)
      (h : W.val.obj ≤ U.val.obj), restrict hX M h (s U) = s W)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    (sectionMk hX hM V s hs).val U = s U := rfl

/-- Sections over an actual open are determined by their original projector values. -/
theorem section_ext {V : Opens X} {s t : (presheaf hX hM).obj (op V)}
    (h : ∀ U : BasisAllOpen.Inside (compactOpenBasis hX) V, (s.val U).val = (t.val U).val) :
    s = t :=
  BasisAllOpen.families_ext fun U => Subtype.ext (h U)

/-- The components of every section are compatible under the original projectors. -/
theorem section_compatible {V : Opens X} (s : (presheaf hX hM).obj (op V))
    (U W : BasisAllOpen.Inside (compactOpenBasis hX) V) (h : W.val.obj ≤ U.val.obj) :
    restrict hX M h (s.val U) = s.val W :=
  s.property U W h

@[simp] theorem presheaf_map_val {U V : Opens X} (i : U ⟶ V)
    (s : (presheaf hX hM).obj (op V)) (W : BasisAllOpen.Inside (compactOpenBasis hX) U) :
    (((presheaf hX hM).map i.op).hom s).val W = s.val ⟨W.val, W.property.trans i.le⟩ :=
  rfl

@[simp] theorem presheaf_map_smul {U V : Opens X} (i : U ⟶ V) (c : ℂ)
    (s : (presheaf hX hM).obj (op V)) :
    ((presheaf hX hM).map i.op).hom (c • s) = c • ((presheaf hX hM).map i.op).hom s :=
  map_smul _ c s

theorem smul_val {V : Opens X} (c : ℂ) (s : (presheaf hX hM).obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((c • s).val U).val =
      @HSMul.hSMul ℂ M M (@instHSMul _ _ (originalModule hM).toSMul) c (s.val U).val :=
  rfl

end Sections

section Original

variable {M : Type (max u v)} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- Renard's section of an original vector: on each compact open `U ⊆ V` its value is
`χ_U · m`. -/
def originalFamily (V : Opens X) (m : M) : BasisAllOpen.Families.{u,v} (rawPresheaf hX M) V :=
  ⟨fun U => NonUnitalModuleCorner.projection (idempotent hX U.val) m,
    fun _ _ h => Subtype.ext (action_absorb hX M h m)⟩

@[simp] theorem originalFamily_val (V : Opens X) (m : M)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((originalFamily hX V m).val U).val = action hX M U.val m := rfl

/-- The original-vector section as a complex-linear map into sections over an actual open. -/
def originalSection (V : Opens X) :
    letI := originalModule hM
    M →ₗ[ℂ] (presheaf hX hM).obj (op V) :=
  letI := originalModule hM
  { toFun := originalFamily hX V
    map_add' := fun m n => section_ext hX hM fun U => (action hX M U.val).map_add m n
    map_smul' := fun c m => section_ext hX hM fun U =>
      action_smul_comm hM c (test hX U.val) m }

theorem originalSection_val (V : Opens X) (m : M)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    letI := originalModule hM
    ((originalSection hX hM V m).val U).val = action hX M U.val m := rfl

/-- Original-vector sections are compatible with restriction between actual opens. -/
theorem originalSection_restrict {U V : Opens X} (i : U ⟶ V) (m : M) :
    letI := originalModule hM
    ((presheaf hX hM).map i.op).hom (originalSection hX hM V m) =
      originalSection hX hM U m :=
  rfl

/-- On a compact open, the original-vector section of a vector already fixed by `χ_U` is
its section under `sectionLinearEquiv`. -/
theorem originalSection_of_value (U : CompactOpen hX) (s : Value hX M U) :
    letI := originalModule hM
    letI := valueModule hX hM U
    originalSection hX hM U.obj s.val = sectionLinearEquiv hX hM U s :=
  rfl

/-- On a compact open, reading the component at the open itself gives `χ_U · m`. -/
theorem sectionLinearEquiv_symm_originalSection (U : CompactOpen hX) (m : M) :
    letI := originalModule hM
    letI := valueModule hX hM U
    (sectionLinearEquiv hX hM U).symm (originalSection hX hM U.obj m) =
      NonUnitalModuleCorner.projection (idempotent hX U) m :=
  rfl

end Original

section Naturality

variable {M N : Type (max u v)} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)
  (hN : IsNondegenerate (PointwiseTestAlgebra.Carrier X) N)

/-- Original-vector sections are natural for original intertwiners. -/
theorem sheafMap_originalSection
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) (V : Opens X) (m : M) :
    letI := originalModule hM
    letI := originalModule hN
    ((sheafMap hX hM hN f).hom.app (op V)).hom (originalSection hX hM V m) =
      originalSection hX hN V (f m) :=
  section_ext hX hN fun U => f.map_smul (test hX U.val) m

end Naturality

end General

section CompactSupport

/-! The published `Langlands.Sheaf.CompactSupport` has one universe for the coefficients,
the space and the sections; with coefficients `ℂ` this is `Type`. -/

variable {X : Type} [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)
  {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)
  (hN : IsNondegenerate (PointwiseTestAlgebra.Carrier X) N)

include hM in
/-- Every original vector of a nondegenerate module is fixed by some compact-open test. -/
theorem exists_compactOpen_action_eq (m : M) : ∃ K : CompactOpen hX, action hX M K m = m := by
  obtain ⟨e, he⟩ := hM m
  let K : CompactOpen hX :=
    ⟨⟨Function.support (e : PointwiseTestAlgebra.Carrier X),
      (PointwiseTestAlgebra.isClopen_support _).isOpen⟩,
      PointwiseTestAlgebra.isCompact_support _⟩
  have hK : test hX K * (e : PointwiseTestAlgebra.Carrier X) = e :=
    (PointwiseTestAlgebra.characteristic_mul_eq_self_iff _ _ _).mpr subset_rfl
  refine ⟨K, ?_⟩
  change NonUnitalModuleCorner.originalAction (test hX K) m = m
  conv_lhs => rw [← he]
  change NonUnitalModuleCorner.originalAction (test hX K)
    (NonUnitalModuleCorner.originalAction (e : PointwiseTestAlgebra.Carrier X) m) = m
  rw [← NonUnitalModuleCorner.originalAction_mul, hK]
  exact he

/-- If `χ_K · m = m`, the original-vector global section is supported in `K`. -/
theorem support_originalSection_subset (K : CompactOpen hX) (m : M)
    (hK : action hX M K m = m) :
    letI := originalModule hM
    CompactSupport.support (X := TopCat.of X) (presheaf.{0,0} hX hM)
        (originalSection.{0,0} hX hM ⊤ m) ⊆ (K.obj : Set X) := by
  let _ := originalModule hM
  intro x hx
  by_contra hxK
  apply hx
  let W : Opens X := ⟨(K.obj : Set X)ᶜ, (clopen hX K).compl.isOpen⟩
  have hzero : originalSection.{0,0} hX hM W m = 0 := by
    apply section_ext hX hM
    intro U
    have hU : (interOpen hX U.val K).obj = ⊥ := by
      apply le_bot_iff.mp
      intro y hy
      exact absurd hy.2 (U.property hy.1)
    change action hX M U.val m = 0
    rw [← hK, action_mul]
    exact congrArg Subtype.val (empty_value_eq_zero hX M _ hU
      (NonUnitalModuleCorner.projection (idempotent hX (interOpen hX U.val K)) m))
  change (presheaf.{0,0} hX hM).Γgerm x (originalSection.{0,0} hX hM ⊤ m) = 0
  rw [← TopCat.Presheaf.Γgerm_res_apply (presheaf.{0,0} hX hM) (U := W) (i := homOfLE le_top) x
    (show x ∈ W from hxK)]
  erw [originalSection_restrict hX hM (homOfLE (le_top : W ≤ ⊤)) m, hzero]
  exact map_zero _

/-- The original-vector global section is compactly supported. -/
theorem originalSection_mem_submodule (m : M) :
    letI := originalModule hM
    originalSection.{0,0} hX hM ⊤ m ∈
      CompactSupport.submodule (X := TopCat.of X) (presheaf.{0,0} hX hM) := by
  obtain ⟨K, hK⟩ := exists_compactOpen_action_eq hX hM m
  exact (compact hX K).of_isClosed_subset (CompactSupport.isClosed_support _ _)
    (support_originalSection_subset hX hM K m hK)

/-- Renard's module-side comparison `m ↦ (χ_U · m)_U` into compactly supported sections. -/
def compactOriginal :
    letI := originalModule hM
    M →ₗ[ℂ] CompactSupport.submodule (X := TopCat.of X) (presheaf.{0,0} hX hM) :=
  letI := originalModule hM
  LinearMap.codRestrict _ (originalSection.{0,0} hX hM ⊤) (originalSection_mem_submodule hX hM)

theorem compactOriginal_val (m : M) :
    letI := originalModule hM
    (compactOriginal hX hM m).val = originalSection.{0,0} hX hM ⊤ m := rfl

theorem compactOriginal_component (m : M)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) ⊤) :
    letI := originalModule hM
    ((compactOriginal hX hM m).val.val U).val = action hX M U.val m := rfl

/-- The module-side comparison is natural for original intertwiners. -/
theorem compactOriginal_naturality
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) (m : M) :
    letI := originalModule hM
    letI := originalModule hN
    CompactSupport.map (X := TopCat.of X) (presheafMap.{0,0} hX hM hN f)
        (compactOriginal hX hM m) = compactOriginal hX hN (f m) :=
  Subtype.ext (sheafMap_originalSection.{0,0} hX hM hN f ⊤ m)

end CompactSupport

/-! Complete unapplied interface of the compactly supported comparison. -/

example : {X : Type} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M] →
    (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M) →
    letI := originalModule hM
    M →ₗ[ℂ] (CompactSupport.functor ℂ (TopCat.of X)).obj (sheaf.{0,0} hX hM) :=
  @compactOriginal

end Langlands.Sheaf.Renard.ProjectorVectorSheaf
