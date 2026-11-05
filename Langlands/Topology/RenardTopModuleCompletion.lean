import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Category.UniformSpace

/-!
# Actual separated completion of topological modules

This is the corrected continuous-linear convention for Renard A.III.1 example 2,
with an internal generalization from topological fields to topological rings.
The printed category with all continuous maps remains a separate question.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory UniformSpace

universe u v w

namespace Langlands.Renard.TopModuleCompletion

/-- The canonical additive uniformity, retaining the given topology. -/
abbrev canonicalUniformSpace (M : Type v) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] : UniformSpace M :=
  IsTopologicalAddGroup.rightUniformSpace M

theorem canonicalUniformSpace_topology (M : Type v) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] :
    (canonicalUniformSpace M).toTopologicalSpace = (inferInstance : TopologicalSpace M) :=
  rfl

variable (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

local instance ambientUniformSpace (M : TopModuleCat.{v} R) : UniformSpace M :=
  canonicalUniformSpace M

local instance ambientUniformAddGroup (M : TopModuleCat.{v} R) : IsUniformAddGroup M :=
  isUniformAddGroup_of_addCommGroup

local instance ambientUniformConstSMul (M : TopModuleCat.{v} R) :
    UniformContinuousConstSMul R M :=
  uniformContinuousConstSMul_of_continuousConstSMul R M

omit [IsTopologicalRing R] in
/-- Actual continuous linear maps are uniformly continuous for the canonical uniformities. -/
theorem uniformContinuous_hom {M N : TopModuleCat.{v} R} (f : M ⟶ N) :
    UniformContinuous f.hom :=
  f.hom.uniformContinuous

/-- Forget to the canonical additive uniform space, retaining the actual maps. -/
def forgetToUniformSpace : TopModuleCat.{v} R ⥤ UniformSpaceCat.{v} where
  obj M := UniformSpaceCat.of M
  map f := UniformSpaceCat.ofHom ⟨f.hom, uniformContinuous_hom R f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Selection by completeness for the canonical uniformity and by separation alone. -/
def completeSeparatedProperty : ObjectProperty (TopModuleCat.{v} R) :=
  fun M => CompleteSpace M ∧ T0Space M

/-- The full subcategory with every continuous linear map between its objects. -/
abbrev CompleteSepModuleCat :=
  (completeSeparatedProperty.{u, v} R).FullSubcategory

/-- The actual full-subcategory inclusion. -/
abbrev inclusion : CompleteSepModuleCat.{u, v} R ⥤ TopModuleCat.{v} R :=
  (completeSeparatedProperty.{u, v} R).ι

abbrev inclusionFullyFaithful : (inclusion.{u, v} R).FullyFaithful :=
  (completeSeparatedProperty.{u, v} R).fullyFaithfulι

local instance completeSpace (N : CompleteSepModuleCat.{u, v} R) :
    CompleteSpace N.obj :=
  N.property.1

local instance separatedSpace (N : CompleteSepModuleCat.{u, v} R) : T0Space N.obj :=
  N.property.2

/-- Forget the module structure of a complete separated object. -/
def forgetCompleteToUniformSpace :
    CompleteSepModuleCat.{u, v} R ⥤ CpltSepUniformSpace.{v} where
  obj N := CpltSepUniformSpace.of N.obj
  map f := ConcreteCategory.ofHom
    ⟨f.hom.hom, uniformContinuous_hom R f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

omit [IsTopologicalRing R] in
/-- The inclusion square commutes strictly. -/
theorem inclusion_square :
    forgetCompleteToUniformSpace.{u, v} R ⋙
        forget₂ CpltSepUniformSpace UniformSpaceCat =
      inclusion R ⋙ forgetToUniformSpace R :=
  rfl

/-- Joint continuity of the existing scalar action on the actual completion.
The proof extends the original biadditive scalar map along `id × toCompl`. -/
theorem completionContinuousSMul (M : TopModuleCat.{v} R) :
    ContinuousSMul R (Completion M) := by
  let m : R →+ M →+ Completion M :=
    (smulAddHom R M).compr₂ Completion.toCompl
  have hm : Continuous (fun p : R × M => m p.1 p.2) :=
    (Completion.continuous_coe M).comp continuous_smul
  have de : IsDenseInducing (AddMonoidHom.id R : R → R) :=
    ⟨Topology.IsInducing.id, denseRange_id⟩
  have df : IsDenseInducing (Completion.toCompl : M → Completion M) :=
    Completion.isDenseInducing_toCompl M
  have hc := de.extend_Z_bilin df hm
  let h : R × Completion M → Completion M :=
    (de.prodMap df).extend (fun p : R × M => m p.1 p.2)
  have hh : Continuous h := hc
  have heq : (fun p : R × Completion M => p.1 • p.2) = h := by
    funext p
    apply Completion.ext' (continuous_const_smul p.1)
      (hh.comp (continuous_const.prodMk continuous_id)) ?_ p.2
    intro x
    change p.1 • (x : Completion M) = h (p.1, x)
    rw [← Completion.coe_smul]
    exact ((de.prodMap df).extend_eq hm (p.1, x)).symm
  exact ⟨heq ▸ hh⟩

attribute [local instance] completionContinuousSMul

omit [IsTopologicalRing R] in
/-- The completion keeps Mathlib's existing uniformity; it is the canonical
additive uniformity of the resulting topology. -/
theorem completion_uniformSpace_eq (M : TopModuleCat.{v} R) :
    canonicalUniformSpace (Completion M) =
      (inferInstance : UniformSpace (Completion M)) :=
  IsUniformAddGroup.rightUniformSpace_eq

/-- The actual completion as a topological module, using its existing operations. -/
def completionTopModule (M : TopModuleCat.{v} R) : TopModuleCat.{v} R :=
  letI := completionContinuousSMul R M
  TopModuleCat.of R (Completion M)

/-- The same actual completion selected by completeness and separation. -/
def completionObject (M : TopModuleCat.{v} R) : CompleteSepModuleCat.{u, v} R :=
  ⟨completionTopModule R M, by
    constructor
    · change @CompleteSpace (Completion M) (canonicalUniformSpace (Completion M))
      rw [completion_uniformSpace_eq R M]
      infer_instance
    · change T0Space (Completion M)
      infer_instance⟩

/-- The completed morphism is Mathlib's completion of the actual continuous linear map. -/
def completionMap {M N : TopModuleCat.{v} R} (f : M ⟶ N) :
    completionObject R M ⟶ completionObject R N :=
  ObjectProperty.homMk <| TopModuleCat.ofHom f.hom.completion

/-- The underlying completed map is exactly `Completion.map`. -/
theorem completionMap_apply {M N : TopModuleCat.{v} R} (f : M ⟶ N)
    (z : Completion M) :
    (completionMap R f).hom.hom z = Completion.map (f.hom : M → N) z :=
  rfl

/-- Completion is a functor with the actual completed morphisms. -/
def completionFunctor : TopModuleCat.{v} R ⥤ CompleteSepModuleCat.{u, v} R where
  obj := completionObject R
  map f := completionMap R f
  map_id M := by
    apply ObjectProperty.hom_ext
    ext z
    change Completion.map (id : M → M) z = z
    exact congr_fun (Completion.map_id (α := M)) z
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext z
    change Completion.map (g.hom ∘ f.hom) z =
      Completion.map g.hom (Completion.map f.hom z)
    exact congr_fun (Completion.map_comp (uniformContinuous_hom R g)
      (uniformContinuous_hom R f)).symm z

/-- The continuous linear canonical map, without separation of the source. -/
def canonicalMap (M : TopModuleCat.{v} R) :
    M ⟶ (inclusion R).obj (completionObject R M) :=
  TopModuleCat.ofHom Completion.toComplL

@[simp] theorem canonicalMap_apply (M : TopModuleCat.{v} R) (x : M) :
    (canonicalMap R M).hom x = (x : Completion M) :=
  rfl

/-- The chosen canonical maps form a natural transformation. -/
def canonicalNatTrans :
    𝟭 (TopModuleCat.{v} R) ⟶ completionFunctor R ⋙ inclusion R where
  app := canonicalMap R
  naturality {M N} f := by
    ext x
    exact (ContinuousLinearMap.completion_apply_coe f.hom x).symm

/-- Chosen extension to a complete separated target in the same universe. -/
def extensionHom (M : TopModuleCat.{v} R) (N : CompleteSepModuleCat.{u, v} R)
    (f : M ⟶ N.obj) : completionObject R M ⟶ N :=
  ObjectProperty.homMk <| TopModuleCat.ofHom f.hom.fromCompletion

theorem extensionHom_apply (M : TopModuleCat.{v} R)
    (N : CompleteSepModuleCat.{u, v} R) (f : M ⟶ N.obj) (z : Completion M) :
    (extensionHom R M N f).hom.hom z =
      Completion.extension (f.hom : M → N.obj) z :=
  rfl

@[simp] theorem extensionHom_coe (M : TopModuleCat.{v} R)
    (N : CompleteSepModuleCat.{u, v} R) (f : M ⟶ N.obj) (x : M) :
    (extensionHom R M N f).hom.hom (x : Completion M) = f.hom x :=
  ContinuousLinearMap.fromCompletion_apply_coe f.hom x

/-- The comparison is the identity on the actual completion carrier.
Its two uniform structures agree by `completion_uniformSpace_eq`. -/
def completionUniformIso (M : TopModuleCat.{v} R) :
    (forgetCompleteToUniformSpace R).obj (completionObject R M) ≅
      UniformSpaceCat.completionFunctor.obj ((forgetToUniformSpace R).obj M) where
  hom := ConcreteCategory.ofHom ⟨id, by
    change @UniformContinuous (Completion M) (Completion M)
      (canonicalUniformSpace (Completion M)) _ id
    rw [completion_uniformSpace_eq R M]
    exact uniformContinuous_id⟩
  inv := ConcreteCategory.ofHom ⟨id, by
    change @UniformContinuous (Completion M) (Completion M)
      _ (canonicalUniformSpace (Completion M)) id
    rw [completion_uniformSpace_eq R M]
    exact uniformContinuous_id⟩
  hom_inv_id := by
    apply InducedCategory.hom_ext
    ext z
    rfl
  inv_hom_id := by
    apply InducedCategory.hom_ext
    ext z
    rfl

@[simp] theorem completionUniformIso_hom_apply (M : TopModuleCat.{v} R)
    (z : Completion M) :
    (completionUniformIso R M).hom z = z :=
  rfl

@[simp] theorem completionUniformIso_inv_apply (M : TopModuleCat.{v} R)
    (z : Completion M) :
    (completionUniformIso R M).inv z = z :=
  rfl

/-- The completion-functor square commutes through the specified identity maps. -/
def completionUniformComparison :
    completionFunctor.{u, v} R ⋙ forgetCompleteToUniformSpace R ≅
      forgetToUniformSpace R ⋙ UniformSpaceCat.completionFunctor :=
  NatIso.ofComponents (completionUniformIso R) (by
    intro M N f
    apply InducedCategory.hom_ext
    ext z
    rfl)

/-- Under the comparison, the canonical map is Mathlib's `completionHom`. -/
theorem canonicalMap_uniform (M : TopModuleCat.{v} R) :
    (forgetToUniformSpace R).map (canonicalMap R M) ≫
        (forget₂ CpltSepUniformSpace UniformSpaceCat).map (completionUniformIso R M).hom =
      UniformSpaceCat.completionHom ((forgetToUniformSpace R).obj M) := by
  ext x
  rfl

/-- The actual completed morphisms agree with Mathlib's uniform-space functor. -/
theorem completionMap_uniform {M N : TopModuleCat.{v} R} (f : M ⟶ N) :
    (forgetCompleteToUniformSpace R).map (completionMap R f) ≫
        (completionUniformIso R N).hom =
      (completionUniformIso R M).hom ≫
        UniformSpaceCat.completionFunctor.map ((forgetToUniformSpace R).map f) := by
  apply InducedCategory.hom_ext
  ext z
  rfl

theorem completionMap_uniform_apply {M N : TopModuleCat.{v} R} (f : M ⟶ N)
    (z : Completion M) :
    (completionMap R f).hom.hom z =
      (UniformSpaceCat.completionFunctor.map ((forgetToUniformSpace R).map f)) z :=
  rfl

/-- The actual extension agrees with Mathlib's `extensionHom` under the comparison. -/
theorem extensionHom_uniform (M : TopModuleCat.{v} R)
    (N : CompleteSepModuleCat.{u, v} R) (f : M ⟶ N.obj) :
    (completionUniformIso R M).inv ≫
        (forgetCompleteToUniformSpace R).map (extensionHom R M N f) =
      UniformSpaceCat.extensionHom
        (Y := (forgetCompleteToUniformSpace R).obj N)
        ((forgetToUniformSpace R).map f) := by
  apply InducedCategory.hom_ext
  ext z
  rfl

theorem extensionHom_uniform_apply (M : TopModuleCat.{v} R)
    (N : CompleteSepModuleCat.{u, v} R) (f : M ⟶ N.obj) (z : Completion M) :
    (extensionHom R M N f).hom.hom z =
      (UniformSpaceCat.extensionHom
        (Y := (forgetCompleteToUniformSpace R).obj N)
        ((forgetToUniformSpace R).map f)) z :=
  rfl

section Concrete

variable (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]
variable (N : Type w) [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousSMul R N]

local instance : UniformSpace M := canonicalUniformSpace M
local instance : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul R M :=
  uniformContinuousConstSMul_of_continuousConstSMul R M
local instance : UniformSpace N := canonicalUniformSpace N
local instance : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul R N :=
  uniformContinuousConstSMul_of_continuousConstSMul R N

variable [CompleteSpace N] [T0Space N]

omit [IsTopologicalRing R]

/-- The concrete extension, with coefficient, source and target universes independent.
Completeness of `N` is for `canonicalUniformSpace N`. -/
def concreteExtension (f : M →L[R] N) : Completion M →L[R] N :=
  f.fromCompletion

theorem concreteExtension_toFun (f : M →L[R] N) :
    (concreteExtension R M N f : Completion M → N) =
      Completion.extension (f : M → N) :=
  rfl

@[simp] theorem concreteExtension_coe (f : M →L[R] N) (x : M) :
    concreteExtension R M N f (x : Completion M) = f x :=
  ContinuousLinearMap.fromCompletion_apply_coe f x

end Concrete

section Field

variable (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]

/-- Exact specialization of the selected category to a topological field. -/
abbrev CompleteSepVectCat := CompleteSepModuleCat.{u, v} k

/-- Exact topological-field specialization, with arbitrary carrier universe. -/
abbrev fieldCompletionFunctor :
    TopModuleCat.{v} k ⥤ CompleteSepVectCat.{u, v} k :=
  completionFunctor k

/-- The same canonical natural transformation over each topological field. -/
abbrev fieldCanonicalNatTrans :
    𝟭 (TopModuleCat.{v} k) ⟶ fieldCompletionFunctor k ⋙ inclusion k :=
  canonicalNatTrans k

/-- The same categorical continuous-linear extension over each topological field. -/
abbrev fieldExtensionHom (M : TopModuleCat.{v} k)
    (N : CompleteSepVectCat.{u, v} k) (f : M ⟶ N.obj) :
    (fieldCompletionFunctor k).obj M ⟶ N :=
  extensionHom k M N f

/-- Exact field specialization of the concrete extension in independent universes. -/
abbrev fieldConcreteExtension (M : Type v) [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]
    (N : Type w) [AddCommGroup N] [Module k N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul k N]
    [@CompleteSpace N (canonicalUniformSpace N)] [T0Space N] (f : M →L[k] N) :=
  concreteExtension k M N f

end Field

end Langlands.Renard.TopModuleCompletion
