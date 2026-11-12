import Langlands.Sheaf.Renard.ProjectorVectorSheafSections
import Langlands.Sheaf.Renard.CompactSectionTestModule

/-!
# The original-module comparison with compact sections of the projector sheaf

Renard (9 July 2026), II.2.5, end of the proof of the Theorem, printed p.40 / PDF p.46:
for a nondegenerate `D(X)`-module `M` with sheaf `M(U) = χ_U · M`, one has
`M_c(X) = ⋃_U χ_U · M = M`. The comparison sends `m` to the compactly supported global
section with components `χ_U · m`.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.ModuleProjectorComparison

open CategoryTheory TopologicalSpace Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.ProjectorBasisSheaf Langlands.Sheaf.Renard.ProjectorVectorSheaf
open Langlands.Sheaf.Renard.CompactSectionTestModule

variable {X : Type} [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)

/-- A compact open neighborhood of `x` on which the test function `f` is constant. -/
theorem exists_compactOpen_eq (f : PointwiseTestAlgebra.Carrier X) (x : X) :
    ∃ W : CompactOpen hX, x ∈ W.obj ∧ ∀ y ∈ W.obj, f y = f x := by
  have ho : IsOpen {y | f y = f x} :=
    (PointwiseTestAlgebra.locallyConstant f).isOpen_fiber (f x)
  obtain ⟨V, hxV, hVo, hVc, hVsub⟩ := hX.2 x _ (ho.mem_nhds rfl)
  exact ⟨⟨⟨V, hVo⟩, hVc⟩, hxV, fun y hy => hVsub hy⟩

/-- `χ_U f = c χ_U` when `U` lies in a set where `f` is constant `c`. -/
theorem test_mul_eq {W : CompactOpen hX} (f : PointwiseTestAlgebra.Carrier X) (c : ℂ)
    (hf : ∀ y ∈ W.obj, f y = c) {U : CompactOpen hX} (hU : U.obj ≤ W.obj) :
    test hX U * f = c • test hX U := by
  ext y
  rw [PointwiseTestAlgebra.mul_apply, PointwiseTestAlgebra.smul_apply]
  change (U.obj : Set X).indicator (fun _ => (1 : ℂ)) y * f y =
    c • (U.obj : Set X).indicator (fun _ => (1 : ℂ)) y
  by_cases hy : y ∈ (U.obj : Set X)
  · rw [Set.indicator_of_mem hy, one_mul, hf y (hU hy), smul_eq_mul, mul_one]
  · rw [Set.indicator_of_notMem hy, zero_mul, smul_zero]

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- On a compact open where `f` is constant `c`, the section of `f • m` is `c` times that
of `m`, for the canonical complex structure. -/
theorem originalSection_test_smul {W : CompactOpen hX} (f : PointwiseTestAlgebra.Carrier X)
    (c : ℂ) (hf : ∀ y ∈ W.obj, f y = c) (m : M) :
    letI := originalModule hM
    originalSection.{0, 0} hX hM W.obj (f • m) = c • originalSection.{0, 0} hX hM W.obj m := by
  let _ := originalModule hM
  apply section_ext hX hM
  intro U
  rw [smul_val]
  change NonUnitalModuleCorner.originalAction (test hX U.val)
      (NonUnitalModuleCorner.originalAction f m) =
    c • NonUnitalModuleCorner.originalAction (test hX U.val) m
  rw [← NonUnitalModuleCorner.originalAction_mul, test_mul_eq hX f c hf U.property]
  exact (NondegenerateScalars.smul_action ℂ PointwiseTestAlgebra.isIdempotented hM c _ m).symm

/-- The germ formula `(f m)_x = f(x) m_x` for original-vector global sections. -/
theorem Γgerm_originalSection_test_smul (f : PointwiseTestAlgebra.Carrier X) (m : M) (x : X) :
    letI := originalModule hM
    (presheaf.{0, 0} hX hM).Γgerm x (originalSection.{0, 0} hX hM ⊤ (f • m)) =
      f x • (presheaf.{0, 0} hX hM).Γgerm x (originalSection.{0, 0} hX hM ⊤ m) := by
  let _ := originalModule hM
  obtain ⟨W, hxW, hf⟩ := exists_compactOpen_eq hX f x
  have h (s : (presheaf.{0, 0} hX hM).obj (op ⊤)) :
      (presheaf.{0, 0} hX hM).Γgerm x s = (presheaf.{0, 0} hX hM).germ W.obj x hxW
        ((presheaf.{0, 0} hX hM).map (homOfLE (le_top : W.obj ≤ ⊤)).op s) :=
    (TopCat.Presheaf.Γgerm_res_apply _ x hxW s).symm
  rw [h, h]
  erw [originalSection_restrict hX hM (homOfLE (le_top : W.obj ≤ ⊤)) (f • m),
    originalSection_restrict hX hM (homOfLE (le_top : W.obj ≤ ⊤)) m]
  rw [originalSection_test_smul hX hM f (f x) hf m, map_smul]

/-- The published `compactOriginal` intertwines the original test action with the test
action on compact sections of the projector sheaf. -/
theorem compactOriginal_test_smul (f : PointwiseTestAlgebra.Carrier X) (m : M) :
    letI := originalModule hM
    compactOriginal hX hM (f • m) = testSmul (sheaf.{0, 0} hX hM) f (compactOriginal hX hM m) := by
  let _ := originalModule hM
  apply Subtype.ext
  apply VectorSheafScalars.ext_germ (sheaf.{0, 0} hX hM)
  intro x _
  exact (Γgerm_originalSection_test_smul hX hM f m x).trans
    (VectorSheafScalars.germ_smul (sheaf.{0, 0} hX hM) (testScalar f)
      (compactOriginal hX hM m).1 x trivial).symm

/-- The module-side comparison as an original test-module map `M → Γc(P M)`. -/
def moduleComparisonHom (M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) :
    NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M.obj
      (CompactSupport.submodule (sheaf.{0, 0} hX M.property).presheaf) where
  toAddMonoidHom :=
    letI := originalModule M.property
    (compactOriginal hX M.property).toAddMonoidHom
  map_smul' f m := compactOriginal_test_smul hX M.property f m

@[simp]
theorem moduleComparisonHom_component
    (M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) (m : M.obj)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) ⊤) :
    ((moduleComparisonHom hX M m).val.val U).val = action hX M.obj U.val m := rfl

/-- Renard II.2.5, end of the proof: the original-module comparison
`M ⟶ Γc(P M)`, `m ↦ (χ_U · m)_U`, as a morphism of nondegenerate test modules. -/
def moduleComparison (M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) :
    M ⟶ (ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX).obj M :=
  ObjectProperty.homMk (moduleComparisonHom hX M)

theorem moduleComparison_hom
    (M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) :
    (moduleComparison hX M).hom = moduleComparisonHom hX M := rfl

/-- Naturality of the original-module comparison. -/
def moduleComparisonNat :
    𝟭 (NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) ⟶
      ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX where
  app M := moduleComparison hX M
  naturality M N g := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact (compactOriginal_naturality hX M.property N.property g.hom m).symm

end Langlands.Sheaf.Renard.ModuleProjectorComparison
