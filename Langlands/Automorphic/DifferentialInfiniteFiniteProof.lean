import Langlands.Automorphic.PreservationStatement
import Langlands.Automorphic.RealDifferentialCovarianceProof
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Finite-dimensional images of genuine differential operators -/

noncomputable section
universe u uk ug ue uv
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.FiniteVectors

variable {k : Type uk} [Field k] {G : Type ug} [Monoid G]
  {E : Type ue} [AddCommGroup E] [Module k E] [Module.Finite k E]
  {V : Type uv} [AddCommGroup V] [Module k V]

/-- A finite-dimensional family of operators takes a finite vector to a finite
vector when its translated values remain in that family applied to the orbit. -/
theorem isFiniteVector_bilinear_of_covariance
    (ρ : Representation k G V) (D : E →ₗ[k] Module.End k V)
    (X : E) {v : V} (hv : IsFiniteVector ρ v)
    (hcov : ∀ g : G, ∃ Y : E, ρ g (D X v) = D Y (ρ g v)) :
    IsFiniteVector ρ (D X v) := by
  let S := orbitSpan ρ v
  have : Module.Finite k S := hv
  let B : E →ₗ[k] S →ₗ[k] V :=
    { toFun := fun Y => (D Y).comp S.subtype
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let T : E ⊗[k] S →ₗ[k] V := TensorProduct.lift B
  have : Module.Finite k (LinearMap.range T) := Module.Finite.range T
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  obtain ⟨Y, hY⟩ := hcov g
  exact ⟨Y ⊗ₜ[k] ⟨ρ g v, action_mem_orbitSpan ρ g v⟩, by
    change D Y (ρ g v) = _
    exact hY.symm⟩

end Langlands.FiniteVectors

namespace Langlands.Automorphic

open Langlands.Global
attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance differentialInfiniteFiniteRationalGroup :
    AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance differentialInfiniteFiniteContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance differentialInfiniteFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _

/-- Actual infinite-subgroup translation on the finite-smooth ambient space. -/
def finiteSmoothInfiniteSubgroupRightAction (U : Subgroup (InfiniteAdelicGL K n)) :
    Representation ℂ U (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothRightAction K n).comp
    ((AdelicGL.ofInfinite K n).toMonoidHom.comp U.subtype)

/-- Forgetting smoothness is faithful and intertwines the actual subgroup actions. -/
def finiteSmoothInfiniteSubgroupInclusion (U : Subgroup (InfiniteAdelicGL K n)) :
    (finiteSmoothInfiniteSubgroupRightAction K n U).IntertwiningMap
      (infiniteSubgroupRightAction K n U) where
  toLinearMap := (finiteSmoothRationalSubrepresentation K n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem isInfiniteFinite_iff_finiteSmoothVector (U : Subgroup (InfiniteAdelicGL K n))
    (f : FiniteSmoothRationalFunctions K n) :
    IsInfiniteFinite K n U f.val ↔
      FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U) f :=
  FiniteVectors.isFiniteVector_map_iff (finiteSmoothInfiniteSubgroupInclusion K n U)
    Subtype.val_injective f

/-- The finite-dimensional space of complexified Lie directions acts linearly. -/
def finiteSmoothComplexDifferential :
    ArchimedeanGL.ComplexLieAlgebra K n →ₗ[ℂ]
      Module.End ℂ (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothEnvelopingAction K n).toLinearMap.comp
    (ArchimedeanGL.envelopingGenerator K n).toLinearMap

private theorem complexLieAlgebra_finite :
    Module.Finite ℂ (ArchimedeanGL.ComplexLieAlgebra K n) := by
  have : Module.Finite ℝ (ArchimedeanGL.RealLieAlgebra K n) :=
    (ArchimedeanGL.realLieAlgebraToMatrix K n).symm.finiteDimensional
  infer_instance

theorem isFiniteVector_realDifferential
    (U : Subgroup (InfiniteAdelicGL K n)) (X : ArchimedeanGL.RealLieAlgebra K n)
    {f : FiniteSmoothRationalFunctions K n}
    (hf : FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U) f) :
    FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U)
      (finiteSmoothEnvelopingAction K n
        (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)) f) := by
  have := complexLieAlgebra_finite K n
  apply FiniteVectors.isFiniteVector_bilinear_of_covariance
    (finiteSmoothInfiniteSubgroupRightAction K n U)
    (finiteSmoothComplexDifferential K n) (ArchimedeanGL.complexify K n X) hf
  intro g
  refine ⟨ArchimedeanGL.complexify K n
    ((ArchimedeanGL.realLieAlgebraToMatrix K n).symm
      ((archimedeanGLCoordinates K n g.val : ArchimedeanMatrix K n) *
        ArchimedeanGL.realLieAlgebraToMatrix K n X *
        (archimedeanGLCoordinates K n g.val⁻¹ : ArchimedeanMatrix K n))), ?_⟩
  exact finiteSmoothRealDifferentialCovariance K n g.val X f

theorem isFiniteVector_complexDifferential
    (U : Subgroup (InfiniteAdelicGL K n)) (X : ArchimedeanGL.ComplexLieAlgebra K n)
    {f : FiniteSmoothRationalFunctions K n}
    (hf : FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U) f) :
    FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U)
      (finiteSmoothEnvelopingAction K n (ArchimedeanGL.envelopingGenerator K n X) f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have he : z ⊗ₜ[ℝ] X = z • ArchimedeanGL.complexify K n X := by
      simp [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul]
    rw [he, map_smul, map_smul, LinearMap.smul_apply]
    exact (isFiniteVector_realDifferential K n U X hf).smul z
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply]
    exact hX.add hY

theorem isFiniteVector_envelopingAction
    (U : Subgroup (InfiniteAdelicGL K n)) (a : ArchimedeanGL.EnvelopingAlgebra K n)
    {f : FiniteSmoothRationalFunctions K n}
    (hf : FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U) f) :
    FiniteVectors.IsFiniteVector (finiteSmoothInfiniteSubgroupRightAction K n U)
      (finiteSmoothEnvelopingAction K n a f) := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra K n)) a
  change FiniteVectors.IsFiniteVector _ (finiteSmoothEnvelopingAction K n
    (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) f)
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap z =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
    exact hf.smul z
  | ι X =>
    exact isFiniteVector_complexDifferential K n U X hf
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    exact hx (hy hf)
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact (hx hf).add (hy hf)

theorem automorphicDifferentialInfiniteFinite :
    AutomorphicDifferentialInfiniteFiniteStatement K n := by
  intro a f
  apply (isInfiniteFinite_iff_finiteSmoothVector K n (standardInfiniteCompact K n) _).mpr
  apply isFiniteVector_envelopingAction K n
  exact (isInfiniteFinite_iff_finiteSmoothVector K n (standardInfiniteCompact K n) _).mp
    ((mem_automorphicSubrepresentation K n f.val).mp f.property).2.1

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    AutomorphicDifferentialInfiniteFiniteStatement K n :=
  @automorphicDifferentialInfiniteFinite

end Langlands.Automorphic
