import Langlands.Automorphic.BlockShapeRealLieDecomposition
import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation

/-! Full operator stability of a projected block section kernel. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global Langlands.Global.ArchimedeanGL
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ V)

/-- The complex Lie action of any algebra action of the concrete
automorphic operator algebra. -/
def operatorAlgebraComplexLieAction : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V :=
  (A.comp (differentialOperator F n)).toLieHom.comp (envelopingGenerator F n)

local notation "ρf" => A.toMonoidHom.comp (finiteOperator F n)
local notation "ρc" => A.toMonoidHom.comp (compactOperator F n)
local notation "ρu" => A.comp (differentialOperator F n)
local notation "L" => operatorAlgebraComplexLieAction A

local instance projectedKernelRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance projectedKernelContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance projectedKernelFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

private theorem finite_compact (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n) (v : V) :
    ρf d (ρc k v) = ρc k (ρf d v) := by
  have h : finiteOperator F n d * compactOperator F n k =
      compactOperator F n k * finiteOperator F n d := by
    apply Subtype.ext
    change finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) *
        finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) =
      finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) *
        finiteSmoothRightAction F n (AdelicGL.ofFinite F n d)
    rw [← map_mul, ← map_mul, AdelicGL.ofInfinite_commute]
  exact LinearMap.congr_fun (by simpa only [map_mul] using congrArg A h) v

private theorem finite_lie (d : FiniteAdelicGL F n) (X : ComplexLieAlgebra F n) (v : V) :
    ρf d (L X v) = L X (ρf d v) := by
  let u := envelopingGenerator F n X
  have h : finiteOperator F n d * differentialOperator F n u =
      differentialOperator F n u * finiteOperator F n d :=
    Subtype.ext (LinearMap.ext (finiteSmoothFiniteRightAction_envelopingAction F n d u))
  exact LinearMap.congr_fun (by simpa only [map_mul] using congrArg A h) v

private theorem compact_lie (k : standardInfiniteCompact F n) (X : ComplexLieAlgebra F n) (v : V) :
    ρc k (L X v) = L (complexLieConjugation F n k.val X) (ρc k v) := by
  let u := envelopingGenerator F n X
  have h : compactOperator F n k * differentialOperator F n u =
      differentialOperator F n (envelopingConjugation F n k.val u) * compactOperator F n k :=
    Subtype.ext (LinearMap.ext (finiteSmoothRightAction_envelopingAction k.val u))
  rw [show L (complexLieConjugation F n k.val X) =
    A (differentialOperator F n (envelopingConjugation F n k.val u)) by
      rw [envelopingConjugation_generator]; rfl]
  exact LinearMap.congr_fun (by simpa only [map_mul] using congrArg A h) v

/-- The common kernel of the projected coefficient at all compact and finite translates. -/
def projectedBlockSectionKernelSubmodule (e : V →ₗ[ℂ] W) : Submodule ℂ V where
  carrier := {v | ∀ k d, e (ρc k (ρf d v)) = 0}
  zero_mem' := fun k d => by simp
  add_mem' := by
    intro v w hv hw k d
    change e (ρc k (ρf d (v + w))) = 0
    simp only [map_add, hv k d, hw k d, add_zero]
  smul_mem' := by
    intro a v hv k d
    change e (ρc k (ρf d (a • v))) = 0
    simp only [map_smul, hv k d, smul_zero]

@[simp]
theorem mem_projectedBlockSectionKernelSubmodule (e : V →ₗ[ℂ] W) (v : V) :
    v ∈ projectedBlockSectionKernelSubmodule A e ↔ ∀ k d, e (ρc k (ρf d v)) = 0 :=
  Iff.rfl

private theorem enveloping_mem_of_real_lie (P : Submodule ℂ V)
    (hreal : ∀ X v, v ∈ P → L (complexify F n X) v ∈ P)
    (u : EnvelopingAlgebra F n) : ∀ v ∈ P, ρu u v ∈ P := by
  induction u using Langlands.Archimedean.InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    intro v hv
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact P.smul_mem c hv
  | «ι» Y =>
    change ∀ v ∈ P, L Y v ∈ P
    induction Y using TensorProduct.inductionOn with
    | tmul c X =>
      intro v hv
      rw [show c ⊗ₜ[ℝ] X = c • complexify F n X by
        rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, LinearMap.smul_apply]
      exact P.smul_mem c (hreal X v hv)
    | add Y Z hY hZ =>
      intro v hv
      rw [map_add, LinearMap.add_apply]
      exact P.add_mem (hY v hv) (hZ v hv)
  | mul a b ha hb =>
    intro v hv
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb v hv)
  | add a b ha hb =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem (ha v hv) (hb v hv)

set_option maxHeartbeats 1500000 in
/-- The projected section kernel is stable under the full operator algebra when the
base evaluation kills upper block derivatives and its kernel is stable under
individual block Lie differentiation. The compact derivative is algebraic-dual
differentiation, so the result also applies to operator quotients. -/
def projectedBlockSectionKernel (B : BlockShape n) (e : V →ₗ[ℂ] W)
    (hderiv : CompactDualDerivative ρc L)
    (hupper : ∀ X v, IsStrictUpperBlockLie F B X → e (L (complexify F n X) v) = 0)
    (hblock : ∀ i (X : RealLieAlgebra F (B.size i)) v, e v = 0 →
      e (L (complexify F n (blockShapeRealLieInclusion F B i X)) v) = 0) :
    Subrepresentation A.toMonoidHom := by
  let P := projectedBlockSectionKernelSubmodule A e
  have hf (d : FiniteAdelicGL F n) (v : V) (hv : v ∈ P) : ρf d v ∈ P := by
    intro k g
    simpa only [map_mul, Module.End.mul_apply] using hv k (g * d)
  have hk (k : standardInfiniteCompact F n) (v : V) (hv : v ∈ P) : ρc k v ∈ P := by
    intro l d
    rw [finite_compact A, ← Module.End.mul_apply, ← map_mul]
    exact hv (l * k) d
  have hLieC (C : compactLieSubalgebra F n) (v : V) (hv : v ∈ P) :
      e (L (complexify F n C.val) v) = 0 := by
    obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n C
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro μ
    have hz (t : ℝ) : e (ρc (c t) v) = 0 := by simpa using hv (c t) 1
    have hder := hderiv C.val c hc0 hc (μ.comp e) v
    change HasDerivAt (fun t : ℝ => μ (e (ρc (c t) v)))
      (μ (e (L (complexify F n C.val) v))) 0 at hder
    simp only [hz, map_zero] at hder
    exact hder.unique (hasDerivAt_const 0 0)
  have hreal (X : RealLieAlgebra F n) (v : V) (hv : v ∈ P) :
      L (complexify F n X) v ∈ P := by
    intro k d
    rw [finite_lie A, compact_lie A, complexLieConjugation_complexify]
    let v' := ρc k (ρf d v)
    have hv' : v' ∈ P := hk k _ (hf d _ hv)
    obtain ⟨D, U, C, hU, hX⟩ :=
      exists_realLie_block_upper_compact F B (realLieConjugation F n k.val X)
    change e (L (complexify F n (realLieConjugation F n k.val X)) v') = 0
    rw [hX]
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,
      hupper U v' hU, hLieC C v' hv', add_zero]
    exact Finset.sum_eq_zero fun i _ => hblock i (D i) v' (hv k d)
  refine ⟨P, ?_⟩
  rintro ⟨u, hu⟩
  induction hu using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with (⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact hf d
    · exact hk k
    · exact enveloping_mem_of_real_lie A P hreal u
  | algebraMap c =>
    intro v hv
    change A (algebraMap ℂ (automorphicOperatorAlgebra F n) c) v ∈ P
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact P.smul_mem c hv
  | add a b ha hb ha' hb' =>
    intro v hv
    let a₀ : automorphicOperatorAlgebra F n := ⟨a, ha⟩
    let b₀ : automorphicOperatorAlgebra F n := ⟨b, hb⟩
    change A (a₀ + b₀) v ∈ P
    rw [show A (a₀ + b₀) v = A a₀ v + A b₀ v from LinearMap.congr_fun (A.map_add a₀ b₀) v]
    exact P.add_mem (ha' hv) (hb' hv)
  | mul a b ha hb ha' hb' =>
    intro v hv
    let a₀ : automorphicOperatorAlgebra F n := ⟨a, ha⟩
    let b₀ : automorphicOperatorAlgebra F n := ⟨b, hb⟩
    change A (a₀ * b₀) v ∈ P
    rw [show A (a₀ * b₀) v = A a₀ (A b₀ v) from LinearMap.congr_fun (A.map_mul a₀ b₀) v]
    exact ha' (hb' hv)

@[simp]
theorem mem_projectedBlockSectionKernel (B : BlockShape n) (e : V →ₗ[ℂ] W)
    (hderiv : CompactDualDerivative ρc L)
    (hupper : ∀ X v, IsStrictUpperBlockLie F B X → e (L (complexify F n X) v) = 0)
    (hblock : ∀ i (X : RealLieAlgebra F (B.size i)) v, e v = 0 →
      e (L (complexify F n (blockShapeRealLieInclusion F B i X)) v) = 0) (v : V) :
    v ∈ projectedBlockSectionKernel A B e hderiv hupper hblock ↔
      ∀ k d, e (ρc k (ρf d v)) = 0 :=
  Iff.rfl

end Langlands.Automorphic
