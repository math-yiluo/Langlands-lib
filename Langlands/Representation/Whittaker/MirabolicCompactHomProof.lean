import Langlands.Representation.Whittaker.MirabolicCompactHomStatement
import Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.Padic
import Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement

/-!
# Proof of scalar uniqueness for compact-to-smooth mirabolic intertwiners

Bernstein–Zelevinsky (1976), Proposition 5.15(b), printed p.49, with proof on p.50.
Evaluation at the identity after an intertwiner `A` is a Whittaker functional on the
compact model, and so is evaluation at the identity itself. The latter is nonzero, so
uniqueness of Whittaker functionals on the compact model makes the former a multiple
`c` of it. Right translation carries the equality at the identity to every point, giving
`A = c • inclusion`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF

namespace MirabolicCompactHom

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)

/-- Evaluation at the identity after an intertwiner from the compact model to the
smooth model. -/
def evalOne (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)) :
    Module.Dual ℂ (MirabolicCompactFunctions ψ n) where
  toFun f := mirabolicEval ψ n (A f) 1
  map_add' f h := by rw [map_add]; rfl
  map_smul' a f := by rw [map_smul]; rfl

@[simp] theorem evalOne_apply
    (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n))
    (f : MirabolicCompactFunctions ψ n) :
    evalOne ψ n A f = mirabolicEval ψ n (A f) 1 := rfl

/-- For the canonical inclusion this is evaluation of the compact function at the identity. -/
theorem evalOne_inclusion_apply (f : MirabolicCompactFunctions ψ n) :
    evalOne ψ n (mirabolicCompactInclusion ψ n) f = mirabolicCompactEval ψ n f 1 := rfl

/-- Evaluation at the identity after an intertwiner is a Whittaker functional. -/
theorem evalOne_mem
    (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)) :
    evalOne ψ n A ∈ MirabolicWhittaker.compactFunctionals ψ n := by
  intro u f
  change mirabolicEval ψ n (A (mirabolicCompactInduced ψ n u f)) 1 =
    (mirabolicCharacter ψ n u : ℂ) * mirabolicEval ψ n (A f) 1
  have hA : A (mirabolicCompactInduced ψ n u f) = mirabolicSmoothInduced ψ n u (A f) :=
    LinearMap.congr_fun (A.isIntertwining' u) f
  rw [hA, mirabolicEval_translate, one_mul, ← mul_one (u : mirabolic n F),
    mirabolicEval_covariance]

/-- Agreement at the identity with a multiple of the inclusion propagates, by right
translation, to equality of intertwiners. -/
theorem eq_smul_inclusion_of_evalOne
    (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)) (c : ℂ)
    (h : ∀ f, mirabolicEval ψ n (A f) 1 = c * mirabolicCompactEval ψ n f 1) :
    A = c • mirabolicCompactInclusion ψ n := by
  refine DFunLike.ext _ _ fun f => Subtype.ext (Subtype.ext (funext fun g => ?_))
  have hA : A (mirabolicCompactInduced ψ n g f) = mirabolicSmoothInduced ψ n g (A f) :=
    LinearMap.congr_fun (A.isIntertwining' g) f
  have key : mirabolicEval ψ n (A f) g = c * mirabolicCompactEval ψ n f g := by
    have h1 := h (mirabolicCompactInduced ψ n g f)
    rw [hA, mirabolicEval_translate, mirabolicCompactEval_translate, one_mul] at h1
    exact h1
  exact key

/-- The generic scalar uniqueness: a test vector for Whittaker functionals on the compact
model and a compact function not vanishing at the identity make every intertwiner from
the compact model to the smooth model a multiple of the canonical inclusion. -/
theorem exists_eq_smul_inclusion
    (htest : ∃ f₀ : MirabolicCompactFunctions ψ n,
      ∀ ℓ ∈ MirabolicWhittaker.compactFunctionals ψ n, ℓ f₀ = 0 → ℓ = 0)
    (hne : ∃ f : MirabolicCompactFunctions ψ n, mirabolicCompactEval ψ n f 1 ≠ 0)
    (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)) :
    ∃ c : ℂ, A = c • mirabolicCompactInclusion ψ n := by
  obtain ⟨f₀, hf₀⟩ := htest
  let ℓ₀ := evalOne ψ n (mirabolicCompactInclusion ψ n)
  have hℓ₀ : ℓ₀ ≠ 0 := by
    obtain ⟨f, hf⟩ := hne
    intro h
    exact hf ((evalOne_inclusion_apply ψ n f).symm.trans (LinearMap.congr_fun h f))
  have h0 : ℓ₀ f₀ ≠ 0 := fun h => hℓ₀ (hf₀ ℓ₀ (evalOne_mem ψ n _) h)
  let c : ℂ := evalOne ψ n A f₀ / ℓ₀ f₀
  have hmem : evalOne ψ n A - c • ℓ₀ ∈ MirabolicWhittaker.compactFunctionals ψ n :=
    Submodule.sub_mem _ (evalOne_mem ψ n A) (Submodule.smul_mem _ c (evalOne_mem ψ n _))
  have hz : (evalOne ψ n A - c • ℓ₀) f₀ = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0, sub_self]
  have hzero := hf₀ _ hmem hz
  refine ⟨c, eq_smul_inclusion_of_evalOne ψ n A c fun f => ?_⟩
  have hf := LinearMap.congr_fun hzero f
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, sub_eq_zero,
    smul_eq_mul] at hf
  exact hf

/-- The scalar character representation of the upper unipotent subgroup is smooth. -/
theorem characterRepresentation_smooth [NonarchimedeanGroup (mirabolic n F)] :
    IsSmooth (mirabolicCharacterRepresentation ψ n) := by
  intro z
  refine ⟨{ toSubgroup := (mirabolicCharacter ψ n).ker
            isOpen' := Langlands.isOpen_ker_of_continuous_complex_character _
              (mirabolicCharacterContinuous ψ n).continuous }, ?_⟩
  intro k
  change (mirabolicCharacter ψ n k : ℂ) * z = z
  rw [show mirabolicCharacter ψ n k = 1 from k.property, Units.val_one, one_mul]

/-- Evaluation at the identity is nonzero on the compact model: a compactly induced
local section takes the value one at the identity. -/
theorem exists_compactEval_one_ne_zero
    [NonarchimedeanGroup (mirabolic n F)] [WeaklyLocallyCompactSpace (mirabolic n F)] :
    ∃ f : MirabolicCompactFunctions ψ n, mirabolicCompactEval ψ n f 1 ≠ 0 := by
  refine ⟨Induction.compactLocalSection _ _ (characterRepresentation_smooth ψ n)
    1 1 Set.univ isOpen_univ (Set.mem_univ _), ?_⟩
  have h := Induction.compactLocalSection_apply _ _ (characterRepresentation_smooth ψ n)
    (1 : mirabolic n F) (1 : ℂ) Set.univ isOpen_univ (Set.mem_univ _)
  change Induction.eval _ _ _ 1 ≠ 0
  rw [h]
  exact one_ne_zero

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Scalar uniqueness over a p-adic field with its canonical topology. -/
theorem compactHomScalar_canonical (F : PadicField.{uF} p) :
    letI := F.canonicalTopologicalData.topology
    letI : IsTopologicalRing F.Carrier := by
      let := F.canonicalTopologicalData.valuativeRel
      let := F.canonicalTopologicalData.localField
      infer_instance
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)),
      ∃ c : ℂ, A = c • mirabolicCompactInclusion ψ n := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : NonarchimedeanAddGroup F.Carrier := rowFourierCutoff_nonarchimedean
  have : ∀ m, NonarchimedeanGroup (GeneralLinear m F.Carrier) := fun m =>
    Langlands.valuativeGeneralLinearNonarchimedean F.Carrier m
  have : ∀ m, LocallyCompactSpace (GeneralLinear m F.Carrier) := fun m =>
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace m
  intro n ψ A
  have : NonarchimedeanGroup (mirabolic n F.Carrier) :=
    MirabolicWhittaker.mirabolic_nonarchimedean
  have : LocallyCompactSpace (mirabolic n F.Carrier) := Mirabolic.locallyCompactSpace
  exact exists_eq_smul_inclusion ψ n
    (MirabolicWhittaker.exists_testVector ψ (MirabolicWhittaker.isOpen_complex_eq_one ψ) n)
    (exists_compactEval_one_ne_zero ψ n) A

end Padic

end MirabolicCompactHom

/-- Bernstein–Zelevinsky (1976), Proposition 5.15(b): every intertwiner from the actual
compact mirabolic model to the actual smooth mirabolic model over a p-adic field with
its canonical topology is a complex multiple of the canonical inclusion. -/
theorem mirabolicCompactHomScalar : MirabolicCompactHomScalarStatement.{uF} := by
  intro p hp F
  exact MirabolicCompactHom.compactHomScalar_canonical F

end Langlands.Whittaker
