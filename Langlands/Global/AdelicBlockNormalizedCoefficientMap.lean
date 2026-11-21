import Langlands.Global.AdelicBlockScalarEnvelopingAction
import Langlands.Global.AdelicBlockScalarParabolicDerivative
import Langlands.Global.AdelicBlockCompactProduct

/-! # Comparing Lie derivatives by testing compact translates at the identity -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 230000

universe u v w

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear ArchimedeanGL AdelicBlockParabolic
open AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))

local notation "W" => smoothCompactFiniteSections F B S
local notation "C" => coefficientValues F B S
local notation "K" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n

/-- Evaluate the normalized Levi coefficient at a compact argument. -/
def normalizedCoefficientMap (k : standardCompact F n) : W →ₗ[ℂ] C where
  toFun f := normalizedCoefficient F B S f k
  map_add' f g := by
    apply Subtype.ext
    funext m
    change _ * (f.val.val.val (B.leviEmbedding (Adeles F) m * k.val) +
      g.val.val.val (B.leviEmbedding (Adeles F) m * k.val)) = _
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext m
    change (leviHalfCharacter F B m : ℂ)⁻¹ * (c * f.val.val.val
      (B.leviEmbedding (Adeles F) m * k.val)) =
      c * ((leviHalfCharacter F B m : ℂ)⁻¹ * f.val.val.val (B.leviEmbedding (Adeles F) m * k.val))
    exact mul_left_comm _ _ _

/-- Testing the identity infinite compact argument after a compact translation tests that translate. -/
theorem normalizedCoefficientMap_compactAction (k : K) (l : Kf) (f : W) :
    normalizedCoefficientMap F B S (compactPair F 1 l) (smoothCompactAction F B S k f) =
      normalizedCoefficientMap F B S (compactPair F k l) f := by
  apply Subtype.ext
  funext m
  change (leviHalfCharacter F B m : ℂ)⁻¹ * f.val.val.val
    ((B.leviEmbedding (Adeles F) m * (compactPair F 1 l).val) * AdelicGL.ofInfinite F n k.val) =
    (leviHalfCharacter F B m : ℂ)⁻¹ * f.val.val.val (B.leviEmbedding (Adeles F) m * (compactPair F k l).val)
  have hk : (compactPair F 1 l).val * AdelicGL.ofInfinite F n k.val = (compactPair F k l).val := by
    change AdelicGL.pair F n 1 l.val * AdelicGL.ofInfinite F n k.val = AdelicGL.pair F n k.val l.val
    rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, one_mul, mul_one]
  rw [mul_assoc, hk]

private theorem eq_of_normalizedCoefficientMap {f g : W}
    (h : ∀ (k : K) (l : Kf), normalizedCoefficientMap F B S (compactPair F k l) f =
      normalizedCoefficientMap F B S (compactPair F k l) g) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply (compactPictureEquiv F B C).injective
  apply Subtype.ext
  funext k m
  let q := standardCompactProductEquiv F n k
  have hq : compactPair F q.1 q.2 = k :=
    (standardCompactProductEquiv F n).symm_apply_apply k
  exact (congrArg (fun l => normalizedSlice F B f.val.val.val l m) hq.symm).trans
    ((congrArg (fun z : C => z.val m) (h q.1 q.2)).trans
      (congrArg (fun l => normalizedSlice F B g.val.val.val l m) hq))

/-- The actual section differential transforms under compact translation by the adjoint. -/
theorem smoothCompactAction_sectionDifferential (k : K) (X : RealLieAlgebra F n) (f : W) :
    smoothCompactAction F B S k (sectionDifferential F B S X f) =
      sectionDifferential F B S (realLieConjugation F n k.val X) (smoothCompactAction F B S k f) := by
  have h := smoothCompactAction_sectionEnvelopingAction F B S k
    (envelopingGenerator F n (complexify F n X)) f
  rw [envelopingConjugation_generator, show complexLieConjugation F n k.val (complexify F n X) =
    complexify F n (realLieConjugation F n k.val X) from rfl,
    sectionEnvelopingAction_real_generator, sectionEnvelopingAction_real_generator] at h
  exact h

/-- Additivity in the real direction for the actual section differential. -/
theorem sectionDifferential_add (X Y : RealLieAlgebra F n) (f : W) :
    sectionDifferential F B S (X + Y) f = sectionDifferential F B S X f + sectionDifferential F B S Y f := by
  simp only [← sectionEnvelopingAction_real_generator, map_add, LinearMap.add_apply]

/-- For compact-equivariant operators, equality of the normalized coefficient
at infinite compact identity for every input implies equality of sections. -/
theorem intertwines_sectionDifferential_of_identity
    {V : Type v} [AddCommGroup V] [Module ℂ V] {L : Type w}
    (ρ : Representation ℂ K V) (J : ρ.IntertwiningMap (smoothCompactAction F B S))
    (ι : L → RealLieAlgebra F n) (D : L → Module.End ℂ V) (α : K → L → L)
    (hι : ∀ k X, realLieConjugation F n k.val (ι X) = ι (α k X))
    (hρ : ∀ k X x, ρ k (D X x) = D (α k X) (ρ k x))
    (h₁ : ∀ X x (l : Kf),
      normalizedCoefficientMap F B S (compactPair F 1 l) (J (D X x)) =
        normalizedCoefficientMap F B S (compactPair F 1 l) (sectionDifferential F B S (ι X) (J x)))
    (X : L) (x : V) :
    J (D X x) = sectionDifferential F B S (ι X) (J x) := by
  apply eq_of_normalizedCoefficientMap F B S
  intro k l
  rw [← normalizedCoefficientMap_compactAction F B S k l (J (D X x)),
    ← normalizedCoefficientMap_compactAction F B S k l (sectionDifferential F B S (ι X) (J x)),
    ← Representation.IntertwiningMap.isIntertwining _ _ J, hρ,
    smoothCompactAction_sectionDifferential, hι, ← Representation.IntertwiningMap.isIntertwining _ _ J]
  exact h₁ (α k X) (ρ k x) l

end Langlands.Global.AdelicBlockScalarSections
