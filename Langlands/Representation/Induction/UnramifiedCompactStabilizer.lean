import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Topology.CompactNormCharacter

/-! # Unramified pullbacks on compact induction stabilizers -/

open scoped NNReal

namespace Langlands.Induction

universe uG uH uM uI

open Plancherel

variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {M : Type uM} [Group M] [TopologicalSpace M]
variable {I : Type uI}

/-- Pull back an actual continuous unramified character through a continuous
group homomorphism. -/
def unramifiedPullbackCharacter (ν : I → (M →* ℝ≥0ˣ))
    (r : H →* M) (hr : Continuous r) (χ : unramifiedCharacters ν) : H →ₜ* ℂˣ where
  toMonoidHom := χ.val.toMonoidHom.comp r
  continuous_toFun := χ.val.continuous.comp hr

@[simp]
theorem unramifiedPullbackCharacter_apply (ν : I → (M →* ℝ≥0ˣ))
    (r : H →* M) (hr : Continuous r) (χ : unramifiedCharacters ν) (h : H) :
    unramifiedPullbackCharacter ν r hr χ h = χ.val (r h) := rfl

/-- A continuous pullback of an actual unramified character is trivial on every
compact subgroup of its source, provided the given norm characters are continuous. -/
theorem compactSubgroup_le_unramifiedPullback_ker (ν : I → (M →* ℝ≥0ˣ))
    (hν : ∀ i, Continuous (ν i)) (r : H →* M) (hr : Continuous r)
    (χ : unramifiedCharacters ν) (J : Subgroup H) (hJ : IsCompact (J : Set H)) :
    J ≤ (unramifiedPullbackCharacter ν r hr χ).toMonoidHom.ker := by
  intro h hh
  change χ.val (r h) = 1
  apply χ.property
  apply (mem_commonNormKernel ν (r h)).mpr
  intro i
  exact Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact
    ((ν i).comp r) ((hν i).comp hr) J hJ hh

section ConjugateStabilizers

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every conjugate compact open stabilizer in a closed inducing subgroup lies
in the kernel of the continuous unramified pullback. -/
theorem conjOpenSubgroup_le_unramifiedPullback_ker
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
    (r : P →* M) (hr : Continuous r) (χ : unramifiedCharacters ν)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (conjOpenSubgroup P K x).toSubgroup ≤ (χ.val.toMonoidHom.comp r).ker :=
  compactSubgroup_le_unramifiedPullback_ker ν hν r hr χ
    (conjOpenSubgroup P K x).toSubgroup (isCompact_conjOpenSubgroup P hP K hK x)

/-- Pointwise form of compact-stabilizer triviality for the literal character
`p ↦ χ(r(p))` used to twist the inducing action. -/
theorem unramifiedPullback_eq_one_of_mem_conjOpenSubgroup
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
    (r : P →* M) (hr : Continuous r) (χ : unramifiedCharacters ν)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    {p : P} (hp : p ∈ conjOpenSubgroup P K x) :
    χ.val (r p) = 1 :=
  conjOpenSubgroup_le_unramifiedPullback_ker P hP ν hν r hr χ K hK x hp

end ConjugateStabilizers

end Langlands.Induction
