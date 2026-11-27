import Langlands.BushnellKutzko.ClassCoverTwist
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceStatement

/-! # Covering simple-character classes: the fibre characters (BK94 (2.7) and (1.8)) -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Scalar congruence: whenever `F[γ]` is a field, every tame corestriction relative to
`F[γ]/F` carries `e` to a scalar of `F[γ]` modulo `𝔓^{-k}`. When `e ∈ 𝔓^{-(k+1)}` and
`[𝔄,n,k+1,γ]` is simple, this says that the derived stratum `[𝔅_γ,k+1,k,s(e)]` is equivalent to
a stratum with a scalar coefficient, which may be null. -/
def CorestrictionScalarMod (L : LatticeChain 𝒪[F] F V) (γ e : A) (k : ℤ) : Prop :=
  ∀ h : IsField (elementAlgebra γ),
    letI := h.toField
    ∀ s : TameCorestriction 𝒪[F] F (elementAlgebra γ) V,
      ∃ δ : elementAlgebra γ,
        (s e).restrictScalars F - subfieldEmbedding F (elementAlgebra γ) V δ ∈
          L.endFiltration (-k)

variable (ψF : AddChar F ℂ)

/-- **BK93 (3.3.18), (3.3.20)(ii).** Let `[𝔄,n,k+1,γ]` and `[𝔄,n,k,β]` both be simple strata on
the same indexed chain `L`, with `β ≡ γ (mod 𝔓^{-(k+1)})`. Then every pair of `Ĉ(𝔄,k,β)` has the
same subgroup as some pair of `Ĉ(𝔄,k,γ)` and is its twist by `ψ_{β-γ}` on that subgroup, and
conversely the twist by `ψ_{β-γ}` of every pair of `Ĉ(𝔄,k,γ)` is a pair of `Ĉ(𝔄,k,β)` with the
same subgroup. Twisting does not change the character domain. -/
def TwistDecompositionAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (S : SimpleStratumAt L n k),
    S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) →
    (∀ P ∈ simpleCharacterPairs ψF S.1 k, ∃ ϑ' ∈ simpleCharacterPairs ψF T.1 k, ϑ'.1 = P.1 ∧
      characterAgreesOn ϑ'.1 P.2 ϑ'.2 (elementCharacter (traceCharacter ψF) (S.1.b - T.1.b))) ∧
    (∀ ϑ' ∈ simpleCharacterPairs ψF T.1 k, ∃ P ∈ simpleCharacterPairs ψF S.1 k, P.1 = ϑ'.1 ∧
      characterAgreesOn ϑ'.1 P.2 ϑ'.2 (elementCharacter (traceCharacter ψF) (S.1.b - T.1.b)))

/-- **The quotient of two extensions (BK94 p. 120 and the proof of (2.7)).** For a simple stratum
`[𝔄,n,k+1,γ]` on `L`, two pairs of `C(𝔄,k,γ)` with the same restriction to `U^{k+2}(𝔄)` have the
same subgroup, and their characters differ by `ψ_e` for some `e ∈ 𝔓^{-(k+1)}` with
`CorestrictionScalarMod L γ e k`. This is an auxiliary
step of the proof of BK94 (2.7), not its conclusion on derived strata. -/
def FibreCharacterAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (ϑ ϑ' : CharacterPair G),
    ϑ ∈ simpleCharacterPairs ψF T.1 k → ϑ' ∈ simpleCharacterPairs ψF T.1 k →
    ϑ.restrict (L.unitFiltration (k + 2)) = ϑ'.restrict (L.unitFiltration (k + 2)) →
    ϑ'.1 = ϑ.1 ∧ ∃ e ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)), CorestrictionScalarMod L T.1.b e k ∧
      characterAgreesOn ϑ.1 ϑ'.2 ϑ.2 (elementCharacter (traceCharacter ψF) e)

/-- **BK93 (2.2.8), (2.4.1) and BK94 (1.8).** Let `[𝔄,n,k+1,γ]` be simple and let `[𝔄,n,k,β]`
be a simple stratum on the same chain with `β ≡ γ (mod 𝔓^{-(k+1)})`. If `e ∈ 𝔓^{-(k+1)}` and the
tame corestriction of `e` relative to `γ` is a scalar modulo `𝔓^{-k}`, then some simple stratum
`[𝔄,n,k,β']` on the same chain satisfies `β' ≡ β + e (mod 𝔓^{-k})`. -/
def RefinementSimpleAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (S : SimpleStratumAt L n k) (e : A),
    S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) →
    e ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) → CorestrictionScalarMod L T.1.b e k →
    ∃ S' : SimpleStratumAt L n k, S'.1.b - (S.1.b + e) ∈ L.endFiltration (-(k : ℤ))

/-- **BK94 (2.7) and (1.8)** from the twist decomposition, the fibre characters and the
refinement. -/
theorem fibreTwistCoverAt_of (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (k : ℕ) (hA1 : TwistDecompositionAt ψF L n k) (hA2 : FibreCharacterAt ψF L n k)
    (hA3 : RefinementSimpleAt L n k) : FibreTwistCoverAt ψF L n k := by
  intro T ϑ hϑ P hP
  obtain ⟨S, hSb, hPS, hres⟩ := hP
  obtain ⟨ϑP, hϑP, hdomP, hagP⟩ := (hA1 T S hSb).1 P hPS
  have hϑH : ϑ.1 ≤ L.unitFiltration (k + 1) := by
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hϑ
    obtain ⟨q, θ, -, rfl⟩ := hϑ
    exact (simpleHGroup_le_unitFiltration T.1.chain T.1.n T.1.b q.tail (k + 1)).trans
      (le_of_eq (congrArg (fun M : LatticeChain 𝒪[F] F V => M.unitFiltration (k + 1)) T.2.1))
  have hϑPH : ϑP.1 ≤ L.unitFiltration (k + 1) := by
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hϑP
    obtain ⟨q, θ, -, rfl⟩ := hϑP
    exact (simpleHGroup_le_unitFiltration T.1.chain T.1.n T.1.b q.tail (k + 1)).trans
      (le_of_eq (congrArg (fun M : LatticeChain 𝒪[F] F V => M.unitFiltration (k + 1)) T.2.1))
  have hresP : ϑ.restrict (L.unitFiltration (k + 2)) = ϑP.restrict (L.unitFiltration (k + 2)) := by
    rw [← hres]
    refine CharacterPair.ext_of_eq ?_ (fun g hg₁ hg₂ => ?_)
    · change P.1 ⊓ _ = ϑP.1 ⊓ _
      rw [hdomP]
    · obtain ⟨m₁, m₂, e₁⟩ := hagP ⟨g, hg₂.1⟩
      have htriv := elementCharacter_eq_one_of_depth L ψF hψ hSb (k := k + 2)
        (by push_cast; omega) hg₂.2
      apply Units.ext
      change (P.2 ⟨g, hg₁.1⟩ : ℂ) = (ϑP.2 ⟨g, hg₂.1⟩ : ℂ)
      rw [show (P.2 ⟨g, hg₁.1⟩ : ℂ) = (P.2 ⟨g, m₁⟩ : ℂ) from rfl, e₁]
      change _ * elementCharacter (traceCharacter ψF) (S.1.b - T.1.b) g = _
      rw [htriv, mul_one]
  obtain ⟨hdomϑ, e, he, hscal, hagree⟩ := hA2 T ϑ ϑP hϑ hϑP hresP
  obtain ⟨S', hS'⟩ := hA3 T S e hSb he hscal
  have hS'b : S'.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) := by
    have h1 := L.endFiltration_antitone
      (show (-((k + 1 : ℕ) : ℤ)) ≤ -(k : ℤ) by push_cast; omega) hS'
    have := add_mem (add_mem h1 hSb) he
    convert this using 1
    abel
  obtain ⟨P'', hP'', hdom'', hag''⟩ := (hA1 T S' hS'b).2 ϑ hϑ
  refine ⟨S', hS'b, P'', hP'', hdom'', hag'', ?_⟩
  have hPeq : P = P'' := by
    refine CharacterPair.ext_of_eq (hdomP.symm.trans (hdomϑ.trans hdom''.symm))
      (fun g hg₁ hg₂ => ?_)
    have hgϑ : g ∈ ϑ.1 := hdom'' ▸ hg₂
    obtain ⟨m₁, m₂, e₁⟩ := hagP ⟨g, hdomϑ ▸ hgϑ⟩
    obtain ⟨m₃, m₄, e₂⟩ := hagree ⟨g, hgϑ⟩
    obtain ⟨m₅, m₆, e₃⟩ := hag'' ⟨g, hgϑ⟩
    have hgU : g ∈ L.unitFiltration (k + 1) := hϑH hgϑ
    have htriv := elementCharacter_eq_one_of_depth L ψF hψ hS' (k := k + 1)
      (by push_cast; omega) hgU
    apply Units.ext
    change (P.2 ⟨g, m₁⟩ : ℂ) = (P''.2 ⟨g, m₅⟩ : ℂ)
    rw [e₁, e₃]
    change (ϑP.2 ⟨g, m₃⟩ : ℂ) * _ = _
    rw [e₂]
    change (ϑ.2 ⟨g, m₄⟩ : ℂ) * elementCharacter (traceCharacter ψF) e g *
        elementCharacter (traceCharacter ψF) (S.1.b - T.1.b) g =
      (ϑ.2 ⟨g, m₆⟩ : ℂ) * elementCharacter (traceCharacter ψF) (S'.1.b - T.1.b) g
    rw [mul_assoc, ← elementCharacter_add,
      ← mul_one (elementCharacter (traceCharacter ψF) (e + (S.1.b - T.1.b)) g), ← htriv,
      ← elementCharacter_add]
    congr 2
    abel
  rw [hPeq]
  exact CharacterPair.AreConjugateBy.refl _ _

end Langlands.BushnellKutzko
