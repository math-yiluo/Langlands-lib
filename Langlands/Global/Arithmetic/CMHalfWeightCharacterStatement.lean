import Langlands.Global.HeckeCharacter
import Langlands.Global.InfinityType
import Langlands.Global.AdelicFunctoriality.Isomorphism

/-!
# Conjugate-inverse Hecke characters of weight one

A proposition definition for the auxiliary character `φ` of Harris–Taylor
(2001), Proposition VII.2.7, whose existence is shown in the proof of
Corollary VII.2.8. It supplies the half-integral twist that Harris's
normalization (1998, p.195) needs for automorphic induction to `GL(n)` with
`n` even. The theorem is not proved here.
-/

noncomputable section

universe u

namespace Langlands.Global

open NumberField

/-- On a CM field `K`, every infinity type `t` of pure weight one is realized,
after the twist by `‖·‖^{1/2}`, by a Hecke character `φ` with `φ ∘ c = φ⁻¹`
for the actual arithmetic complex conjugation `c`, unramified at every place
of a finite set `S` of finite places disjoint from its conjugate set. At each
archimedean place the component of `φ` is `z ↦ z^{t(σ)} z̄^{t(σ̄)} / |z|`. -/
def CMHalfWeightCharacterStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (t : InfinityType K), t.IsPureOfWeight 1 →
    ∀ (S : Finset (FinitePlace K)),
      Disjoint S (S.map
        (AdelicFunctoriality.finitePlaceEquiv
          (IsCMField.complexConj K).toRingEquiv).toEmbedding) →
      ∃ φ : HeckeCharacter K,
        (∀ x, φ (AdelicFunctoriality.ideleClassComplexConj x) = (φ x)⁻¹) ∧
        (∀ x : (InfiniteAdeles K)ˣ,
          (φ.atInfinity x : ℂ) *
              ∏ τ : InfinitePlace K, ((‖(InfinityType.coordinate τ x : ℂ)‖ : ℝ) : ℂ) =
            (InfinityType.toCharacter t x : ℂ)) ∧
        ∀ w ∈ S, φ.IsUnramifiedAt w

end Langlands.Global
