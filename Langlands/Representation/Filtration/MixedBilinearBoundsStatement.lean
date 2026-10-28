import Langlands.Representation.Filtration.MixedBilinear

/-! Uniform targets for mixed bilinear bounds along actual finite filtrations. -/

namespace Langlands.MixedBilinear

universe uK uG uH uI uV uW

/-- The full mixed form-space length is bounded by the sum over actual graded
positions in both supplied filtrations, retaining multiplicities. -/
def FiltrationLengthBoundStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (H : Type uH) [Monoid H] (I : Type uI)
    (A : Rep.{uV} k G) (B : Rep.{uW} k H) (m n : ℕ)
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (χ : I → k),
    length a b χ A.ρ B.ρ ≤
      ∑ i : Fin m, ∑ j : Fin n,
        length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ

/-- A supplied graded pair bounds the whole form space if every other graded
pair has mixed form-space length zero. -/
def SinglePairLengthBoundStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (H : Type uH) [Monoid H] (I : Type uI)
    (A : Rep.{uV} k G) (B : Rep.{uW} k H) (m n : ℕ)
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (χ : I → k) (i₀ : Fin m) (j₀ : Fin n),
    (∀ i j, i ≠ i₀ ∨ j ≠ j₀ →
      length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ = 0) →
    length a b χ A.ρ B.ρ ≤
      length a b χ (f.gradedRepresentation i₀).ρ (g.gradedRepresentation j₀).ρ

/-- Length at most one makes every mixed covariant form a scalar multiple of
any supplied nonzero form; no existence of a nonzero form is assumed. -/
def LengthOneProportionalityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (H : Type uH) [Monoid H] (I : Type uI)
    (V : Type uV) (W : Type uW)
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k H W)
    (a : I → G) (b : I → H) (χ : I → k),
    length a b χ ρ σ ≤ 1 →
      ∀ B₀ B : forms a b χ ρ σ, B₀ ≠ 0 → ∃ c : k, B = c • B₀

/-- The uniform finite-filtration and scalar-proportionality target for mixed
bilinear forms over independent ambient monoids and carrier universes. -/
def FiltrationBoundsStatement : Prop :=
  FiltrationLengthBoundStatement.{uK, uG, uH, uI, uV, uW} ∧
    SinglePairLengthBoundStatement.{uK, uG, uH, uI, uV, uW} ∧
      LengthOneProportionalityStatement.{uK, uG, uH, uI, uV, uW}

end Langlands.MixedBilinear
