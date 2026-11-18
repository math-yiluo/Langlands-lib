import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# A multiplicity-one `O(n)`-type in every real standard module

Vogan's theorem on lowest `K`-types (Vogan 1981, Theorem 6.5.9(b)) says that the lowest
`K`-types of a `θ`-stable standard representation occur in it with multiplicity one, for every
continuous parameter. Theorem 6.6.15 identifies these standard representations with the
representations parabolically induced, as in Theorem 6.6.14, from sets of cuspidal data
`(MA, δ, ν)`, where `δ` is a discrete series representation of `M` (Definition 6.6.11). By
Lemma 6.6.12, every set of cuspidal data comes from a set of character data. This module
states the consequence used for `GL_n(ℝ)`: the `(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite
functions of every real standard module `realStandardModule n ds` of rank `n` contains some
irreducible continuous finite-dimensional representation of `O(n)` exactly once. For
`GL_n(ℝ)`, a block of nonzero weight carries a genuine discrete series, and a block of weight `0`
splits into two characters by induction in stages; see the paired Markdown.

This is a statement, not a proof.
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- **A multiplicity-one `O(n)`-type in every real standard module** (Vogan 1981,
Theorem 6.5.9(b) with Lemma 6.6.12 and Theorems 6.6.14–6.6.15). For every list `ds` of real blocks of total rank `n`,
there is an irreducible continuous matrix representation `τ` of `O(n)` of positive degree `d`
whose space of `O(n)`-intertwiners into the `O(n)`-finite functions of the real standard module
of `ds` is one-dimensional. Irreducible means that the only subspaces of `ℂ^d` stable under
every `τ k` are `0` and `ℂ^d`. -/
def RealStandardKTypeMultiplicityOneStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    ∃ (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ),
      Continuous τ ∧ 0 < d ∧
        (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ x ∈ W, τ k *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        Module.finrank ℂ (gkIntertwiners (realStandardRep n ds) d τ) = 1

end Langlands.Archimedean
