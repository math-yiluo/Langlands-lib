# Epsilon and gamma laws for sums, pairs and special blocks

Worker 33 wrote this module for task `e534647a` (row 11 of the local-factor
coverage map). The main declaration is
`Langlands.LocalFactor.PairBlockFactorStatement`. It is a proposition only. No
local-constant system is constructed or chosen, no proof of the factor laws is
claimed, and nothing is assumed as an axiom. The only proved results are the
continuity lemmas listed under "Helpers".

## Objects

Everything comes from the published common-closure interface:

- `CommonClosure`: a finite p-adic field `F`, finite intermediate extensions
  `E : Extension F` in its algebraic closure, their Weil subgroups `W_E`, the
  continuous exact virtual groups `R(W_E)` (`Virtual`), additive characters
  `ψ` and Haar measures `μ`.
- `NonabelianSystem`: an assignment `ε_E(x, ψ, μ)` with the system property
  `IsSystem F e ε` for a reciprocity family `e`.
- `CommonClosureWeilDeligne`: pairs `A : Pair F E`, the complex Weil–Deligne
  representations of `W_E` whose covariance character is the actual norm
  character `ν = normCharacter F E` (so `ν(Φ) = q_E^(-1)` for a supplied
  geometric Frobenius `Φ : GeometricFrobenius F E`, where `q_E` is the residue
  cardinality of `E`). It also supplies the full Weil–Deligne epsilon value
  `conditionalEpsilonValue`, equal to the system's value on the twisted class
  of the underlying representation times `det(-q_E^(-s) Φ | V^I / (ker N)^I)`
  (Tate (4.1.6)), and the L-value `spectralLValue` on its domain
  `SpectralRegularPoint`.
- `CommonClosureSpectral`: the system value `conditionalDeligneValue x s`
  `= ε_E(x ⊗ ω_s, ψ, μ)` of a virtual class at `s ∈ ℂ`, where `ω_s` is the
  spectral twist character `|·|^s`.
- `CommonClosureGamma`: the gamma value
  `γ(s, A) = ε(s, A) L(1 - s, A^∨) / L(s, A)` (`conditionalGammaValue`) on
  `RegularPoint F E A Φ`, the parameters at which both L-factors are regular. It
  also supplies the pair values `conditionalPairEpsilonValue` and
  `conditionalPairGammaValue`, which are these values of the actual tensor
  product `A ⊗ B` of pairs.
- `WeilDeligne.SpecialBlocks`: the special block `specialBlock ν m` on `ℂ^m`,
  with `W_E` acting on the `j`-th coordinate by `ν^j` (`0 ≤ j < m`) and
  monodromy shifting coordinate `j` to `j + 1`. It also supplies
  `block ν ρ m = ρ ⊗ specialBlock ν m`, with `ρ` given zero monodromy.

All values use the same `ψ`, the same arbitrary Haar measure `μ` and the same
`Φ` on both sides. Every representation is continuous, as the system requires.

## Definitions and helpers

`twistedFactor F E ρ k` is the zero-monodromy pair `ν^k ⊗ ρ`, where `ν^k` is the
`k`-th power of `ν` as a continuous character.

`IsUnramifiedTwist F E ω Φ t` says that the continuous character
`ω : W_E → ℂ^×` is trivial on the inertia subgroup `inertia F E` and that
`ω(Φ) = q_E^(-t)` (`spectralParameter`). Every unramified continuous character
satisfies this for some complex `t`, because `q_E > 1` and the complex
exponential maps onto `ℂ^×`. So both the absolute value and the phase of
`ω(Φ)` are arbitrary, and the image of `ω` need not be finite.

Helpers, proved in the module:

- `sum_isContinuous`: the direct sum of continuous pairs is continuous. This is
  the published `Weil.OperationClosure.continuous_prod`.
- `twist_isContinuous`: a pair twisted by a continuous character is continuous.
  This is the published `FiniteRepresentation.isContinuous_twist`.
- `specialBlock_isContinuous`: the special block for `ν` is continuous. The
  action is the composite of the continuous map `g ↦ (ν(g)^j)_j` into `ℂ^m`
  with the linear map `c ↦ Σ_j c_j · proj_j` into `End(ℂ^m)`. That linear map
  is continuous for the module topology (`IsModuleTopology.continuous_of_linearMap`).
- `block_isContinuous`: blocks of continuous factors are continuous, by the
  published `FiniteRepresentation.isContinuous_tensor`.
- `twistedFactor_isContinuous`: `ν^k ⊗ ρ` is continuous when `ρ` is.

## The statement

`PairBlockFactorStatement` says that for every prime `p`, every p-adic field `F`
and every extension `E`, the following seven laws hold for every system
`IsSystem F e ε`, every `ψ`, `μ` and `Φ`, and all continuous pairs.

1. `EpsilonDirectSum`: `ε(s, A ⊕ B) = ε(s, A) ε(s, B)` for every `s ∈ ℂ`.
2. `GammaDirectSum`: `γ(s, A ⊕ B) = γ(s, A) γ(s, B)`.
3. `GammaShortExact`: if `f : A → C` and `g : C → B` are morphisms of pairs
   (they commute with monodromy) and the underlying sequence
   `0 → A → C → B → 0` is short exact, then `γ(s, C) = γ(s, A) γ(s, B)`.
4. `PairDistributivity`: pair epsilon and pair gamma distribute over a direct
   sum in either leg:
   `ε(s, (A ⊕ A') ⊗ B) = ε(s, A ⊗ B) ε(s, A' ⊗ B)`, the same with the sum in
   the second leg, and the two corresponding identities for pair gamma.
5. `BlockGamma`: for continuous `ρ` and `n ≥ 0`,
   `γ(s, ρ ⊗ S_(n+1)) = ∏_{i=0}^{n} γ(s, ν^i ⊗ ρ)`.
6. `BlockPairGamma`: for continuous `ρ`, `ρ'` and `n, m ≥ 0`,
   `γ(s, (ρ ⊗ S_(n+1)) ⊗ (ρ' ⊗ S_(m+1))) = ∏_{i=0}^{n} ∏_{j=0}^{m} γ(s, ν^(i+j) ⊗ ρ ⊗ ρ')`.
7. `UnramifiedTwist`: if `IsUnramifiedTwist F E ω Φ t`, then twisting by `ω`
   shifts `s` to `s + t` in all of the following:
   - the system value of a virtual class: `ε(ω x, s) = ε(x, s + t)`, using
     `ExactGrothendieckGroup.continuousTwist`;
   - the system value of a class pair, with the twist in either leg:
     `ε((ω x) ⊗ y, s) = ε(x ⊗ y, s + t)` and `ε(x ⊗ (ω y), s) = ε(x ⊗ y, s + t)`,
     using `continuousTensorSame`;
   - the Weil–Deligne epsilon value `ε(s, ω ⊗ A) = ε(s + t, A)`;
   - the pair epsilon value `ε(s, (ω ⊗ A) ⊗ B) = ε(s + t, A ⊗ B)`;
   - the L-value `L(s, ω ⊗ A) = L(s + t, A)`;
   - the gamma value `γ(s, ω ⊗ A) = γ(s + t, A)`.

Here `S_(n+1)` is `specialBlock ν (n + 1)`, and every Weil–Deligne twist keeps
the monodromy of `A`.

### Regular points

Each gamma or L-value is evaluated only at a regular point of its own pair.
Each gamma or L clause therefore quantifies over one regular point for every
value it contains, and assumes that their complex parameters agree, or differ
by `t` in clause 7. The clauses thus assert the identities exactly at the
parameters where every value involved is defined. They say nothing about
points where some L-factor has a pole. For direct sums the regular domains
agree, because the Euler polynomials multiply. For short exact sequences and
blocks the domains can differ, since the kernel of monodromy is not exact.

## Provenance

The source is Henniart 2002 §§2.1–2.4. Henniart cites Tate [Corvallis, §4] for
these facts. His `σ` are representations of the Weil–Deligne group `W'_F`, and
his `ε` and `γ` are the factors with a fixed `ψ`. Here they are formulated over
every intermediate field `E` of the common closure, for the measure-dependent
values of an arbitrary supplied system. The changes are as follows.

- **2.1.** Henniart states that `L` and `ε` multiply on direct sums, so `γ` does
  too (clauses 1 and 2). He also states that `γ` alone multiplies when `σ` is an
  extension of `σ_1` by `σ_2` (clause 3). The direct-sum law for `L` is
  published as `WDEulerDirectSumStatement` in
  `Langlands.LocalFactor.WeilDeligneEulerStatement` (row 8). The dual of a sum
  is covered by `DualCompatibility` in `Langlands.WeilDeligne.OperationStatements`.
  Neither is repeated here. `L` and `ε`
  are deliberately not stated for short exact sequences, since they fail
  there (Tate (4.1.6): "they are not additive as functions of V, because
  `V_N` is not").
- **2.2.** Henniart writes `σ ⊗ σ'` for sums `σ = Σ σ_i` and `σ' = Σ σ'_j` of
  indecomposables. He states that `L`, `ε` and `γ` of the tensor are products
  over all `(i, j)`. Clause 4 is the binary form in each leg, for arbitrary
  pairs rather than indecomposable ones. Induction on the number of summands
  gives the finite products. The representation isomorphism
  `σ ⊗ σ' ≃ Σ σ_i ⊗ σ'_j` is not stated in this module; clause 4 is stated
  directly on the factor values. The `L` law of 2.2 follows from the published
  row-8 direct-sum law together with the invariance of `L` under isomorphism.
- **2.3.** Henniart's `St_n` restricts to `W_F` as `1, ν, …, ν^(n-1)`. That is
  the uncentered block `specialBlock ν n` used here, with weights indexed from
  `0`. In the extracted text of both formulas of 2.3 (the restriction of
  `St_n`, and `St_n ⊗ St_m`), a tensor symbol appears where a direct sum is
  meant. The dimensions, and the words "la somme porte sur les entiers `j`",
  show that these are direct sums. The representation-level identities of 2.3
  are published in `Langlands.WeilDeligne.BlockStatements` and are not
  repeated here.
- **2.4.** Henniart's formula is
  `γ(s, (ρ ⊗ St_n) ⊗ (ρ' ⊗ St_n'), ψ) = ∏_{i=1}^{n} ∏_{j=1}^{n'} γ(s, ν^(i+j-2) ⊗ ρ ⊗ ρ', ψ)`.
  With indices starting at `0` and block lengths `n + 1` and `m + 1`, this is
  clause 6. Henniart takes `ρ, ρ'` irreducible. The identity holds for every
  continuous `ρ, ρ'`, since its proof uses only multiplicativity of `γ` on
  exact sequences, so no irreducibility is assumed. Clause 5 is the case of a
  single block, that is `ρ' = 1` and `m = 0` in Henniart's formula; it is
  stated separately because the tensor with a trivial one-dimensional pair is
  not syntactically `ρ ⊗ S_(n+1)`. The `L` laws of 2.4 are published in row 8
  (`WDEulerBlockStatement` and `WDEulerPairBlockStatement`).

Why clause 3 holds, and why no semisimplicity is needed: Tate (4.1.6) defines
`ε(V) = ε(ρ) det(-Φ | V^I / V_N)` with `V_N = (ker N)^I`. Hence the
quotient correction and the Weil–Deligne L-ratio combine to the L-ratio of the
underlying representation, as rational functions of `q^(-s)`. So `γ` of a pair
equals `γ` of its underlying Weil representation, wherever both are defined.
For Weil representations, `I`-invariants are exact (inertia acts through a
finite quotient), and the system is additive on the exact virtual group. That
gives multiplicativity on short exact sequences, and with it clauses 3, 5 and 6.
This is the argument Henniart relies on; it is recorded here only to explain
the hypotheses and is not part of the statement.

Clause 7 is the change of variable built into the conventions. The system
value at `s` is `ε(x ⊗ ω_s)` (Tate (3.4.5) writes `ε(V ω_s, ψ, dx)`). The
Weil–Deligne correction is evaluated at `q_E^(-s) Φ`. An unramified `ω` with
`ω(Φ) = q_E^(-t)` equals `ω_t` on `W_E`, so `ω ⊗ ω_s = ω_(s+t)`. Twisting by
`ω` keeps `I`-invariants and monodromy, and multiplies the action of `Φ` by
`q_E^(-t)`. Tate (3.4.6) gives the explicit value
`ε(V ⊗ W) = ε(V)^(dim W) det W(π^(a(V) + dim V · n(ψ)))` for unramified `W`. That
explicit conductor exponent is stated with the conductor laws of row 9 (Worker
46), not here. The class-level clauses (the first three items of clause 7)
answer Worker 4's request in the coverage map. They are the unramified-twist
comparison for class pairs with arbitrary complex `t`, stated on Weil classes
because such twists need not preserve finite image.

## Sources

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`:
  G. Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587–602. §§2.1–2.2,
  printed p.593 (PDF p.7); §§2.3–2.4, printed p.594 (PDF p.8).
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: J. Tate,
  *Number theoretic background*, Corvallis Part II (1979). PDF page = printed
  page + 9.
  - (3.4.2), (3.4.5), (3.4.6), printed p.15 (PDF p.24): additivity, the
    `ω_s` twist and unramified twists.
  - (4.1.4)–(4.1.6), printed pp.20–21 (PDF pp.29–30): `Sp(n)`,
    indecomposables, and the Weil–Deligne `L`, `a` and `ε` with the
    non-additivity remark.
