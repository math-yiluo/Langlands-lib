# L-factors of pairs: supercuspidal, square-integrable and tempered representations

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
the L-factor computations of Section 8 of Jacquet, Piatetski-Shapiro and
Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983):
Proposition (8.1), Theorem (8.2) with its statement (6), and Proposition
(8.4). The L-factors are the relations `IsPadicPairLPolynomial` and the
rank-symmetric `IsPadicSymmetricLPolynomial` of the module `PadicPairFactors`.
The induced representations are the published normalized block inductions
`PadicField.canonicalNormalizedProductInduced` of `Induction/BlockFactors`,
with the block shapes `succBlockShape` of `MultiplicativityStatement`. The
module defines `IsIrreducibleComponent`, `centeredSegmentBlocks` and six
statements, none of them proved.

## Source

JPSS 1983 (registered source `jpss-1983-rankin-selberg`; printed page = PDF
page + 365). The pages below were read visually from the scan.

- **(8.1), printed page 443.** "We assume first that `r ≥ t` and that `π` is
  irreducible supercuspidal. Then `π` is generic …" **Proposition.** Suppose
  `π` is an irreducible, supercuspidal representation of `G_r` and `σ` a
  representation of Whittaker type of `G_r` [sic, for `G_t`].
  (i) If `r > t`, then `L(s, π × σ) = 1`.
  (ii) If `r = t` and `σ` is irreducible, then `L(s, π × σ) = ∏(1 - a q^{-s})^{-1}`,
  where the product is taken over all complex numbers `a` of the form
  `a = q^{-u}` such that `π ⊗ α^{-u} ≃ σ`.
- **(8.2), printed pages 443-445.** An irreducible admissible representation is
  square-integrable if its central character is unitary and its matrix
  coefficients are square-integrable on `Z_r\G_r`; `π ⊗ α^u` with `π`
  square-integrable is quasi-square-integrable. Let `a` divide `r`, `π_0` be an
  irreducible supercuspidal representation of `G_a`, `m = r/a`, `Q` the
  (upper) standard parabolic subgroup of `G_r` of type `(a, a, …, a)`, and
  `π_i = π_0 ⊗ α^{(m+1)/2 - i}`, `1 ≤ i ≤ m`. Then (display (1))
  `ξ = Ind(G, Q; π_1, …, π_m)` has a unique component which is
  quasi-square-integrable, denoted (display (2)) `π = σ(π_1, …, π_m)`; it is
  also the unique generic component. Similarly `t = bn`, `σ_0` is an
  irreducible cuspidal representation of `G_b`, (display (4))
  `σ = σ(σ_1, …, σ_n)` with `σ_i = σ_0 ⊗ α^{(n+1)/2 - i}`, and `t ≤ r`.
  **Theorem.** With the above assumptions, (display (5))
  `L(s, π × σ) = ∏_{i=1}^{n} L(s, π_1 × σ_i)`.
  *Proof.* The critical point is (display (6)): "If `π` and `σ` are
  square-integrable, then `L(s, π × σ)` has no poles in the half-plane
  `Re(s) > 0`." Section (8.3), printed pages 448-451, proves (6) from the
  absolute convergence of the integrals for `Re(s) > 0`.
- **(8.4), printed pages 451-452.** "A tempered representation `π` is a
  representation of the form (display (1)) `π = Ind(G_r, Q; π_1, …, π_m)`,
  where the `π_i` are square-integrable." Similarly (display (2))
  `σ = Ind(G_t, R; σ_1, …, σ_n)` with square-integrable `σ_i`.
  **Proposition.** With the above assumptions,
  `L(s, π × σ) = ∏ L(s, π_i × σ_j)`, the product taken over `1 ≤ i ≤ m`,
  `1 ≤ j ≤ n`. In particular `L(s, π × σ)` has no pole in the half-plane
  `Re(s) > 0`.
- **Normalized induction, printed pages 376-377,** and the convention (2.12),
  printed page 403, for factors with the smaller rank first: see
  `MultiplicativityStatement.md` and `PadicPairFactors.md`.

Henniart, *Une caractérisation de la correspondance de Langlands locale pour
GL(n)*, Bull. SMF 130 (2002) (registered source
`henniart-2002-characterization`), §3.3, printed page 598 (text layer read),
restates JPSS (8.1) as: for supercuspidal `π, π'`,
`L(s, π × π') = ∏ L(s, χ)`, where `χ` runs over the quasicharacters of `F^×`
(the unramified ones suffice) with `π ≃ χ π'^∨`.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data
(residue cardinality `q`, normalized absolute value), `ψ` is a
`UnitaryAdditiveCharacter` of `F`, and `ν` is in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
Supercuspidality, square-integrability and the twists use the canonical
topology. `α = |det|` is the published `determinantNorm`, and the twist
`π ⊗ α^s` by a real power is the published `realPowerTwist`.

- `IsIrreducibleComponent ξ π`, for complex representations of any group
  (carriers in independent universes): `π` is irreducible (Mathlib's
  `Representation.IsIrreducible`) and some Mathlib `Subrepresentation` `U` of
  `ξ` has a surjective intertwiner onto `π`. That is, `π` is isomorphic to a
  quotient of a subrepresentation of `ξ`: an irreducible subquotient, JPSS's
  "component".
- `centeredSegmentBlocks F m π₀ i = π₀ ⊗ α^{m/2 - i}` for `i : Fin (m + 1)`.
  With `M = m + 1` blocks numbered from `1`, JPSS's
  `π_{i+1} = π_0 ⊗ α^{(M+1)/2 - (i+1)}` has exponent `m/2 - i`. So the family
  is JPSS's `(π_1, …, π_M)` in order, and the block `0` is JPSS's `π_1`.
- `SupercuspidalUnequalRankLFactorStatement` ((8.1)(i)): for `t < r`, an
  irreducible `π` of `GL_{r+1}(F)` satisfying the published `IsSupercuspidal`,
  and `σ` of `GL_{t+1}(F)` satisfying the published `IsOfWhittakerType` for
  `standardCharacter ψ`, `IsPadicPairLPolynomial F ψ ν.val π σ 1`.
- `SupercuspidalEqualRankLFactorStatement` ((8.1)(ii)): for an irreducible
  supercuspidal `π` and an irreducible `σ` of Whittaker type, both of
  `GL_{r+1}(F)`, there is a finite set `A` of complex numbers such that `a ∈ A`
  exactly when `a = q^{-u}` for some complex `u` for which some
  `χ : F^× →* ℂ^×` with `χ(x) = |x|^{-u}` for all `x` makes
  `π ⊗ (χ ∘ det)` equivalent to the smooth contragredient `σ̃` (published
  `smoothContragredient`); and
  `IsPadicPairLPolynomial F ψ ν.val π σ (∏_{a ∈ A} (1 - a X))`.
  The character `χ` is `α^{-u}` on `F^×`; it is determined by `u`.
- `SquareIntegrableLFactorStatement` ((8.2), display (5)): for `a, m, r` with
  `∑_{i < m+1} (a + 1) = r + 1` (`m + 1` blocks of size `a + 1`), and `b, n, t`
  likewise; irreducible supercuspidal `π₀` of `GL_{a+1}(F)` and `σ₀` of
  `GL_{b+1}(F)`; `π` of `GL_{r+1}(F)` essentially square-integrable (published
  `IsEssentiallySquareIntegrable`) and an irreducible component of the
  normalized induction of `centeredSegmentBlocks F m π₀` from the upper block
  parabolic of type `(a+1, …, a+1)`; `σ` likewise for `σ₀`; and `t ≤ r`: there
  are polynomials `P` and `Q j` with `IsPadicPairLPolynomial F ψ ν.val π σ P`,
  `IsPadicSymmetricLPolynomial F ψ ν.val (π₀ ⊗ α^{m/2}) (σ₀ ⊗ α^{n/2 - j}) (Q j)`
  for every `j`, and `P = ∏_j Q j`.
- `SquareIntegrablePoleFreeStatement` ((8.2), display (6)): for irreducible
  `π` and `σ` satisfying the published `IsSquareIntegrable`, of any ranks
  `r + 1` and `t + 1`, there is `P` with
  `IsPadicSymmetricLPolynomial F ψ ν.val π σ P` and `P(z) ≠ 0` whenever
  `‖z‖ < 1`.
- `TemperedLFactorStatement` ((8.4)): for families `π i` of `GL_{m i + 1}(F)`,
  `i : Fin k`, and `σ j` of `GL_{n j + 1}(F)`, `j : Fin l`, all irreducible and
  square-integrable, with `∑ (m i + 1) = r + 1` and `∑ (n j + 1) = t + 1`,
  there are `P` and `Q i j` with `IsPadicSymmetricLPolynomial` of the two
  normalized inductions (shapes `succBlockShape m hm` and `succBlockShape n hn`)
  equal to `P`, of `(π i, σ j)` equal to `Q i j`, `P = ∏_i ∏_j Q i j`, and
  `P(z) ≠ 0` whenever `‖z‖ < 1`.
- `TemperedLFactorFormulasStatement` is the conjunction of the five statements.

An L-witness `P` has constant term `1`, and `L(s) = 1/P(q^{-s})`.

## Interpretation

- **The misprint in (8.1)(ii).** The printed condition `π ⊗ α^{-u} ≃ σ` lacks a
  contragredient; the statement uses `π ⊗ α^{-u} ≃ σ̃`. For `r = t = 1`,
  `π = χ_1` and `σ = χ_2`, the integral of Theorem 2.7 is Tate's integral for
  `χ_1 χ_2`, so `L(s, π × σ) = L(s, χ_1 χ_2)`, whose pole factor is
  `1 - χ_1χ_2(ϖ) q^{-s}` exactly when `χ_1 χ_2 = α^u` is unramified, with
  `a = χ_1χ_2(ϖ) = q^{-u}`. That is `χ_1 α^{-u} = χ_2^{-1}`, the corrected
  condition; the printed one would give the wrong answer, for instance the
  empty product for `χ_2 = χ_1^{-1}` with `χ_1^2` ramified. Henniart 2002
  §3.3 states the theorem with the contragredient: the factor `L(s, χ)` of an
  unramified `χ` is `(1 - χ(ϖ) q^{-s})^{-1}`, and with `χ = α^u`,
  `χ(ϖ) = q^{-u} = a`, his condition `π ≃ χ π'^∨` is exactly
  `π ⊗ α^{-u} ≃ σ̃`.
- **The set `A`.** Every nonzero complex number is some `q^{-u}`, and `u` is
  determined by `a` up to `2πi/log q`, which does not change `α^{-u}`. The
  statement asserts that the set of such `a` is finite and that `L` is the
  product of the factors `1 - aX`, each `a` once, as in the source (the poles
  are simple). Finiteness is part of the claim.
- **Whittaker type and genericity.** In (8.1) `σ` is of Whittaker type for
  `θ_ψ = standardCharacter ψ` (JPSS Section 2.1); `π` is not assumed generic,
  JPSS note that it is. In (8.2) and (8.4) no genericity is assumed. The
  relations require nonzero Whittaker functionals (`ψ` for the representation
  of larger rank, `ψ̄` for the other, as in JPSS), so the conclusions include
  the genericity of the representations, which JPSS cite (Gelfand-Kazhdan,
  [H.J. II]) and which is not proved in the Library.
- **Components.** JPSS define `σ(π_1, …, π_m)` as the unique
  quasi-square-integrable component of `ξ`, quoting Bernstein-Zelevinsky for
  existence and uniqueness. The statement assumes that `π` is an irreducible
  essentially square-integrable subquotient of `ξ` and so applies to that
  component; it neither asserts nor uses the uniqueness. The published
  `IsEssentiallySquareIntegrable` is "some real twist `ν^{-s}π` is
  square-integrable modulo the center", and the published `IsSquareIntegrable`
  is admissibility, a unitary central character and square-integrable matrix
  coefficients modulo the center for every Haar measure, as in JPSS (8.2). A
  complex exponent `u` in JPSS's `π ⊗ α^u` reduces to its real part, since
  the twist by `α^{i Im u}` preserves square-integrability. The same
  representation is Henniart's `St_m(ρ)` for `ρ = π_0 ⊗ α^{-(m-1)/2}` and the
  segment head of the Library's `Classification/Segments`; these
  identifications (Zelevinsky 9.1, 9.3) are not used or proved here.
- **Ranks.** JPSS's `a, m, r = am` are `a + 1`, `m + 1`, `r + 1` here; the
  hypothesis `∑_{i < m+1} (a + 1) = r + 1` is `(m+1)(a+1) = r+1`, in the form
  required by `succBlockShape`. In (8.2) `t ≤ r`, so `L(s, π × σ)` is the pair
  relation with `π` first; the factors `L(s, π_1 × σ_i)` have ranks `a + 1`
  and `b + 1` of either order and use the symmetric relation (JPSS (2.12)).
  (8.4) assumes no rank order and uses the symmetric relation throughout.
- **Parabolics and normalization.** (8.2) induces from the upper standard
  parabolic, as the Library does. (8.4) writes `Ind(G_r, Q; π_1, …, π_m)` and
  `Ind(G_t, R; σ_1, …, σ_n)` without restating `Q` and `R`; the statement uses
  the upper block parabolic of Section (8.2). JPSS's normalized induction
  (9), printed page 377, is `f(hg) = δ_Q^{1/2}(h) σ(h) f(g)`, which is the
  Library's normalization by the square root of `leviModulus` (see
  `MultiplicativityStatement.md`).
- **Tempered representations.** JPSS define a tempered representation as one
  of the form (8.4)(1) and quote [H.J. II] for its irreducibility. The
  statement takes the induced representation itself; irreducibility is
  neither assumed nor asserted, and the published analytic `IsTempered` is
  not used.
- **Poles.** `L(s) = 1/P(q^{-s})` has a pole at `s` exactly when
  `P(q^{-s}) = 0`, and `Re(s) > 0` exactly when `‖q^{-s}‖ < 1` (`q > 1`).
  Every `z` with `0 < ‖z‖ < 1` is some `q^{-s}`, and `P(0) = 1`. So "no pole in
  `Re(s) > 0`" is "`P(z) ≠ 0` for `‖z‖ < 1`".
- **Existence of factors.** The conclusions assert that the factors exist, as
  well as the identities: the nonvacuity parts of the relations (a compatible
  quotient measure and nonzero functionals) and the ideal generators of JPSS
  Theorem 2.7. None of this is proved in the Library. Each relation has at
  most one solution (`IsPadicPairLPolynomial.unique`,
  `IsPadicSymmetricLPolynomial.unique`).
- **Measures and field.** The additive measure `ν.val` is self-dual; the
  L-polynomials do not depend on it, and the statements hold vacuously if it
  does not exist. Every compatible quotient measure is quantified in the
  relations. `F` is a p-adic field, as in `PadicPairFactors`.
- **Universes.** In (8.1), (6) and (8.4) the two sides live in universes `uV`
  and `uW`; in (8.2) `π₀`, `σ₀`, `π`, `σ` live in `uV`, `uW`, `uV₂`, `uW₂`.
  The induced representations live in `max uF uV` and `max uF uW`.

## Not stated

The absolute convergence of the integrals for square-integrable inputs on
`Re(s) > 0` (Proposition (8.3)), the uniqueness and genericity of the
quasi-square-integrable component, the irreducibility of the tempered
inductions, and epsilon or gamma formulas (Section 8 states none) are not
part of this module. The L-factors of Langlands quotients (Section 9) are a
separate module.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `TemperedLFactorFormulasStatement` was inspected: it returns
`Prop`, has universe parameters `uF uV uW uV₂ uW₂`, and uses only `propext`,
`Classical.choice` and `Quot.sound`. There is no `sorry` and no new axiom.
