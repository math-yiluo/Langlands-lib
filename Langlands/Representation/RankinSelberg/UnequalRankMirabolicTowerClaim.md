# Rigidity of pairings with tower data

Module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerClaim`,
namespace `Langlands.RankinSelberg.UnequalRankTower`.

This is a helper module for the proof of
`Langlands.RankinSelberg.UnequalRankMirabolicPairingRigidityStatement`
(JPSS 1983, Section 2.11, Lemma on printed p.399). It states no new
proposition. Its results are internal. `towerClaim` is the inner induction of
the proof: it handles the pairing between a representation of the mirabolic
group `P_j` and the level-`j` piece of `η` that comes from a tower datum. JPSS
handle this step with the classification of `P_j`-representations and finite
length of `η|_(P_j)`. This module avoids both. It uses the published `Φ⁻`
derivative results and the finiteness from `UnequalRankMirabolicTowerFinite`.

Notation is that of `UnequalRankMirabolicTower`: `P_j = mirabolic j F`,
`U_(N+1) = upperUnipotent (N + 1) F`, `θ_N = standardCharacter ψ N`, and
`IsTower ψ η h ρ q` is the tower structure, with `h : j ≤ N`.
`sp(s) = spectralPoint q_F s = q_F^(-s)`, where `q_F = T.residueCardinality`.
`R(ρ) = MirabolicRigidity.radicalSpan ρ`. A form
`β ∈ InvariantBilinear.forms X ρ χ_s` with `χ_s(g) = determinantWeight |·| g (-s)`
satisfies `β(X(g) x, ρ(g) y) = |det g|^(-s) β(x, y)` for `g ∈ P_j`.

## Polynomials and eigenvalues

`apply_aeval_of_eigen`: if a linear functional `f` on `M` satisfies
`f(S y) = l · f(y)` for an endomorphism `S` and a scalar `l`, then
`f(P(S) y) = P(l) · f(y)` for every complex polynomial `P`. This is `comp_aeval`
from `UnequalRankMirabolicTowerFinite`, applied with `S' = l · id` on `ℂ`.

## Claim `C(j)`

`towerClaim F T j`: let `F` be a `PadicField p` with topology data `T`, `ψ` a
unitary additive character, and `j ≤ N`. Let `η` be an admissible irreducible
representation of `GL_(N+1)(F)` on `W`. Let `ρ` be a smooth representation of
`P_j` on `A` and `q : W → A` a linear map with `IsTower ψ η h ρ q`. Let `X` be a
smooth irreducible representation of `P_j`. Then there is a finite set
`E ⊂ ℂ` such that, for every `s` with `sp(s) ∉ E`, every nonzero
`β ∈ forms X ρ χ_s` gives

- an isomorphism `X ≅ mirabolicCompactInduced ψ j`, and
- a nonzero `(U_(N+1), θ_N)`-equivariant functional on `η` (`HasFunctional`).

The universes of `W`, `A` and `V` are independent.

### Proof (induction on `j`)

**`j = 0`.** Take `E = ∅`. The isomorphism is the published `rankOne_equiv`.
Pick `x` with `β(x, ·) ≠ 0`. Then `IsTower.hasFunctional` (level `0`) turns the
functional `β(x, ·) ∘ q` into the required functional on `η`.

**`j + 1`.** The published `radicalTrivial_or_radicalGenerated` splits into two
cases.

*Case 1: `X` is radical-trivial.* Let `ϖ` be the uniformizer unit, so
`|ϖ| = q_F^(-1)`, and let `z = leviScalar ϖ ∈ P_(j+1)`. Since `X` is
radical-trivial, `X(z)` commutes with `X` (published `apply_mul_leviScalar`).
`X` has countable dimension (`rank_le_aleph0`), so Schur's lemma
(`exists_scalar_of_commute`) gives `X(z) = c` for a scalar `c`. Also
`IsTower.exists_polynomial` gives a nonzero `P` with `P(ρ(z)) y ∈ R(ρ)` for all
`y`. Take
`E = ⋃_(l a root of P) {w : w^(j+1) = (l c)⁻¹}`.
This set is finite.

Suppose `sp(s) ∉ E` and `β ≠ 0`. Pick `x, y` with `β(x, y) ≠ 0`. Then:

- `c ≠ 0`, because `X(z)` is invertible and `x ≠ 0`.
- `β(x, ·)` vanishes on `R(ρ)`: for a radical element `u`,
  `β(x, ρ(u) y') = β(X(u) x, ρ(u) y') = β(x, y')`. This uses `X(u) x = x`
  and `|det u| = 1` (`determinantWeight_radical`).
- `β(x, ρ(z) y') = (μ / c) β(x, y')` with `μ = sp(s)^(-(j+1))`. This comes from
  `β(X(z) x, ρ(z) y') = |det z|^(-s) β(x, y')`, `X(z) x = c x` and
  `determinantWeight_leviScalar`.

By `apply_aeval_of_eigen`,
`0 = β(x, P(ρ(z)) y) = P(μ / c) β(x, y)`, so `μ / c` is a root of `P`. Then
`sp(s)^(j+1) = ((μ / c) · c)⁻¹`, so `sp(s) ∈ E`, which is a contradiction. In
this case no nonzero form exists outside `E`.

*Case 2: `X` is radical-generated.* Let `X' = Φ⁻ X` and `ρ' = Φ⁻ ρ` be the
published unnormalized `Φ⁻` functors (`phiMinusUnnormalized T ψ j`) applied
to the smooth representations. Let `π = phiMinusQuotient T ψ j ρ`.

- `π ∘ q` is a tower datum for `ρ'` at level `j` (`IsTower.descend`). The
  successor law is `phiMinusUnnormalized_action`. The radical law is
  `phiMinusQuotient_radical` together with `theta_radicalElement`, since the
  `Φ⁻` character on `radicalElement c` is `ψ(c_j)`.
- If `X'` has `⊥ = ⊤` as subrepresentations, take `E = ∅`. The published
  `phiMinusPairingTransfer` turns a nonzero `β` into a nonzero form on
  `X' × ρ'`. But `forms_eq_zero_of_bot_eq_top_left` says that every such form
  is zero, so no nonzero `β` exists.
- Otherwise `X'` is irreducible: `phiMinusIrreducible` gives the dichotomy and
  `isIrreducible_of_dichotomy` concludes. The induction hypothesis for
  `(X', ρ', π ∘ q)` at level `j` gives a set `E'`. Take
  `E = {w / q_F : w ∈ E'}`. If `sp(s) ∉ E`, then
  `sp(s - 1) = q_F · sp(s) ∉ E'` (`spectralPoint_sub_one`). A nonzero `β` gives,
  by `phiMinusPairingTransfer`, a nonzero `β' ∈ forms X' ρ' χ_(s-1)`. The
  induction hypothesis then gives `X' ≅ mirabolicCompactInduced ψ j` and the
  functional on `η`. The published `nonempty_equiv_of_phiMinus` lifts the first
  isomorphism to `X ≅ mirabolicCompactInduced ψ (j + 1)`. It uses functional
  multiplicity one (`mirabolicFunctionalMultiplicity`) at levels `j` and `j+1`.
