# Generic principal series with a prescribed central character

Author: Worker 389.

This supporting module constructs, for every quasi-character `ω` of `K^×` and every rank
`r + 1`, quasi-characters `μ_1, …, μ_(r+1)` with `∏ μ_i = ω` and a generic irreducible admissible
object of `GL_(r+1)(K)` that is a subquotient of the normalized principal series
`principalSeries K r μ = i(μ_1, …, μ_(r+1))` and has central character `ω`. It also shows that
twisting by a quasi-character `η` carries such constituents of `i(μ)` to constituents of
`i(μ_1 η, …, μ_(r+1) η)`. These are the "principal-series models" `π₀` used in the proof of
Henniart (1986), Lemma 4.2, whose gamma factors are compared through
`PrincipalSeriesPairGammaMatchStatement`. The module adds no axiom.

The topology on `K.Carrier` and on `GL_n(K.Carrier)` is the canonical one, installed by the
named local instances `principalSeriesModelTopology`, `principalSeriesModelGLTopology` and
`principalSeriesModelGLTopologicalGroup`.

## Declarations

Namespace `Langlands.Automorphic.StableTwist`.

Subquotients, for any group `G` and complex representations. In the Library,
`IsSubquotientOf ρ π` (`Correspondence/UnramifiedNormalization.lean`) means that some
subrepresentation of `ρ` maps onto `π` by a surjective intertwining map.

- `isSubquotientOf_self`: `ρ` is a subquotient of itself (the whole space and the inclusion).
- `isSubquotientOf_of_equiv_left`: a subquotient of `ρ` is a subquotient of any `ρ'`
  equivalent to `ρ` (the subrepresentation is pulled back along the inverse equivalence and
  composed with the given surjection).
- `isSubquotientOf_twist`: twisting both `ρ` and `π` by the same character `χ : G →* ℂˣ`
  preserves `IsSubquotientOf ρ π` (the same subspace is invariant and the same linear map
  intertwines, since both actions are scaled by `χ(g)`).

Principal series:

- `quasiSmoothCharacter η`: `η` as a smooth character (open kernel).
- `characterBlockTwistEquiv μ η`: the twist of the rank-one block `μ ∘ det` by `η ∘ det` is
  `(μ η) ∘ det`.
- `principalSeriesTwistEquiv μ η`: the determinant twist of `i(μ)` by `η` is equivalent to
  `i(μ η)`, from the published `normalizedProductDeterminantTwistEquiv` applied blockwise.
- `exists_generic_subquotient_twist`: if a class `π` has a `ψ`-generic representative that is
  a subquotient of `i(μ)`, then every class `πη` with `IsCharacterTwist K η π πη` has a
  `ψ`-generic representative that is a subquotient of `i(μ η)`. Genericity passes through the
  twist by `isGeneric_quasicharacter_twist`; the subquotient relation by the two lemmas above
  and `principalSeriesTwistEquiv`.
- `exists_isCharacterTwist`: every class has a twist by every quasi-character
  (`isCharacterTwist_iff_eq_twist`).
- `principalSeries_hasGLCentralCharacter`: scalar matrices act on `i(μ)` by `∏ μ_i`
  (`hasScalarCharacter_normalizedProductInduced`; on each rank-one block the determinant of
  the scalar `a` is `a`).
- `rankOneSupercuspidal_isSquareIntegrable`: the rank-one object of a norm-one
  quasi-character is square-integrable modulo the center.
- `rankOneCuspidalDatum η` and `characterBlock μ`: the rank-one cuspidal datum of `η`, and the
  normalized product induction of the rank-one objects `μ_k ∘ det` along the shape of
  singletons.
- `characterBlock_isGeneric`: if every `μ_k` has norm one, `characterBlock μ` is `ψ`-generic.
  The singleton segments `[μ_k]` are segment heads and square-integrable, hence pairwise
  unlinked (`squareIntegrableSegmentNonlinkage`); the published Zelevinsky exhaustion
  `genericSegmentProductExhaustion` then gives genericity of the segment product, which is
  `characterBlock μ` up to the isomorphism `ofCuspidalsInducedIso`.
- `characterBlockEquiv μ`: `characterBlock μ` is equivalent to `principalSeries K r μ` (the
  factors differ by a `ULift`).
- `exists_unitary_mul_pow`: every quasi-character `ω` is `ω_u · ν^(r+1)` with `ω_u` of norm
  one and `ν` unramified. With `c = |ω(ϖ)|` for the uniformizer `ϖ`, `ν` is the unramified
  character with `ν(ϖ) = c^(1/(r+1))`, and `|ω(a)| = c^(ord a)` gives `|ω_u(a)| = 1`.
- `exists_generic_principalSeries_object`: the main result. With `ω = ω_u ν^(r+1)` as above,
  take `μ_1 = ω_u ν` and `μ_i = ν` for `i > 1`, so `∏ μ_i = ω`. The norm-one characters
  `(ω_u, 1, …, 1)` give a generic `characterBlock`; twisting by `ν` keeps genericity and gives
  `i(μ)` (`principalSeriesTwistEquiv`); transported to `characterBlock μ`, this generic
  (hence irreducible admissible) representation is the required object `A`. It is a
  subquotient of `i(μ)` through `characterBlockEquiv`, and its central character is
  `∏ μ_i = ω` by `principalSeries_hasGLCentralCharacter` transported along the same
  equivalence (`hasScalarCharacter_of_equiv`).

## Sources and provenance

Internal construction. Henniart, *On the local Langlands conjecture for GL(n): the cyclic
case*, Ann. of Math. 123 (1986) (`henniart-1986-cyclic`), proof of Lemma 4.2, printed p.158,
uses a generic constituent of the principal series attached to `(ω, 1, …, 1)`. The module
uses `(ω_u ν, ν, …, ν)` instead, an unramified twist of a principal series of norm-one
characters, because the Library's genericity criterion (Zelevinsky's classification) is
available in the square-integrable (norm-one) case; only the product `∏ μ_i = ω` matters for
the application.
