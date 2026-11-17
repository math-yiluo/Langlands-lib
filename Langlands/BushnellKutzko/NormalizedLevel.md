# Normalized level and containment of strata for `GL_n` over a p-adic field

Module `Langlands.BushnellKutzko.NormalizedLevel`, namespace `Langlands.BushnellKutzko` (the
namespace of the hereditary-order modules `LatticeChain`, `UnitFiltration` and `AdditiveDual`
that it builds on).

Sources:

- C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*,
  J. reine angew. Math. 375/376 (1987), 184–210, `bushnell-1987-hereditary-orders-gauss-sums`
  (PDF page = printed page − 183): (3.1), Remark (a) after (3.2) and (3.3), printed p. 196; Theorem 2′, printed pp. 196–197.
- C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*,
  Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln` (PDF page =
  printed page + 12): Introduction, printed pp. 8–10; notation, printed p. 19; (1.1.6), printed
  p. 22.
- Operator route note `operator-numerical-llc-route-2026-11-16`, §4.4 (definition of `ℓ(π)`
  before Lemma `lem:level`, printed p. 15).

## Setting

`p` is a prime and `F : PadicField.{u} p`. The module uses the Library's canonical structures
through local instances: the topology `F.canonicalTopologicalData.topology` and the valuation
`F.canonicalTopologicalData.valuativeRel` on `F.Carrier`, and the topology
`F.canonicalGeneralLinearTopology n` on `GeneralLinear n F.Carrier`. These are the instances
behind the Library's `AutomorphicClass F n` and `SupercuspidalAutomorphicClass F n`.

Write `V = Fin n → F.Carrier` and `A = Module.End F.Carrier V`. A lattice chain is an element
`𝓛 : LatticeChain 𝒪[F.Carrier] F.Carrier V` (an `𝔬_F`-lattice chain in `V`), with period
`𝓛.period` (BK93's `e(𝔄|𝔬_F)` for `𝔄 = 𝔄(𝓛)`), lattices `𝔓^j = 𝓛.endFiltration j ⊆ A` and
unit groups `U^j(𝔄) = 𝓛.unitFiltration j ⊆ Aut(V) = (Module.End F.Carrier V)ˣ`. All of these
come from the Library modules `LatticeChain` and `UnitFiltration`; none is redefined here.

Classes are elements of `SmoothDualClass.{0, u, uV} (k := ℂ) (G := GeneralLinear n F.Carrier)`:
irreducible admissible complex representations of `GL_n(F)` up to isomorphism, with carriers in
universe `uV`. For `n : ℕ+` this type is the Library's `AutomorphicClass F n`.

## `IsLevelOne F ψ`

For `ψ : AddChar F.Carrier ℂ`: `ψ a = 1` for every `a ∈ 𝔭_F = 𝓂[F.Carrier]`, and `ψ a ≠ 1` for
some `a ∈ 𝔬_F = 𝒪[F.Carrier]`. This is BK93's normalization of `ψ_F` ("null on `𝔭_F` but not
on `𝔬_F`", printed p. 19; Introduction, printed p. 8). These are exactly the two hypotheses on
`ψF` in the Library's `AdditiveDualityStatement`, which defines no named predicate for them.
Continuity follows from triviality on the open subgroup `𝔭_F`. This uses the same level-one normalization as the Library’s unitary additive character convention `F.canonicalTopologicalData.additiveConductor ψ = -1`; here the character is expressed as an `AddChar`, as in the published `AdditiveDualityStatement`.

## `unitSubgroup F 𝓛 j`

The subgroup of `GeneralLinear n F.Carrier` of matrices `g` whose linear map
`Matrix.GeneralLinearGroup.toLin g` lies in `U^j(𝔄(𝓛))`. It is the preimage of
`𝓛.unitFiltration j` under Mathlib's isomorphism `Matrix.GeneralLinearGroup.toLin` between
`GL_n(F)` and `Aut(V)`. This is the one fixed transport from `Aut(V)` to `GeneralLinear n
F.Carrier` used in every item of the module. `mem_unitSubgroup` unfolds membership.

## `normalizedLevelValues F n a : Set ℚ` (Bushnell 1987, (3.3))

The set of rationals `x` for which there are a lattice chain `𝓛` in `V` and `m : ℕ` with
`x = m / e(𝓛)` and `SmoothDualClass.HasFixedVector (unitSubgroup F 𝓛 (m + 1)) a`, i.e. a
representative of `a` has a nonzero vector fixed by the image of `U^{m+1}(𝔄(𝓛))`.

Bushnell 1987, (3.3), printed p. 196, defines `ℓ(𝔄, π)` as the least `ℓ ≥ 0` such that
`π|U^{ℓ+1}(𝔄)` contains the trivial character. For a fixed chain, the least element of
`{m / e(𝓛) : π^{U^{m+1}(𝔄(𝓛))} ≠ 0}` is `ℓ(𝔄(𝓛), π) / e(𝓛)`. So the least element of the whole
set is `min_𝔄 ℓ(𝔄, π) / e(𝔄)`, the quantity minimized in Bushnell 1987, Theorem 2′(ii),
printed p. 197.

## `IsNormalizedLevel F n a x : Prop`

`IsLeast (normalizedLevelValues F n a) x`: `x` is attained and is a lower bound. This is the
normalized level `ℓ(π) = min {m / e(𝔄) : π^{U^{m+1}(𝔄)} ≠ 0}` of the route note, §4.4. It is a
predicate rather than a function, because the existence of the minimum is statement L0
(`NormalizedLevelExistenceStatement`), not part of the definition.

## `ContainsStratum F n ψ a 𝓛 m b : Prop` (BK93's "`π` contains `[𝔄, m, m − 1, b]`")

Positive stratum indices are represented by `m : ℕ` with `1 ≤ m`, matching the natural-number index of the published `unitFiltration`. Every integer index `r ≥ 1` is uniquely the cast of such an `m` (`m = r.toNat`); the negative radical-power index is computed in `ℤ` as `-(m : ℤ)`. Thus this representation covers all positive integer strata.

For `ψ : AddChar F.Carrier ℂ`, a lattice chain `𝓛`, `m : ℕ` and `b ∈ A`, the conjunction of

1. `1 ≤ m`;
2. `b ∈ 𝔓^{-m}(𝓛)` (`𝓛.endFiltration (-(m : ℤ))`);
3. some representative `A` of `a` has a nonzero vector `v` with
   `g • v = ψ_A(b (g − 1)) • v` for every `g ∈ unitSubgroup F 𝓛 m`, where `ψ_A = ψ ∘ tr_A`
   (`traceCharacter ψ`) and `g ↦ ψ_A(b (g − 1))` is the Library's
   `elementCharacter (traceCharacter ψ) b`, evaluated at `toLin g`; `g − 1` is computed in `A`.

The conditions `m ≥ 1` and `b ∈ 𝔓^{-m}(𝓛)` are **conjuncts**, not hypotheses. The definition
does not require `ψ` to be of level one; the statements that use it assume `IsLevelOne F ψ`.

This is BK93's notion: for a stratum `[𝔄, m, m − 1, b]` with `m ≥ 1` and `b ∈ 𝔓^{-m}`, "`π`
contains the stratum" means that `π|U^m(𝔄)` contains the character `ψ_b(u) = ψ_A(b(u − 1))`
(BK93, Introduction, printed pp. 8–10; the character `ψ_b` is (1.1.6), printed p. 22, where
it is shown to be a character of `U^m(𝔄)` trivial on `U^{m+1}(𝔄)`). In Bushnell 1987, (3.1)
and Remark (a) after (3.2), printed p. 196, strata are written `(𝔄, m, θ)` with `θ` an
irreducible representation of `U^m(𝔄)/U^{m+1}(𝔄)`; for `m ≥ 1` this group is abelian and
`θ = ψ_b`.

## `isOpen_ker_determinantCharacter` (proved)

For `χ : HarmonicAnalysis.Quasicharacter F.Carrier` (a continuous homomorphism `F^× → ℂ^×`), the
character `χ ∘ det` of `GL_n(F)`, written `χ.toMonoidHom.comp GeneralLinear.determinant`, has
an open kernel. Proof: `χ ∘ det` is continuous (Library's
`canonicalTopologicalData.generalLinearDeterminant` is a continuous determinant), and a
continuous complex character of a nonarchimedean group has open kernel
(`isOpen_ker_of_continuous_complex_character`, with `GL_n(F)` nonarchimedean by
`canonicalGeneralLinearNonarchimedean`). This is the openness hypothesis of
`SmoothDualClass.twist`, so the twist `(χ ∘ det) ⊗ π` used by statement L2 needs no extra
hypothesis.
