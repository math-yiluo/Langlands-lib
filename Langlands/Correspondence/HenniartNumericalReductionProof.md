# Henniart's numerical correspondence: the counting reduction

Module `Langlands.Correspondence.HenniartNumericalReductionProof`, namespace
`Langlands.Henniart`. Proof of Task 5891 (`e69d09d4-6da8-4810-886b-664574e533f8`).
Authors: Worker 5733 wrote the Lean proof and the first version of this note
(shared draft of Task 5584, revision 1). Worker 5428 checked it and revised this note.

Universes: `uK` (p-adic fields), `uW` (Weil carriers) and `uV` (supercuspidal
carriers), independent.

## Statement: `NumericalOrbitReductionStatement.{uK, uW, uV}`

The theorem `Langlands.Henniart.numericalOrbitReduction` proves the published
proposition `Langlands.Henniart.NumericalOrbitReductionStatement.{uK, uW, uV}` of
module `Langlands.Correspondence.HenniartNumericalStatement`:

```
NumericalOrbitCountStatement.{uK, uW, uV} →
(∀ p [Fact p.Prime] (K : PadicField p) k (π : SupercuspidalAutomorphicClass K k.succPNat),
  Numerical.conductor K π ≠ ⊤) →
NumericalSurjectivityStatement.{uK, uW, uV}
```

In words, the theorem has two hypotheses:

- Orbit counts. For every p-adic field `K`, `k` and conductor `a`, consider the unramified-twist
  orbits of irreducible `(k+1)`-dimensional Weil classes that have Artin conductor `a`
  (`Numerical.weilOrbitStratum K k a`). Also consider the unramified-twist orbits of
  supercuspidal classes of `GL_(k+1)(K)` that have conductor `a`
  (`Numerical.supercuspidalOrbitStratum K k a`). Both sets are finite and they have the same
  `Set.ncard`.
- Finite conductors. Every supercuspidal class has a finite conductor, that is, a finite
  `firstFixedLevel`.

The conclusion: every numerical injection is surjective. A numerical injection
(`Numerical.IsNumericalInjection`) is a map that is injective, preserves conductors and
is compatible with unramified twists.

This module does not assert either hypothesis. The theorem adds no premise beyond the two
in the statement.

## Proof

Two helper lemmas in namespace `Langlands.Henniart.Numerical` restate the published orbit
criteria at a fixed rank:

- `weilOrbitClass_eq_iff`: two rank-`(k+1)` classes `σ, τ` have the same orbit class
  exactly when `weilUnramifiedTwist K k z τ = σ` for some `z : ℂˣ`.
  - The proof rewrites with the published
    `Langlands.VirtualRepresentation.Weil.unramifiedOrbitClass_eq_iff`, from module
    `Langlands.VirtualRepresentation.Weil.Twist`. That lemma states the same criterion for
    elements of the rank-indexed basis `Σ n, IrreducibleWeilClass K n`, using
    `twistBasisEquiv`.
  - The twisted basis element stays at rank `k.succPNat`. So an equality in the sigma type
    reduces to an equality of second components, by `Sigma.mk.inj_iff` and `eq_of_heq`.
  - The converse direction holds by definition (`rfl`): `weilUnramifiedTwist` is the
    twist of the basis element at that rank.
- `supercuspidalOrbitClass_eq_iff`: the same statement for supercuspidal classes and
  `supercuspidalUnramifiedTwist`. It follows from the published
  `Langlands.VirtualRepresentation.PadicSupercuspidal.unramifiedOrbitClass_eq_iff`, from
  module `Langlands.VirtualRepresentation.Supercuspidal.Unramified`, by the same argument.

The main proof runs as follows.

1. Fix `p`, `K`, `k`, a numerical injection `φ` and a supercuspidal class `π`. Its three
   parts are injectivity, conductor preservation and twist compatibility.
2. By the conductor hypothesis, the conductor of `π` is a natural number `a`
   (`WithTop.ne_top_iff_exists`).
3. The count hypothesis at `(K, k, a)` says that the supercuspidal stratum `T` of
   conductor `a` is finite. It also says `T` has the same `ncard` as the Weil stratum `S`.
4. For each orbit `c ∈ S`, choose (by `Classical.choose`) a Weil class `pick c` in the
   orbit `c` with Artin conductor `a`. Let `f c` be the orbit class of `φ (pick c)`. Then:
   - `f c ∈ T`, because `φ` preserves conductors and so `φ (pick c)` has conductor `a`.
   - `f` is injective on `S`. Suppose `f c₁ = f c₂`. The supercuspidal criterion gives
     a `z` with `supercuspidalUnramifiedTwist K k z (φ (pick c₂)) = φ (pick c₁)`.
     Twist compatibility rewrites the left side as
     `φ (weilUnramifiedTwist K k z (pick c₂))`. Injectivity of `φ` then gives
     `weilUnramifiedTwist K k z (pick c₂) = pick c₁`. The Weil criterion makes the orbits
     of `pick c₁` and `pick c₂` equal, that is, `c₁ = c₂`.
5. Apply Mathlib's `Set.surj_on_of_inj_on_of_ncard_le` to `f`, with the inequality
   `T.ncard ≤ S.ncard` from the equal counts and finiteness of `T`. It says that an
   injective map from `S` into a finite set `T` with `T.ncard ≤ S.ncard` hits every
   element of `T`.
6. The orbit of `π` lies in `T`, so it equals `f c` for some `c ∈ S`. The supercuspidal
   criterion gives a `z` with `supercuspidalUnramifiedTwist K k z (φ (pick c)) = π`. By
   twist compatibility, `φ` sends the Weil class `weilUnramifiedTwist K k z (pick c)` to
   `π`.

The proof does not use finiteness of the Weil stratum: `T` is finite and the two
cardinalities are equal.

Lean check (environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lake build):
- 0 errors and 0 warnings.
- `numericalOrbitReduction` is a theorem with level parameters `uK, uW, uV`.
- Its axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The proof is internal. The statement is the published `NumericalOrbitReductionStatement`
(Worker 14). Its Markdown, `HenniartNumericalStatement.md`, records the source conventions
and the orbit form of the counts.

The source is Henniart (1988), registered as `henniart-1988-numerical`. Printed page `p` is
PDF page `p − 495`.
- Théorème 1.2 is on printed p. 498 (PDF p. 3).
- In §2.6, printed p. 505 (PDF p. 10), Henniart defines `𝒜²_K(n, j, ϖ_K)`. This is the set
  of `π ∈ 𝒜²_K(n)`, the essentially square-integrable classes of `GL(n, K)`, with
  `ω_π(ϖ_K) = 1` and Swan exponent `s(π) ≤ j`.
- In §2.8, printed pp. 506–507 (PDF pp. 11–12), he assumes an injection
  `φ_d : 𝒢⁰_K(d) → 𝒜⁰_K(d)` for every divisor `d` of `n`. Each one preserves Swan
  conductors and is compatible with unramified twists.
  - He twists them on `𝒳_K`-orbits so that `ω_{φ_d(σ)}(ϖ_K) = det σ(ϖ_K)`.
  - He then builds an injection into `𝒜²_K(n, j, ϖ_K)` from the Weil-side set
    `𝒢²_K(n, j, ϖ_K)`. That set consists of irreducible classes `σ` of dimension `d | n`
    with Swan exponent `k` such that `kn ≤ dj` and `det σ(ϖ_K)^(n/d) = 1`.
- The counts give `|𝒢²_K(n, j, ϖ_K)| = |𝒜²_K(n, j, ϖ_K)|` (printed p. 507), so this
  injection is bijective for every `j`. Henniart concludes: "Il s'ensuit aussitôt que
  chaque φ_d est bijective également".

The Library statement replaces Henniart's counts with counts of unramified-twist orbits
of fixed rank and fixed conductor (see `HenniartNumericalStatement.md`). Henniart's counts
are of essentially square-integrable classes with bounded Swan exponent and normalized
central character. The proof here is the pigeonhole step for the orbit form: an injection
between finite sets of equal size is onto, applied to orbits and lifted back to classes
along a twist. The proof does not use Henniart's normalization of the central character at
`ϖ_K`. The orbit strata already identify classes that differ by any unramified twist.

The counts themselves and the finiteness of supercuspidal conductors are not proved here.

## Imported results

- `Langlands.Correspondence.HenniartNumericalStatement` (unchanged). It supplies the target
  and the definitions `Numerical.weilOrbitStratum`, `Numerical.supercuspidalOrbitStratum`,
  `Numerical.conductor`, `Numerical.HasArtinConductor`, `Numerical.weilUnramifiedTwist`,
  `Numerical.supercuspidalUnramifiedTwist` and `Numerical.IsNumericalInjection`. Through
  its imports it also supplies the two orbit criteria
  `Langlands.VirtualRepresentation.Weil.unramifiedOrbitClass_eq_iff` and
  `Langlands.VirtualRepresentation.PadicSupercuspidal.unramifiedOrbitClass_eq_iff`, both
  proved from `Quotient.eq` and `MulAction.mem_orbit_iff`.
- Mathlib:
  - `Set.surj_on_of_inj_on_of_ncard_le` (`Mathlib/Data/Set/Card.lean`)
  - `WithTop.ne_top_iff_exists`
  - `Sigma.mk.inj_iff`
  - `eq_of_heq`
  - `Classical.choose` and `Classical.choose_spec`
