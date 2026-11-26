# Refined orbit strata for Henniart's numerical correspondence

This module defines the Swan exponents, torsion numbers, refined orbit strata
and counts used in Option II of the operator's numerical local Langlands
route. It states four propositions and proves none of them. All mathematical
objects and twists are those of
`Langlands.Correspondence.HenniartNumericalStatement`.

## Sources and scope

The principal source is the registered operator note
`operator-numerical-llc-route-2026-11-16`, *The numerical local Langlands
correspondence for GL_n: counts on the two sides and the recommended route of
proof*, 16 November 2026. Its retained directory is
`literature/Operator note - Numerical local Langlands for GL_n, counts on the two sides and the recommended route (16 November 2026)`;
directory SHA-256:
`faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
The cited file is `numerical-LLC-route.tex`, §§2.2–2.3 (Swan conductor, slope,
torsion number, refined strata, `T_K`, and `C_K`, including Remark
`rem:range`) and §6.1 (the proposition `C(L,x,N)` and Lemma
`lem:countsurj`). These passages were read directly. The note supplies design
guidance and a paper proof of the lemma; no Lean proof is supplied here.

The Artin-integrality source is Jean-Pierre Serre, *Local Fields*, translated
by Marvin Jay Greenberg, Graduate Texts in Mathematics 67, Springer, 1979,
registered `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The retained file is `Serre--Local Fields--1979.pdf` in the central library.
Chapter VI §2, Theorem 1′, printed p.99 (PDF page 106), says that the Artin
conductor of every finite-group character is a nonnegative integer; the
ramification-sum expression is Proposition 2, Corollary 1′, pp.100–101
(PDF pages 107–108), and the proof of integrality is on p.102 (PDF page 109).
The Weil-class existence proposition below is the corresponding derived
target for the Library's finite inertia presentations, rather than a literal
statement in Serre about the Library's classes. Establishing presentations,
their surjective inertia restrictions, and applying finite-group integrality
are the work of its separate proof, `weilArtinConductorExistence` (module
`HenniartWeilArtinConductorExistenceProof`).

The source note treats non-archimedean local fields in §2 and p-adic fields in
§6. This module covers precisely all `K : PadicField.{uK} p`, for all primes
`p`, and all positive ranks `n = k + 1`. The field universe `uK`, Weil carrier
universe `uW`, and supercuspidal carrier universe `uV` are independent.

## Generality of the Weil-side definitions

The five Weil-side definitions below, `HasWeilSwan`, `weilTorsionNumber`,
`weilRefinedStratum`, `weilTwistIrreducibleCount` and `weilConductorCount`,
have the formulas of the general definitions with the same names in
`Langlands.Henniart.LocalNumerical` (module `HenniartLocalNumerical`), which
take any nonarchimedean local field `K` with a separable closure `Ω`, in any
characteristic. Their ingredients `HasArtinConductor`, `weilUnramifiedTwist`,
the Weil group and its degree map are the general ones at `K.Carrier`,
`AlgebraicClosure K.Carrier` and the valuative relation, topology and
local-field instance of `K.canonicalTopologicalData`: `HasArtinConductor` by
its definition, the others by unfolding. So each p-adic definition here unfolds
to the general one at these instances. The following examples check this by
`rfl`; the page of `HenniartLocalNumerical` checks the other declarations of its
table.

```lean
import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.Correspondence.HenniartRefinedStrata

noncomputable section
open Langlands Langlands.Henniart Langlands.Correspondence
universe uK uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

example {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} F k.succPNat) (s : ℕ) :
    Numerical.HasWeilSwan F σ s =
      LocalNumerical.HasWeilSwan F.Carrier (AlgebraicClosure F.Carrier) σ s := rfl

example {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} F k.succPNat) :
    Numerical.weilTorsionNumber F σ =
      LocalNumerical.weilTorsionNumber F.Carrier (AlgebraicClosure F.Carrier) σ := rfl

example (k s f : ℕ) : Numerical.weilRefinedStratum.{uK, uW} F k s f =
    LocalNumerical.weilRefinedStratum.{uK, uK, uW}
      F.Carrier (AlgebraicClosure F.Carrier) k s f := rfl

example (k s : ℕ) : Numerical.weilTwistIrreducibleCount.{uK, uW} F k s =
    LocalNumerical.weilTwistIrreducibleCount.{uK, uK, uW}
      F.Carrier (AlgebraicClosure F.Carrier) k s := rfl

example (k j : ℕ) : Numerical.weilConductorCount.{uK, uW} F k j =
    LocalNumerical.weilConductorCount.{uK, uK, uW}
      F.Carrier (AlgebraicClosure F.Carrier) k j := rfl
```

The GL-side definitions `HasSupercuspidalSwan`, `supercuspidalTorsionNumber`,
`supercuspidalRefinedStratum`, the proposition `CountsAgreeUpToSlope` and the
four proposition targets remain p-adic.

## Definitions in `Langlands.Henniart.Numerical`

1. `HasWeilSwan K σ s` means that there is a natural Artin conductor `a`
   satisfying `HasArtinConductor K σ a` and `a - (k + 1) = s`. Subtraction is
   truncated subtraction in `ℕ`. By the convention of route note §2.2,
   `a = n + sw` for irreducible classes of rank at least two; for rank one
   the ramified case has `a = sw + 1`, while the unramified case has
   `a = sw = 0`. Truncated subtraction therefore implements the specified
   Swan convention in every rank. The definition asserts no existence or
   uniqueness of an Artin conductor.
2. `HasSupercuspidalSwan K π s` means that some `a : ℕ` has
   `conductor K π = a` and `a - (k + 1) = s`. The equality coerces `a` to
   `WithTop ℕ`, because the published conductor is the first fixed-vector
   level and may formally be `⊤`. Thus the relation includes finiteness of
   that conductor. The Swan convention is again route note §2.2; the
   identification of first fixed-vector level with the epsilon conductor is
   inherited from the numerical-statement interface and is not proved here.
3. `weilTorsionNumber K σ` and `supercuspidalTorsionNumber K π` are the
   `Nat.card` of the subtypes of `z : ℂˣ` whose published unramified twists
   fix the respective class. They encode `t(x) = #{χ ∈ X_K : χx ≅ x}`
   from route note §2.2. The existing twists parametrize all unramified
   characters by their value `z` on geometric Frobenius on the Weil side,
   and on a uniformizer on the field side. Equality of classes expresses
   isomorphism. `Nat.card` is defined without a finiteness hypothesis and is
   zero for an infinite subtype; neither stabilizer finiteness nor
   divisibility of `t` by the rank is asserted in this module.
4. `weilRefinedStratum K k s f` is the set of classes in the published
   quotient `Weil.UnramifiedOrbitClasses (Weil.Local.localDegree K)` which
   contain a rank-`k + 1` representative `σ` with `HasWeilSwan K σ s`
   and `weilTorsionNumber K σ = f`. `supercuspidalRefinedStratum K k s f`
   uses `PadicSupercuspidal.UnramifiedOrbitClasses K` and representatives
   `π` satisfying the analogous Swan and torsion conditions. The existing
   orbit maps are applied to the rank-tagged classes `⟨k.succPNat, σ⟩`
   and `⟨k.succPNat, π⟩`. These are the existential images of the specified
   loci in the full orbit quotients, encoding `W_K(n,s,f)` and `S_K(n,s,f)`
   of route note §2.2. The definitions require no auxiliary choice of orbit
   representatives or proof of invariance.
5. `weilTwistIrreducibleCount K k s : ℕ∞` is
   `(weilRefinedStratum K k s 1).encard`, the number `T_K(k+1,s)` of route
   note §2.2. The definition uses torsion number one; the interpretation as
   irreducibility on inertia is not proved here.
6. `weilConductorCount K k j : ℕ∞` is the sum, with `n = k + 1`,
   \[
   C_K(n,j)=\sum_{d\mid n}\ \sum_{\substack{s\in\mathbb N\\ns\le dj}}
     T_K(d,s).
   \]
   In Lean the outer sum uses `n.divisors`. Since `n` is positive, each
   divisor `d` is positive and its rank parameter is `d - 1`. The inner
   sum uses `Finset.range (d * j / n + 1)`, the natural indices
   `0 ≤ s ≤ ⌊dj/n⌋`, equivalent to `ns ≤ dj` because `n > 0`.
   In particular `s = 0` is included, also when `j = 0`. This implements
   route note §2.3 and its Remark `rem:range`, which explicitly corrects
   the printed lower bound in Henniart's summation. No explicit formula
   for the count is asserted.
7. `CountsAgreeUpToSlope K x N` is `C(K,x,N)` of route note §6.1:
   for every `k s f : ℕ` with `k + 1 ≤ N` and
   `(s : ℝ) ≤ (k + 1) * x`, the Weil and supercuspidal refined strata have
   equal `encard`, and the supercuspidal stratum is finite. The slopes use
   real arithmetic, with natural rank and Swan exponent coerced to `ℝ`.
   There is no hypothesis `x ≥ 0` or `N ≥ 1`; the formula applies to every
   real `x` and natural `N`.

All stratum counts use `Set.encard : Set α → ℕ∞`, so an infinite set has
count `⊤`. Equality of these counts together with the stated
supercuspidal finiteness expresses equality of finite cardinalities on the
two sides. This avoids using a natural cardinality which would identify
infinite sets with empty ones.

## Four proposition targets in `Langlands.Henniart`

`WeilArtinConductorExistenceStatement.{uK,uW}` says that for every prime
`p`, every `K : PadicField.{uK} p`, every `k : ℕ`, and every irreducible
Weil class `σ` of rank `k + 1` with carrier universe `uW`, some natural
`a` satisfies `Numerical.HasArtinConductor K σ a`. Its provenance is the
derived application of Serre VI §2, Theorem 1′, described above. It is a
separate proposition, not an assumption added to the other targets.

`NumericalInjectionRefinedStrataStatement.{uK,uW,uV}` says that every
`Numerical.IsNumericalInjection K φ`, in every prime, field and rank,
preserves torsion numbers, sends every `HasWeilSwan K σ s` to
`HasSupercuspidalSwan K (φ σ) s`, and satisfies
`(weilRefinedStratum K k s f).encard ≤
(supercuspidalRefinedStratum K k s f).encard` for every `s f`.
Its provenance is route note §2.2 and the first sentences of the proof of
Lemma `lem:countsurj`, §6.1: injectivity and twist compatibility preserve
stabilizers, while conductor preservation gives Swan preservation, and the
induced orbit map is injective. These are the intended proof obligations,
not implemented proofs.

`CountingSurjectivityStatement.{uK,uW,uV}` states both implications of
route note §6.1, Lemma `lem:countsurj`, universally over primes `p`,
fields `K`, real bounds `x` and natural rank bounds `N`:

- If `CountsAgreeUpToSlope K x N` holds, then every numerical injection
  in every rank `k + 1 ≤ N` reaches every `π` with Swan exponent `s`
  satisfying `s ≤ (k + 1)x`. Reaching `π` means `π ∈ Set.range φ`,
  equivalently the existence of an actual Weil class mapping to it.
- Conversely, assume that every Weil class in ranks at most `N` has a
  natural Artin conductor and that in each rank at most `N` there exists
  a numerical injection reaching all such `π` of slope at most `x`.
  Then `CountsAgreeUpToSlope K x N` holds. The existence quantifier for
  the injection precedes the universal quantifiers over `π` and `s`.

The converse's explicit conductor hypothesis accounts for the fact that
`HasArtinConductor` is a relation based on finite inertia presentations:
conductor preservation alone does not give a natural conductor for a
preimage. The paper lemma uses the underlying existence implicitly. The
hypothesis here is precisely a bounded-rank hypothesis, with no global
integrality assumption or proof included. GL-side
finiteness in the intended proof is supplied by the published
`Langlands.Henniart.supercuspidalOrbitStratumFiniteness`; it is not added
as a hypothesis of this statement.

`RefinedStrataStatement.{uK,uW,uV}` is exactly
`NumericalInjectionRefinedStrataStatement ∧ CountingSurjectivityStatement`.
It packages preservation and the counting lemma, without adjoining
`WeilArtinConductorExistenceStatement`.

## Dependencies and proofs

The module imports the numerical-statement module
`Langlands.Correspondence.HenniartNumericalStatement` and Mathlib's
set-cardinality and natural-divisor interfaces. It introduces no
proofs or axioms. The proposition targets are proved in other modules:
`RefinedStrataStatement`, and with it its two components, as `refinedStrata`
(module `HenniartRefinedStrataProof`), and `WeilArtinConductorExistenceStatement`
as `weilArtinConductorExistence` (module `HenniartWeilArtinConductorExistenceProof`).
In particular no correspondence, finiteness theorem,
stabilizer theorem, or explicit counting formula is established by these
definitions.
