# Local cyclic base change of prime degree certified by σ-lifts

Module `Langlands.BaseChange.CertifiedLocalCyclicBaseChangeStatement`, namespace
`Langlands.BaseChange`. The module contains one declaration, the proposition
`CertifiedLocalCyclicBaseChangeStatement` (universe parameters `uK uV`, in this order). It is
a statement only: the module proves neither the proposition nor anything else.

This is interface E2 of the operator's external-inputs plan in the form that clause N′ of
`Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement` (the named external
input derived from Arthur–Clozel III.5.1) consumes: one local map with the numerical
properties of input (I3) that is also certified by σ-lift character identities.

## Notation

All names below are published Library declarations; none is restated here.

- `Langlands.Henniart.Numerical.CyclicPrimeStep.{uK} p` (module
  `Langlands.Correspondence.HenniartCyclicBaseChange`): a cyclic extension `M/L` of p-adic
  fields of prime degree. Its fields `S.base = L` and `S.top = M` are `PadicField.{uK} p`, so
  their carriers lie in `Type uK`; `S.embedding : L →ₐ[ℚ_p] M` makes `M` an `L`-algebra
  (`S.algebra`), for which `M/L` is Galois with a Galois group `S.Gal` of prime order.
- `Langlands.Henniart.Numerical.CyclicBaseChangeMap.{uK, uV} S`: the type of maps `Ch` that send,
  for every `k : ℕ`, a supercuspidal class of `GL_{k+1}(L)`
  (`SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat`) to a multiset of supercuspidal
  classes over `M` of positive ranks `k' + 1`.
- `Langlands.Henniart.Numerical.IsWeakCyclicBaseChange S Ch`: the weak clauses of local cyclic
  base change, namely (W1) rank and `Gal(M/L)`-invariance, (W2) invariance under twists by the
  characters `Ξ` of `L^×` trivial on the norms, (W3a)–(W3c) fibres and image, and (W4) the
  conductor identity.
- `IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ` (module
  `Langlands.BaseChange.SigmaLiftOnSupercuspidals`): for every `k`, every supercuspidal class
  `π` of `GL_{k+1}(L)` and every actual supercuspidal representative `A` of `π`, some
  irreducible admissible representation `τ` of `GL_{k+1}(M)` is, with a σ-intertwiner and a
  constant, a σ-lift of `A` (`IsSigmaLift σ (orderOf σ)`, Henniart–Lemaire II.2.7), and `Ch k π`
  is a supercuspidal support of `τ`. The `L`-algebra structure on `M` used in the type of `σ`
  is `S.embedding.toRingHom.toAlgebra`, which is definitionally the one of `S.Gal`.

## The statement

`CertifiedLocalCyclicBaseChangeStatement.{uK, uV}` says: for every prime `p` (with
`[Fact p.Prime]`) and every cyclic step `S : CyclicPrimeStep.{uK} p` there is a map
`Ch : CyclicBaseChangeMap.{uK, uV} S` such that

1. `IsWeakCyclicBaseChange S Ch`, and
2. `IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ` for every `σ : S.Gal` with `σ ≠ 1`.

In words: every cyclic extension of prime degree of p-adic fields has a base-change map on
supercuspidal classes that satisfies the numerical laws (W1)–(W4) and that sends each
supercuspidal class to a supercuspidal support of its σ-lift, for every nonidentity element
`σ` of the Galois group. In a group of prime order every `σ ≠ 1` is a generator, so
`orderOf σ` is the degree `[M : L]`, as the σ-lift of Henniart–Lemaire requires.

Clause 1 is input (I3), `Langlands.Henniart.LocalCyclicBaseChangeStatement.{uK, uV}`, for this
`S`: keeping the first clause for every `p` and `S` gives
`LocalCyclicBaseChangeStatement.{uK, uV}`. The second clause supplies the hypothesis on `Ch` in
clause N′ of `CyclicStrongBaseChangeSupportStatement` at the same local universes: for every
`S`, the map `Ch` provided here can be passed to clause N′ of
`CyclicStrongBaseChangeSupportStatement.{uK, uV, uF, uE, uP, uQ}`, whose hypothesis on `Ch` is
clause 2 verbatim. The converse of the first implication is not claimed.

## Universe levels

The universe parameters `uK` and `uV` are free, as in `LocalCyclicBaseChangeStatement.{uK, uV}`.
Three carrier levels occur:

- the p-adic fields `L` and `M` have carriers in `Type uK`;
- the supercuspidal classes in the domain and in the output of `Ch`
  (`SupercuspidalAutomorphicClass.{uK, uV}`) are isomorphism classes of representations in
  `SmoothRep.{0, uK, uV}`, so their representatives (such as `A` above) have carriers in
  `Type uV`;
- the lifted representation `τ` in `IsSigmaLiftOnSupercuspidals` lies in
  `SmoothRep.{0, uK, max uK uV}`, so its carrier is in `Type (max uK uV)`.

The parameters `uK` and `uV` are the first two universe
parameters of `CyclicStrongBaseChangeSupportStatement`, so the statement at `.{uK, uV}`
supplies maps for that premise at the same two levels. The reductions of
`Langlands.Automorphic.Unramified.StrongBaseChangeSupportReductionStatement` instantiate the
premise at `uK := uF, uV := max uF uE` (B5, B7) and at `uK := uV := uK` (B6); a derivation of
B5 or B6 along the routes described there uses this statement at the same levels.

## Why both clauses

The derivations of B5 and B6 from `CyclicStrongBaseChangeSupportStatement` need one map with
both properties. N′ applies only to a map certified by σ-lifts (clause 2) and carries a
supercuspidal support `s` downstairs to the support `s.bind Ch` upstairs. The rank clause (W1)
of clause 1 then controls the ranks: each `Ch k π` has total rank `k + 1`. The numerical laws
alone do not determine `Ch` (see the Markdown of `SigmaLiftOnSupercuspidals`), and (I3) alone
gives no certified map. The statement does not assert that `Ch` is unique.

## Intended proof and its obligations

This module contains no proof. The intended proof follows the route described in the Markdown
of `Langlands.BaseChange.LocalCyclicBaseChangeReductionStatement`, from the seven local σ-lift
statements named there (uniqueness, twists, existence for essentially square-integrable
representations, fibres, the structure and existence of σ-lifts of supercuspidal
representations, conductors):

1. Fix a generator `σ₀` of `S.Gal`. For a supercuspidal class `π`, let `P` be the σ₀-lift of a
   representative, unique up to isomorphism. By the structure statement,
   `P ≅ Π₁ × Π₁^{σ₀} × ⋯ × Π₁^{σ₀^{s-1}}` with `s = 1` or `s = [M : L]` (compare
   Arthur–Clozel, Chapter I, Lemma 6.10). Define `Ch k π` as the
   multiset of the classes of the blocks `Π₁^{σ₀^j}`, `j < s`, chosen as a function of the
   isomorphism class of `P`.
2. (W1)–(W4) are proved as in that route.
3. Clause 2 for `σ₀`: for every representative `A` of `π`, the σ₀-lift of `A` (obtained from `P`
   by `IsSigmaLift.transport`) has `Ch k π` as a supercuspidal support. This needs a comparison
   of the product `sigmaOrbitProduct` of the structure statement with the normalized parabolic
   induction used by `IsSupercuspidalSupport`.
4. Clause 2 for every `σ ≠ 1`. Each such `σ` is a power `σ₀^i` with `[M : L] ∤ i`, and clause 2
   requires a σ-lift for `σ` itself, with the same support `Ch k π`. So the σ-lift of a
   supercuspidal representation must not depend on the generator. Arthur–Clozel state this
   for tempered representations in Chapter I, Theorem 6.2 (c): the notion of local lifting does
   not depend on the choice of `σ`. None of the seven σ-lift statements compares σ-lifts for
   different generators, so this comparison is an obligation of a proof of the present
   statement, in addition to those premises.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8): II.2.7, Définition, printed p. 67 (the σ-lift); II.2.9, Remarques (2)
  and (4), printed p. 70; II.4.6–II.4.12, printed pp. 88–97 (σ-lifts of essentially
  square-integrable and supercuspidal representations).
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*,
  Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF page =
  printed page + 14): Chapter I, §6, Definition 6.1 and Theorem 6.2, printed p. 51, with the
  proof of Theorem 6.2 (c) on printed p. 57; Lemma 6.10, printed p. 62.
- Operator note `operator-external-inputs-plan-2026-11-16` (*Formalizing the large external
  inputs of the local Langlands correspondence for GL_n*, 16 November 2026, file
  `external-inputs-plan.tex`): the E2 paragraph of Section 2.5 (TeX line 233), and Section 4.6
  (TeX lines 730–737), where B5 and B6 follow from III.5.1 together with E2.
