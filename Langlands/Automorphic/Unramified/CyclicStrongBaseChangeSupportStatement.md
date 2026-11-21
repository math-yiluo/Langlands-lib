# Strong cyclic base change on isobaric support and parameters

## Unproved external input

```lean
Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement.{uK, uV, uF, uE, uP, uQ} : Prop
```

This `def` names the support-and-parameter consequence of Arthur–Clozel III.5.1
in the Library's vocabulary. It is not a verbatim transcription of III.5.1:
the source compares local components of automorphic representations, whereas
this statement compares actual supercuspidal support multisets and archimedean
parameter lists of isobaric data. The definition supplies no proof of any of
its four conjuncts.

## Common hypotheses

In each clause, `F : Type uF` and `E : Type uE` are number fields, `E` is an
`F`-algebra with `[IsGalois F E]` and `[IsCyclic (E ≃ₐ[F] E)]`, and both
`AdeleQuotient F` and `AdeleQuotient E` are assumed compact. The degree is
prime: N′ requires `Module.finrank F E = S.degree` for a local cyclic prime
step `S`; S, C and R require `(Module.finrank F E).Prime` directly.

`DF : IsobaricData F` and `DE : IsobaricData E` are finite multisets of actual
positive-rank cuspidal classes, with repetitions and the empty datum allowed.
`DF.IsUnitary` and `DE.IsUnitary` require every constituent to be unitarizable.
`IsobaricData.IsWeakBaseChangeOf.{uF, uE, uP, uQ} DE DF` puts the upstairs
datum first and requires equal ranks and arithmetic weak base change between
attached spectral systems. There are no CM, totally complex,
regular-algebraic, conjugate-self-dual or supercuspidal hypotheses on the
global data.

The six universe parameters are independent and are ordered as in the
signature above: local fields, genuine local supercuspidal classes, global
fields `F` and `E`, and the spectral presentations over `F` and `E`,
respectively. The support relation uses actual local representation carriers
in `max uK uV`; it does not identify this universe with `uP` or `uQ`.

## N′: nonsplit finite places

First take a residue prime `p` with `[Fact p.Prime]`, a
`CyclicPrimeStep.{uK} p` named `S`, and a `CyclicBaseChangeMap.{uK, uV} S`
named `Ch`. The map takes a successor-rank index `k` and a genuine
supercuspidal isomorphism class of `GL_{k+1}(S.base)` to a multiset of such
classes of possibly differing positive ranks over `S.top`. For every
`σ : S.Gal` with `σ ≠ 1`, assume the published
`IsSigmaLiftOnSupercuspidals S.embedding Ch σ`. The algebra in `S.Gal` is
definitionally `S.embedding.toRingHom.toAlgebra`. Every nonidentity element
of this prime-order group is a generator. The certification requires a
σ-lift for each actual supercuspidal representative, with the specified
multiset as the support of the same lift. It uses the twisted-character
identity, not just the rank, fibre, image or conductor laws of
`IsWeakCyclicBaseChange`.

With the common global hypotheses and the degree equality, take
`v : FinitePlace F` and `w : FinitePlacesAbove E v` with `∀ w', w' = w`.
Proofs `hpF` and `hpE` identify both residue primes with `p`. The supplied
`ℚ_p`-algebra equivalences `αF`, `αE` identify the base and top fields of
`S` with the actual completions at `v` and `w.1`. The `letI` in each
equivalence type installs that completion's canonical `Padic p`-algebra,
as in `HasLocalSupercuspidalSupport`. The pointwise square requires
`αE (S.embedding x) = FiniteExtension.completionMap v w.1 (αF x)` for all
`x : S.base.Carrier`.

For any multiset `sF` of rank-tagged supercuspidal classes over `S.base`
satisfying `IsobaricData.HasLocalSupercuspidalSupport DF v hpF S.base αF sF`,
N′ concludes that `sF.bind (fun x => Ch x.1 x.2)` satisfies the same relation
for `DE` with `w.1`, `hpE`, `S.top` and `αE`. The support relation enumerates
all global constituents, attaches their actual local components via the
completion equivalence, and sums their supercuspidal supports. A local
support consists of classes whose normalized parabolic induction has the
local component as a subquotient. The enumeration, sum and `Multiset.bind`
retain every global and local occurrence. The clause takes an arbitrary
support witness, not a chosen support with a default value. It does not
assert existence of a certified map or of a downstairs support.

## S: split finite places

For every `v : FinitePlace F` and `w : FinitePlacesAbove E v`, take a prime
`p`, the two proofs `hpF`, `hpE` as before, and a common `K : PadicField.{uK} p`.
Here `αF` and `αE` identify `K` with the two actual completions, with the
same canonical-algebra convention. The equality
`αE x = FiniteExtension.completionMap v w.1 (αF x)` for every `x : K.Carrier`
forces the actual completion map to be an isomorphism. This presents a
split place of the prime-degree Galois extension; no uniqueness of `w` or
cyclic local step is required. For every witness `s` of the downstairs
support relation over `K`, the same multiset, including all ranks and
multiplicities, satisfies the upstairs relation under `αE`.

## C: places above a complex place

This is the unitary-isobaric base-change clause of
`CyclicWeakBaseChangeComplexPlaceStatement` (canonical B7). Take an actual
complex place `v` of `F`, a place `w : InfinitePlacesAbove E v.1`, and any
`ds : List ComplexCharacterData`. The downstairs predicate for `ds` holds
if and only if the upstairs predicate holds at `complexPlaceAbove v w`
for `complexPlaceParameterTransport v w ds`. In the selected coordinates,
transport is the identity if the upstairs embedding restricts to the
selected downstairs embedding, and conjugates each character otherwise.
Conjugation negates the weight and keeps the exponent.

Both archimedean aggregate predicates (complex and real) enumerate all
actual cuspidal constituents with their multiplicities. Each constituent's
literal parameter requires an embedding of the K-finite standard module
intertwining the compact and Lie actions at that place. The aggregate
predicate compares the supplied list to the concatenation of the
constituent lists up to permutation, with repetitions retained.

## R: places above a real place

Take an actual real place `v` of `F`, a place `w : InfinitePlacesAbove E v.1`,
and any `ds : List RealBlock`. Both parts use the actual upstairs place
`⟨w.1, hw⟩` with the indicated proof `hw`.

- If `hw : w.1.IsReal`, the real parameter predicates for the same list `ds`
  are equivalent **provided every induced block in `ds` has nonzero weight**.
  The condition is on the supplied list and guards the entire biconditional.
  A weight-zero induced block can be expanded into the two real character
  blocks of the same exponent (one trivial on the sign and one nontrivial)
  without changing its real standard module. But a global constituent can
  split into several upstairs constituents, and the aggregate predicate
  requires each block to belong to a single constituent. In particular an
  induced block of rank two cannot be distributed across two rank-one
  constituents. Thus the unrestricted same-list biconditional would be too
  strong. The comparison with normalized irreducible real Weil block
  presentations, including conjugacy of inducing characters and replacement
  of weight-zero induced blocks by two real characters, is an unproved
  local comparison, not a normalization theorem provided here.
- If `hw : w.1.IsComplex`, a real parameter for `DF` gives a complex parameter
  for `DE` with list `realParameterRestrictToComplex ds`, with no condition
  on the induced weights. A real character restricts along the complex norm
  to weight zero with the same exponent; an induced block `d` restricts to
  `[d, d.conj]`. The aggregate predicates allow permutations, so this list
  needs no new choice of coordinates: norm pullback is conjugation invariant
  and conjugation of an induced pair swaps its entries. The implication is
  forward only, since restriction forgets real-character parity.

## Sources and intended use

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula* (1989), source `arthur-clozel-1989-base-change`.
  III Definition 1.2, printed p. 199 (PDF p. 213), defines strong lifting
  at every finite and infinite place. III Definition 4.1, printed p. 202
  (PDF p. 216), describes induction from unitary cuspidal constituents.
  III Theorem 5.1, printed pp. 212–213 (PDF pp. 226–227), takes the
  prime-cyclic scope of III.4.2 and upgrades a weak lift to a strong lift.
  For N′ the local input is I Theorem 6.2, printed p. 51 (PDF p. 65),
  with the induction step in §6.2, printed pp. 52–53 (PDF pp. 66–67),
  and the extension via Langlands quotients after I Proposition 6.8,
  printed pp. 59–60 (PDF pp. 73–74). I Lemma 6.10, printed p. 62
  (PDF p. 76), describes the support shape for a supercuspidal lift, and
  I Lemma 6.12, printed p. 66 (PDF p. 80), explains how these lifts
  enter the generalized Steinberg blocks.
- Zelevinsky, *Induced Representations of Reductive p-adic Groups II. On
  Irreducible Representations of GL(n)* (1980), source
  `zelevinsky-1980-induced-ii`, Proposition 1.10, printed p. 174
  (PDF p. 11), supplies the supercuspidal support relation reused in
  `IsobaricData.HasLocalSupercuspidalSupport` and the uniqueness of the
  support multiset for an irreducible local representation.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL(n)
  en caractéristique non nulle* (2011), source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
  II.2.7, Définition, printed p. 67 (PDF p. 75), supplies the σ-lift
  relation used by Task 7513's certification. II.2.9, Remarque (2),
  printed p. 70 (PDF p. 78), deduces uniqueness up to isomorphism using
  II.2.8, Lemme, and II.2.9, Proposition, printed p. 69 (PDF p. 77).
  Task 7449's `Langlands.BaseChange.SigmaLiftUniquenessStatement` is the
  Library target for that uniqueness. The intended identification of
  the certified image support uses uniqueness of the σ-lift and of its
  supercuspidal support; neither is proved by this definition.
- The archimedean clauses use the published
  `IsobaricComplexPlaceParameter`, `ComplexPlaceParameterTransport`,
  `IsobaricRealPlaceParameter` and `ArchimedeanRestriction` modules for
  the parameter predicates and coordinate or restriction conventions.
  The local-to-global comparisons in those conventions are part of this
  unproved external input.

Task 7340's conditional derivation of B6 is to use N′ with E2's certified
map at each nonsplit completion step, with the support compatibility of
Arthur–Clozel I.6, and S at split steps. Support existence, uniqueness and
the Hecke-endpoint comparison belong to that derivation. Its conditional
derivation of B7 is to use C with the singleton relations and the
orbit-induction parameter sum. The standalone definitions of canonical
B6 and B7 do not take E2 or III.5.1 as hypotheses. The separate restricted
compatibility target of Task 7465 and the original Harris/cohomological
fallbacks are unchanged.
