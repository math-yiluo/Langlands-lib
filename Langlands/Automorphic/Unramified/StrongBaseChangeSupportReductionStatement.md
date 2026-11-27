# B5, B6 and B7 from strong cyclic base change on support and parameters

Module `Langlands.Automorphic.Unramified.StrongBaseChangeSupportReductionStatement`, namespace
`Langlands.Automorphic.Unramified`. The module contains six proposition definitions. Each is
an implication whose only hypothesis is one instantiation of
`CyclicStrongBaseChangeSupportStatement` and whose conclusion is a published interface, at all
of its universe parameters:

| Declaration | Universe parameters | Conclusion |
| --- | --- | --- |
| `CyclicWeakBaseChangeSupercuspidalReductionStatement` | `uF uE uV uW` | B5, `CyclicWeakBaseChangeSupercuspidalStatement.{uF, uE, uV, uW}` |
| `CyclicWeakBaseChangeSupercuspidalReductionTCStatement` | `uF uE uV uW` | `CyclicWeakBaseChangeSupercuspidalTCStatement.{uF, uE, uV, uW}` |
| `TowerBaseChangeHeckeComponentReductionStatement` | `uF uK uV uW` | B6, `TowerBaseChangeHeckeComponentStatement.{uF, uK, uV, uW}` |
| `TowerBaseChangeHeckeComponentReductionTCStatement` | `uF uK uV uW` | `TowerBaseChangeHeckeComponentTCStatement.{uF, uK, uV, uW}` |
| `CyclicWeakBaseChangeComplexPlaceReductionStatement` | `uF uE uV uW` | B7, `CyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}` |
| `CyclicWeakBaseChangeComplexPlaceReductionTCStatement` | `uF uE uV uW` | `CyclicWeakBaseChangeComplexPlaceTCStatement.{uF, uE, uV, uW}` |

The universe parameters of each declaration are those of its conclusion, in the same order.
The module states these implications and proves none of them; it proves neither the premise
nor any conclusion. Each reduction is a separate declaration, and none refers to another.

## The premise

`CyclicStrongBaseChangeSupportStatement.{uK, uV, uF, uE, uP, uQ}` (module
`Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`) is a named external
input: the support-and-parameter consequence of Arthur–Clozel, Theorem III.5.1 (a weak lift
between representations induced from unitary cuspidal ones is a strong lift), in the Library's
vocabulary. The Library states it as a proposition and this module does not prove it. For a
cyclic extension `E/F` of number fields of prime degree, unitary isobaric data `DF` over `F`
and `DE` over `E`, and `IsobaricData.IsWeakBaseChangeOf DE DF`, it has four clauses:

- **N′** (a finite place `v` with a single place `w` above it): for a cyclic step
  `S : Numerical.CyclicPrimeStep p` whose fields are identified with the completions `F_v` and
  `E_w`, and a local map `Ch` certified by σ-lifts for every `σ ≠ 1`
  (`IsSigmaLiftOnSupercuspidals`), every supercuspidal support `s` of `DF` at `v` gives the
  support `s.bind Ch` of `DE` at `w` (`IsobaricData.HasLocalSupercuspidalSupport`).
- **S** (split finite places): the same support upstairs as downstairs.
- **C** (complex places): `DF` has the aggregate complex-place parameter `ds` at `v` if and
  only if `DE` has `complexPlaceParameterTransport v w ds` at `w`.
- **R** (real places).

Its universe parameters are, in order: the p-adic fields of the local steps (`uK`); the
supercuspidal classes (`uV`; the attached local representations have carriers in
`max uK uV`); the number fields `F` (`uF`) and `E` (`uE`); the spectral presentations over `F`
(`uP`) and over `E` (`uQ`).

## Universe instantiation

### B5, B7 and their totally complex forms

The four declarations use `CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW}`.

- *Global fields and presentations* `uF, uE, uV, uW`: the levels of the conclusion. The weak
  base change hypotheses of B5 and of clause (1) of B7 are
  `IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}`; on singletons they are equivalent to
  `IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}`
  (`IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff`), the relation of the premise at
  `uP = uV`, `uQ = uW`. Clause (3) of B7 is the premise's clause C at these levels.
- *Local fields* `uK := uF`: the completion `F_v` lies in `Type uF`, so in N′ the base of the
  step can be the completion itself (`CompletionPadic.padicFieldAt v hpF`, with the identity
  as `αF`). The top must be a p-adic field in `Type uF` with a `ℚ_p`-algebra isomorphism `αE`
  onto the completion `E_w`, which lies in `Type uE`. Such a field exists because `E_w` is
  finite-dimensional over `F_v`, for example by transport of structure along an
  `F_v`-basis of `E_w`.
- *Local representations* `uV := max uF uE`: the attached local representations then have
  carriers in `max uF uE`. This universe holds copies (`SmoothRep.universeLift`) of the local
  components of presentations over `F`, whose carriers lie in `Type uF`, and over `E`, in
  `Type uE`, together with the normalized products of their supercuspidal blocks, so that one
  support multiset can be compared on both sides.
- This is the instantiation of the Library reduction
  `QuadraticWeakBaseChangeSplitSupportReductionStatement`. The derivation of B7 uses only
  clause C, whose statement does not involve the first two levels; they are chosen as for B5,
  so that one instance of the premise serves B5, B7 and that reduction.

### B6 and its totally complex form

The two declarations use `CyclicStrongBaseChangeSupportStatement.{uK, uK, uK, uK, uV, uW}`.

- *Global fields* `uK, uK`: a tower `T : PrimeCyclicBaseChangeTower F K` consists of
  intermediate fields of `K/F`, and each step is the extension
  `T.level i.castSucc → T.level i.succ` of two of them, whose carriers lie in `Type uK`.
- *Presentations* `uV, uW`: `IsSuccessiveWeakBaseChange.{uF, uK, uV, uW}` is, at each step,
  `IsobaricData.IsWeakBaseChangeOf.{uK, uK, uV, uW}` of the upper datum over the lower one.
- *Local fields* `uK`: the completions of the levels lie in `Type uK`, so in N′ the base and
  top of the step can be the completions of two adjacent levels themselves, with the
  identities as `αF` and `αE`.
- *Local representations* `uK`: the carriers `max uK uK = uK` hold the local components of the
  presentations at every level, whose carriers lie in `Type uK`.

The realizations `S`, `S'` over `F : Type uF` and the Hecke families over `K` are related to
the levels of the tower by the endpoint equivalences `T.bottomEquiv` and `T.topEquiv`. These
comparisons of global data do not involve the premise, so `uF` does not occur in its
instantiation.

### Totally complex forms

Each totally complex conclusion is the general one with `[NumberField.IsTotallyComplex F]`
inserted after `[NumberField F]`: it specializes the general conclusion to this extra
instance. Both reductions use the same universe instantiation of the premise, so each general
reduction implies its totally complex form by forgetting the instance. The converse is not
claimed.

## Intended derivations

The following describes how each implication is meant to be proved, with the inputs used. It
is a plan, not a proof. None of the inputs named here is a hypothesis of the implications, and
the comparisons listed are not proved in this module.

### B5

Data: `E/F` Galois of prime degree, a finite place `v` of `F` with a single place `w` above it,
cuspidal realizations `S` over `F` and `T` over `E` of index `r`, a presentation `P` of `T`
at `uW` whose component at `w` is supercuspidal, `HasUnitaryCentralCharacter S` and
`IsoClass.IsWeakBaseChangeOf T.isoClass S.isoClass`. The steps follow obligations 1–5 of
Section 4 of the Markdown of `CyclicWeakBaseChangeSupercuspidalStatement`.

1. *Unitary singletons.* Apply the premise to the singletons `DF` of `S.isoClass` and `DE` of
   `T.isoClass`. `DF` is unitary by
   `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter` and
   `IsobaricData.isUnitary_ofCuspidal`. B5 assumes nothing on `T`, so the unitarity of `DE` must
   be derived (obligation 1). The extension is cyclic because its Galois group has prime
   order. N′ holds for every unitary pair related by `IsobaricData.IsWeakBaseChangeOf`, so it
   applies to these singletons directly.
2. *The local step.* Since `w` is the only place above `v`, `E_w/F_v` is Galois of degree
   `[E : F]`. This gives `S_v : CyclicPrimeStep.{uF} p` with base `F_v`, top identified with
   `E_w` (see *Universe instantiation*), embedding induced by the completion map, and
   `Module.finrank F E = S_v.degree`.
3. *The certified map.* `Langlands.BaseChange.CertifiedLocalCyclicBaseChangeStatement.{uF, max uF uE}`
   gives `Ch` for `S_v` with (W1)–(W4) and the σ-lift certification that N′ requires. This is
   the certified form of interface E2 (input (I3) with σ-lift identities).
4. *Support downstairs.* The weak base change hypothesis supplies a presentation of `S` at
   `uV` (`IsoClass.isWeakBaseChangeOf_isoClass_iff`). Its component at `v` need not be
   irreducible: its unramified data give irreducibility and admissibility only outside a finite
   exceptional set of places, which may contain `v`. A supercuspidal support exists only for an
   irreducible representation (Zelevinsky 1.10; `IsSupercuspidalSupport` requires
   irreducibility), so the support is formed on another presentation of `S` at `uV`, whose
   local components are irreducible and admissible at every finite place.
   `Langlands.Automorphic.cuspidalAllLocalIrreduciblePresentationExistence` gives, from the
   supplied presentation, such a presentation with factors in `Type uF`, and
   `CuspidalSpectralPresentation.exists_small` realizes it with factors in `uV`. A copy of its
   irreducible component at `v` in `max uF uE` has a supercuspidal support `sF`
   (`Aubert.SupportGrading.exists_isSupercuspidalSupport`), so
   `DF.HasLocalSupercuspidalSupport v hpF S_v.base αF sF`.
5. *Support upstairs.* N′ gives `sF.bind (fun x => Ch x.1 x.2)` as a support of `DE` at `w`.
   The local theory of Arthur–Clozel, Chapter I, §6 (the extension after Proposition 6.8,
   Lemmas 6.10 and 6.12), which carries supports along local base change, enters through N′.
6. *Comparison with `P`.* The support relation of step 5 attaches to `T` the component at `w`
   of a presentation of some realization in the class of `T`. Transported to `T`
   (`CuspidalSpectralPresentation.transport`, which keeps the local classes), it becomes a
   presentation of `T` whose component at `w` is irreducible, because `IsSupercuspidalSupport`
   requires irreducibility. The component of `P` at `w` is irreducible because it is
   supercuspidal. Two irreducible local components of presentations of `T` have the same class
   (`CuspidalSpectralPresentation.localComponent_isoClass_eq`). By uniqueness of supercuspidal
   support (`GLSupercuspidalSupportUniquenessStatement`, proved in the Library as
   `Langlands.glSupercuspidalSupportUniqueness`), `sF.bind Ch` is the singleton of the class
   of that component, of rank `r + 1`.
7. *Ranks.* By (W1) every `Ch k π` has total rank `k + 1`, so it is nonempty. A bind that is a
   singleton therefore comes from a singleton `sF = {x}`, with `x` of rank `r + 1`. The
   irreducible component at `v` of the presentation chosen in step 4 is then an irreducible
   subquotient of the representation induced from one supercuspidal block of full rank, that
   is, it is supercuspidal.
8. *Actual component.* The presentation of `S` at `uV` chosen in step 4 therefore has a
   supercuspidal local component at `v`, which is
   `IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v` (obligation 5).

Only the rank clause (W1) of the weak clauses is used.

### B6

Data: a tower `T` of `K/F`, unitary chains `D`, `D'` of successive weak base changes starting at
the singletons of `S` and `S'`, unitary Hecke families `μ`, `μ'` of `K` at their ends, a place
`v` of `F` with a single place `w` of `K` above it, `¬ SameFiniteComponentsAt μ μ' w.1`, and
presentations `P` of `S` (at `uV`) and `P'` of `S'` (at `uW`). Suppose that the components of
`P` and `P'` at `v` have the same isomorphism class; the derivation reaches a contradiction.
This follows the last paragraph of the Markdown of `CyclicStrongBaseChangeSupportStatement`.

1. *Places of the tower.* Let `v_i` be the place of `T.level i` below `w`. Since `w` is the only
   place of `K` above `v`, `v_{i+1}` is the only place of `T.level (i+1)` above `v_i`: two places
   above `v_i` would give two places of `K` above `v`. So at every step N′ applies, with local
   degree equal to the prime degree of the step. Clause S, for split places, is not needed
   under this hypothesis.
2. *Certified maps.* For each step, `CertifiedLocalCyclicBaseChangeStatement.{uK, uK}` gives a
   certified map `Ch_i` for the step of completions at `v_i` and `v_{i+1}`. The same `Ch_i` is
   used for both chains.
3. *Bottom.* `D.StartsAtCuspidal S.isoClass` makes the bottom datum the pullback of the
   singleton of `S` along `T.bottomEquiv`, and likewise for `D'` and `S'`. The supplied
   components of `P` and `P'` at `v` are isomorphic but need not be irreducible, since `v` may
   lie in the exceptional set of their unramified data, and a supercuspidal support is formed
   only for an irreducible representation. The derivation therefore starts from the common
   irreducible local type:
   - Choose presentations `Q` of `S` and `Q'` of `S'` whose local components are irreducible
     and admissible at every finite place
     (`Langlands.Automorphic.cuspidalAllLocalIrreduciblePresentationExistence`, with
     `CuspidalSpectralPresentation.exists_small` for the carrier universe). Let `Q_v` and
     `Q'_v` be their irreducible components at `v`.
   - `Q_v` embeds in the local representation of `S` at `v`, so its isotypic part there is
     nonzero, and therefore everything, because `S` is irreducible
     (`OperatorRealization.isotypicPart_eq_top_of_ne_bot`). Pulling this back along the
     injective inclusion of the component of `P` at `v` into that local representation
     (`CompactSplitting.isotypicPart_comap_of_injective`) shows that this nonzero component
     is `Q_v`-isotypic. Likewise the component of `P'` at `v` is a nonzero `Q'_v`-isotypic
     representation.
   - The two supplied components are isomorphic, and a nonzero representation that is
     isotypic of two irreducible types forces the types to be isomorphic: `Q_v ≅ Q'_v`.

   Transport this common irreducible type from `v` to `v_0` along `T.bottomEquiv` and take its
   supercuspidal support `s_0` (as in step 4 of B5). Then `s_0` is a support of both bottom
   data.
4. *Up the tower.* N′ at step `i` carries a support `s_i` of the lower datum to
   `s_i.bind Ch_i` for the upper datum, for `D` and for `D'` (unitarity is assumed for every
   entry). Each intermediate datum is the upper datum of one step, with the support relation at
   presentations in `uW`, and the lower datum of the next, where N′ needs presentations in
   `uV`. Moving between the two uses comparisons of presentations across universes, such as
   the Library's `CuspidalSpectralPresentation.universeLift` and
   `CuspidalSpectralPresentation.exists_small`. At the top both chains have the same support
   at the place below `w`.
5. *Top.* `EndsAtHeckeFamily` (at `uV` for `D`, at `uW` for `D'`) gives the terminal data,
   transported to `K` along `T.topEquiv`, the Euler factors of `μ` and `μ'` at almost all
   places. Rigidity (strong multiplicity one, Jacquet–Shalika) identifies the constituents of
   each terminal datum with rank-one cuspidal classes attached to the characters `μ i`, so its
   support at `w` is the multiset of the local characters `(μ i).finiteComponent w.1`, and
   likewise for `μ'`. Since the two supports are equal, these multisets agree, which is
   `SameFiniteComponentsAt μ μ' w.1`: a contradiction.

Support existence and uniqueness, the transports along the endpoint equivalences and the
Hecke-endpoint comparison belong to this derivation.

### B7

1. *Clause (1).* Apply clause C to the singletons of `S.isoClass` and `T.isoClass`. The weak
   relation passes by `IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff`. The singleton of `S` is
   unitary as in step 1 of B5; the unitarity of `T`, which clause (1) does not assume, must be
   derived. `IsobaricData.hasComplexPlaceParameter_ofCuspidal` identifies the aggregate
   parameter of a singleton with the literal parameter of a permutation of the list. Returning
   to the exact lists of clause (1) needs a comparison of the literal predicate for permuted
   lists (parameter order).
2. *Clause (2).* Apply clause C to the singleton of `S.isoClass` and the orbit datum
   `IsobaricData.galoisOrbit F` of the class of `T`, with one constituent for each Galois
   automorphism. The obligations are: the orbit datum is unitary (from
   `HasUnitaryCentralCharacter T`); the singleton of `S` is unitary, which clause (2) does not
   assume; the orbit datum is a weak base change of the singleton of `S`, given the weak
   induction, including at inert unramified places (orbit induction); the parameter of each
   Galois conjugate of `T` at a place above `v` is that of `T` at the corresponding place, so
   that transporting `complexPlaceLanglandsSum v e ds` to a place `w` above `v` gives the
   aggregate list of the orbit datum up to `List.Perm`. The reverse direction of C then gives
   the aggregate parameter of the singleton of `S`, and the singleton theorem with the
   parameter-order comparison gives the literal one.
3. *Clause (3)* is clause C at the same levels.

## Sources

- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF
  page = printed page + 14): Chapter III, Definitions 1.1–1.2 (weak and strong lifting),
  printed p. 199; Theorem 4.2, printed p. 202; Theorem 5.1, printed pp. 212–213. Chapter I,
  §6: the extension of local lifting by the Langlands classification after Proposition 6.8,
  printed pp. 59–60; Lemma 6.10, printed p. 62; Lemma 6.12, printed p. 66.
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8): II.2.7, printed p. 67, the σ-lift used by the certification of the local
  maps.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*, Ann. Sci. ENS
  (1980), source ID `zelevinsky-1980-induced-ii`, Proposition 1.10, printed p. 174: existence
  and uniqueness of the supercuspidal support.
- Operator note `operator-external-inputs-plan-2026-11-16` (*Formalizing the large external
  inputs of the local Langlands correspondence for GL_n*, 16 November 2026, file
  `external-inputs-plan.tex`): Section 2.2, items B5–B7 (TeX lines 196–199); Section 4.6,
  the interface paragraph (TeX lines 730–737: B5, B6 and B7 are consequences of III.5.1 at one
  place, B5 and B6 together with E2, B7 at a place that splits); Section 4.8, the paragraphs
  after Remark 4.2 (TeX lines 905–914: B5 and B7 for the two branches of Harris's
  Proposition 4.8, B6 in place of A2 in the prime branch, all three from III.5.1).
