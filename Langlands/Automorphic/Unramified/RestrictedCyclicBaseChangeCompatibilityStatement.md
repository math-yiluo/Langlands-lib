# Restricted cyclic base-change compatibility

`Langlands.Automorphic.Unramified.RestrictedCyclicBaseChangeCompatibilityStatement`
is a proposition definition for the restricted weak-to-strong compatibility
input used by the E3 program. The chosen-map formulation is an internal
interface composing the published local cyclic base-change and actual local
support vocabulary with global weak base change.

## One choice before all global data

For every rational prime `p` and every cyclic prime-degree local step `S`,
the proposition asks for a map
`Ch : Langlands.Henniart.Numerical.CyclicBaseChangeMap S`.
It satisfies `IsWeakCyclicBaseChange S Ch` and the compatibility clause for
every rank and every compatible globalization. The choice of `Ch` precedes
the number fields, places, rank, global realizations, and local classes, so
each globalization uses the same map for the given step.

Retaining `Ch` and its weak-law conjunct for each `p,S` gives the published
E2 proposition `Langlands.Henniart.LocalCyclicBaseChangeStatement`.
The strengthening here asks for a witness to E2 that also satisfies the
global compatibility clause. The compatibility claim applies to that witness.

The independent universe parameters are `uK`, `uV`, `uF`, `uP`, and `uQ`,
in that order. They describe the local fields, local class carriers, number
fields, base spectral presentations, and upstairs spectral presentations,
respectively. Both number fields have universe `uF`.

## Compatible globalization and base input

Let `F,E` be number fields with the compactness instances of their adele
quotients required by the existing cuspidal-class vocabulary. The base
field `F` is CM. The actual extension `E/F` is Galois and cyclic, and its
degree is `S.degree`, so it has the same prime degree as the local step.

Choose a finite place `v` of `F`. Its conjugate is the actual place
`vc := Langlands.Global.Harris.conjPlace F v`, and the two places are
distinct. There is exactly one actual place `w` of `E` above `v` and
exactly one actual place `wc` above `vc`. These are elements of the
published `FinitePlacesAbove` subtype, whose elements carry the genuine
lying-over proof.

The equalities `hpF` and `hpE` identify the residue primes at `v` and
`w.1` with `p`. The supplied algebra equivalences have directions

```text
αF : letI := (padicFieldAt v hpF).algebra
  S.base.Carrier ≃ₐ[Padic p] (padicFieldAt v hpF).Carrier
αE : letI := (padicFieldAt w.1 hpE).algebra
  S.top.Carrier ≃ₐ[Padic p] (padicFieldAt w.1 hpE).Carrier.
```

The carrier of `padicFieldAt` is definitionally the actual adic completion.
Each `letI` supplies its canonical `Padic p` algebra for the equivalence type.
The square required for every `x : S.base.Carrier` is

```text
αE (S.embedding x) = FiniteExtension.completionMap v w.1 (αF x).
```

The pointwise equality compares the given local embedding with the actual
completion map. The lying-over instance on `w` supplies the one required by
`FiniteExtension.completionMap`.

For every natural number `r`, take an actual
`T : CuspidalOperatorRealization F r` on \(\mathrm{GL}_{r+1}\).
The positive rank in the local class is written `r.succPNat`.
Require a unitary central character, regular algebraicity of `T.isoClass`,
and supercuspidal components of that class at both `v` and `vc`,
with base spectral-presentation universe `uP`.

The input
`π : SupercuspidalAutomorphicClass S.base r.succPNat`
is a genuine supercuspidal representation class over `S.base`.
`T.isoClass.HasPadicSupercuspidalClass.{uF,uP,uK,uV}
  v hpF S.base αF π` attaches it at `v`, with `p` implicit. The
relation identifies a representative of `π` equivariantly and
complex-linearly with a local component from an actual spectral
presentation, pulled back along the entrywise map given by `αF`.

## Upstairs datum and conclusion

Take every `D : IsobaricData E` whose constituents are unitarizable and
that is a weak base change of

```text
IsobaricData.ofCuspidal
  (PositiveRankCuspidalClass.ofFixedRank T.isoClass).
```

The weak relation `IsobaricData.IsWeakBaseChangeOf.{uF,uF,uP,uQ}` requires
equal total rank and arithmetic weak base change between attached spectral
systems. The upstairs system uses every global constituent of `D` with
its multiplicity. The scope includes both the singleton and the
noncuspidal orbit sum used in E3.

The conclusion is directly
`D.HasLocalSupercuspidalSupport.{uF,uQ,uK,uV}
  w.1 hpE S.top αE (Ch r π)` at `w.1`, with `p` implicit and
upstairs spectral universe `uQ`.
It asserts the existence of actual local components of every global
constituent and of supercuspidal supports for those components, whose
multiset sum is `Ch r π`.

The codomain of `Ch` is a multiset of pairs
`Σ k : ℕ, SupercuspidalAutomorphicClass S.top k.succPNat`.
A pair records an index `k` and a genuine local supercuspidal class of
rank `k+1`. A local support can have several smaller-rank entries
for one global constituent. Repeated global constituents contribute
repeated copies of their local supports, and repeated entries within
each local support also retain their multiplicities. The conclusion concerns
the total local support at `w`. The place `wc` enters the globalization
hypotheses.

## Provenance and proof boundary

The operator's plan, registered as
`operator-external-inputs-plan-2026-11-16`, Section 4.6, Interface and
final recommendation (`external-inputs-plan.tex`, lines 726--773),
requires restricted Arthur--Clozel III.5.1 alongside B5--B7 as a
separate premise for E3. The common chosen witness is the project's
formulation of the compatibility between E2 and E3.

James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120,
Princeton University Press, 1989, registered as
`arthur-clozel-1989-base-change`, provides the mathematical source for the
following parts of the interface.

- III.1.1--III.1.2, printed p.199 / PDF p.213, distinguish weak lifting
  at almost all unramified places from strong lifting at every place.
- III.4.1 and III.4.2(c), printed p.202 / PDF p.216, use representations
  induced from unitary cuspidal data and assert weak base change in that
  class for cyclic prime-degree extensions.
- III.5.1, printed p.212 / PDF p.226 (proof continues on printed p.213 /
  PDF p.227), promotes a weak lifting in that class to a strong lifting.
- I.6.2, printed p.51 / PDF p.65, first gives local lifting for tempered
  representations. The discussion after I.6.8, printed pp.59--60 /
  PDF pp.73--74, extends it using Langlands classification.

The restriction specializes the base to a regular-algebraic
cuspidal class over a CM field with supercuspidal components at two
distinct conjugate places. Arthur--Clozel's local lifting supplies the
mathematical model for the chosen map. The Lean statement requires both
the published W1--W4 weak laws and the global compatibility property
for that map.

This module defines the proposition. Its proof belongs to the E3 program:
compatibility of Henniart's candidate with weak cyclic base change of prime
degree.
