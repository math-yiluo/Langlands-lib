# Totally complex prime cyclic isobaric base change

In namespace `Langlands.Automorphic.Unramified`,
`CyclicPrimeIsobaricBaseChangeTCStatement` is a proposition definition. It is
the existing `CyclicPrimeIsobaricBaseChangeStatement` with only
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`.

## Hypotheses and conclusion

The actual fields `F : Type uF` and `E : Type uE` are number fields, `F` is
totally complex, and `[Algebra F E] [IsGalois F E]` specify the extension.
The degree `(Module.finrank F E)` is prime. No generator is chosen: a Galois
extension of prime degree is cyclic. Compactness of `AdeleQuotient F` and
`AdeleQuotient E` is explicit, as required by the imported automorphic objects.
There is no additional totally complex instance in the statement for `E`.

For every actual `DF : IsobaricData F` with `DF.IsUnitary`, there is an
actual `DE : IsobaricData E` satisfying:

- `DE.IsUnitary`;
- `IsobaricData.IsWeakBaseChangeOf DE DF`;
- every `DE' : IsobaricData E` with `DE'.IsUnitary` and
  `IsobaricData.IsWeakBaseChangeOf DE' DF` equals `DE`.

Uniqueness ranges over all unitary isobaric data over `E`. It is not restricted
to cuspidal data or to a chosen Galois-stable subclass.
`IsobaricData` is the existing finite multiset of positive-rank cuspidal
classes, including multiplicities and allowing mixed ranks. Its `IsUnitary`
predicate requires every constituent to be unitarizable. This is an explicit
condition on the data; no central-character hypothesis replaces it here.
The Library convention for a constituent in `IsoClass F r` is rank `r + 1`.
This target quantifies over arbitrary isobaric data and has no fixed `r` binder.

## Direction and universes

The declaration's universe order is `uF uE uV uW`: two field universes followed
by two spectral-presentation witness universes. The exact relation is
`IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} DE DF`, with the upper-field
datum first. Its existential spectral witnesses are for `DF` at universe
`uV` and `DE` at universe `uW`; it also includes equality of ranks.
Its arithmetic weak-base-change condition compares attached unramified Euler
polynomials at almost all finite places through residue-degree powers.
It asserts no comparison of local components at a specified ramified place.

## Provenance and scope

The original source is Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula* (1989), registered as
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Chapter III Definition 4.1 and Theorem 4.2(c), printed p.202 / PDF p.216,
use representations induced from unitary cuspidal data. The existing
`IsobaricCyclicTransferStatement` expresses this through constituent data
and the published weak-transfer relation; this file preserves its general
existence-and-uniqueness body and restricts only the base field.

This specialization is a derived statement target. It supplies no proof of
existence, uniqueness, or strong local compatibility, and does not prove the
general target from its totally complex restriction. A proof of the general
target would specialize by supplying the stated field data.
