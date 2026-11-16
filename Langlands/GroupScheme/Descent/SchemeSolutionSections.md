# Compatible sections of an underlying scheme solution

Let `D : Datum p G` be an actual group-scheme Čech datum and let
`s : SchemeSolution D` be a supplied underlying scheme solution. All schemes
and test schemes lie in an arbitrary universe `u`. This internal adapter
generalizes `AffineDatumSections` to the interface without an affine field
and to surjective étale covers, which need not be quasi-compact.

`move_proj` proves that an arbitrary test-scheme point and its transported
point have equal quotient images. `sectionTransport_eq_iff` says that two
sections over two specified base coordinates with the same image in the
base are related by transport exactly when their quotient images agree.
The reverse implication uses the full kernel-pair lift and
`Datum.move_relation`. These results require no geometric assumption on `p`.

`sectionSubgroup (D := D) U` is the subgroup of sections `p*U ⟶ G.X` whose
values respect transport for every test scheme and every pair above the
same point of `U`. It depends on `D,U`, rather than on a chosen solution.
Multiplicative transport and precomposition preserve unit, product and
inverse, proving the subgroup laws.

`localSection f` restricts an actual section `f : U ⟶ s.obj` by slice
pullback and applies `s.iso.hom`. Its quotient composite is the projection
to `U` followed by `f.left`, so it belongs to the compatible subgroup.

Under `[Etale p] [Surjective p]`, faithful pullback proves
`localSection_injective`. Conversely, compatibility makes a local section
followed by `s.proj` equal on every pair above the same point of `U`.
The projection `p*U ⟶ U` is an effective epimorphism, so
`sectionDesc` descends this actual scheme map. Epimorphism cancellation
proves that it lies over `B`, and the supplied pullback square proves
recovery of the local section. This gives the actual equivalence

```lean
s.sectionEquiv U : (U ⟶ s.obj) ≃ sectionSubgroup (D := D) U
```

No affineness, field, smoothness, finite-type, commutativity, or
quasi-compactness hypothesis is used. The provenance is the imported
kernel-pair and transport constructions, Mathlib's effective epimorphisms
and faithful pullback, and the published affine section argument. No new
external-source assertion is made. This module constructs the section
equivalence from a supplied quotient; constructing that quotient and
reconstructing its group object are separate steps.
