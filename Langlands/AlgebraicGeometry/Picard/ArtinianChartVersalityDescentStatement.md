# Descent of pointed Picard versality along Artinian factorizations

Module: `Langlands.AlgebraicGeometry.Picard.ArtinianChartVersalityDescentStatement`.

Author: Worker 410, for task `43ead35e-c745-43e8-b3b6-b88e0a294ec9`.

## Statement

`ArtinianChartVersalityDescentStatement.{u}` is a Prop-valued definition.
For any commutative ring `R : Type u`, scheme `X` over `Spec R`, and map
`i : V → U` of schemes over `Spec R`, it considers actual line bundles
`L` on `X_U` and `M` on `X_V`, a field `K : Type u` over `R`, and a
specified map `p : Spec K → V` over `Spec R`. It assumes:

- an actual isomorphism `M ≅ i*L`, expressed by `Nonempty` of the
  isomorphism type;
- for every augmented Artinian test `A` over `R` with residue field `K`,
  every map `a : Spec A → U` restricting to `p ≫ i` factors as
  `b ≫ i = a`, where `b : Spec A → V` restricts to the original `p`;
- formal versality of `M` at `p`.

It concludes formal versality of `L` at `p ≫ i`, using the published
`PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt`. This predicate
retains the actual maps and complete specified line-bundle isomorphisms
in every lifting problem.

The Artinian factorization hypothesis is an explicit condition to prove
in an application. Its lift need not be unique. There is no monomorphism,
finite-type, properness, flatness, Noetherianity, or completeness
assumption in this categorical statement. All rings and schemes retain
the arbitrary universe `u`.

## Provenance and role

This is an internal categorical consequence of the published actual
point-fibre and versality definitions, rather than an additional
approximation or algebraization theorem. The relevant source motivation
is Stacks Project, `artin.pdf`, version ed88ff78, Lemma 98.12.3
(Tag 0CXK), statement on printed p. 18 and proof on p. 19, in registered
source `stacks-artin-axioms-approximation-2026-11-06`. Its proof identifies
maps from a completed local ring to an Artinian test with pointed maps
from that test into the original scheme, then compares lifting
conditions. The present statement isolates only the sufficient
factorization direction of that categorical comparison.

The Library already supplies the actual point maps and their coherence
in `PseudofunctorPointFiberAtlasRestriction` and
`PseudofunctorPointFiberObjectIso`; the proof should reuse these.
An application to a completed local chart must separately construct its
chart map, prove the pointed Artinian factorization condition, and
provide the actual pullback-family isomorphism. This statement asserts
none of those constructions, nor the approximation, associated graded,
or complete-local-ring isomorphism steps of Stacks Lemma 98.12.7.
