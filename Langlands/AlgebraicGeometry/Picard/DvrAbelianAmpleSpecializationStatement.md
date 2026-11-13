# Specialization of a specified ample line bundle over a DVR

Author: Worker 537.

`Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationStatement.{u}`
is the generic-to-closed specialization assertion for an actual abelian
scheme over the spectrum of a discrete valuation domain `R` in an arbitrary
universe `u`. For a specified line bundle `L` on the total scheme, it asserts
that ampleness of its residue-field fibre at the zero prime implies
ampleness of its residue-field fibre at the closed point.

The generic point is the prime `⊥`, using the supplied domain instance.
The closed point is `IsLocalRing.closedPoint R`, using the local-ring
instance furnished by the discrete valuation ring. Both pullbacks use the
scheme-theoretic fibre inclusions `A.X.hom.fiberι`. No choice of fraction
field or algebraic closure is part of the statement.

There is no restriction on the relative dimension, residue characteristic,
symmetry of the bundle, polarization, or existence of a dual scheme. The
statement concerns the same supplied total line bundle on both fibres.
It does not construct a bundle or a representing object. This module
defines the proposition and supplies no proof of specialization.

## Source and derivation

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
Chapter I, Remark 1.10(b), printed p.7 (PDF p.19), states that the
ample-fibre locus of an invertible sheaf on an abelian algebraic space is
closed. The registered source is
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
content SHA-256
`f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`.
Worker 537 read printed pp.6–7 and inspected both rendered pages.
No source-specific errata note was found in the current Library.

The present target is an internal derived specialization of that assertion:
take the base to be `Spec R`, restrict to scheme-valued abelian schemes,
and apply closedness to the specialization from the zero prime to the
maximal ideal. The source's preceding argument on printed p.6 uses
nondegeneracy of the bundle, Riemann–Roch, and semicontinuity; this
statement does not claim those ingredients are already formalized.

## Role in the general closedness proof

For a locally noetherian scheme, every strict specialization is realized
by an actual DVR-valued point, as proved in
`Langlands.AlgebraicGeometry.nonempty_dvrSpecialization`. Preservation and
reflection of ampleness under field base change then transport the two
fibre conditions through that point. Thus a proof of this target supplies
the geometric specialization input for
`AbelianFibreAmpleLocusClosedStatement`. Openness from
`properFibreAmpleSpreading` supplies the remaining local constructibility
needed for the topological closedness argument.

This prerequisite carries no authority to resume or duplicate separately
allocated dual-scheme or Picard representability constructions. A proof
using such a construction must await its authorized accepted publication.
