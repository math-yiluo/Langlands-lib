# Smooth compactly supported sections

Author: Worker 13. This module reuses Worker 0's published smooth-vector
constructions without modifying or duplicating the general smooth
representation category.

For a topological group acting on a space by continuous individual operators,
`SmoothCompactSections.representation` takes the existing smooth part of the
actual compact-section representation. Its elements are compactly supported
sections fixed by some open subgroup. The proof `isSmooth` retains the fixing
subgroup of each vector and proves the equation in the subtype. It does not
assume that every compactly supported section is smooth.

`exists_preimage_iff` identifies its image in global sections exactly: a
section lies in the image if and only if its support is compact and it is a
smooth vector for the global action. Both implications use the actual
subtype inclusions and fixing equations.

Equivariant sheaf morphisms induce maps by the existing `smoothMap`.
`functor` constructs the resulting functor to Mathlib's `Rep R G`;
each of its objects has the proved smoothness property. `inclusion` and
`globalInclusion` are natural equivariant inclusions into compact and global
sections. Their naturality and the functor laws reduce to the underlying maps.
`smoothFunctor` lifts the same functor to the published full subcategory
`Langlands.SmoothRep R G` using the proved smoothness of each object.
`smoothFunctorToRepIso` identifies its composite with the inclusion in `Rep`
with the original functor. This identification is definitionally the identity,
so the representation carriers, operators and intertwiners are unchanged.

An equivariant map from any representation to global sections whose values
have compact support has an actual `compactLift`. If its source is smooth,
`lift` restricts further to smooth compact sections. `lift_apply` proves that
the global-section values are unchanged. `hom_ext` proves uniqueness from
those values, using two subtype inclusions. The source module of these maps
may have an independent universe.

The ring, space and section-module universe is `u`; the group universe is
`uG` and the auxiliary source-module universe is `uW`. The assumptions are
`CommRing R`, `IsTopologicalGroup G`, a group action on `X`, and
`ContinuousConstSMul G X`. The representation modules have no topology.

## Source and specialization boundary

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995–1996 manuscript, section 1.5, printed p.11, defines support by nonzero
germs and forms the union over open subgroups of compact invariant sections.
The preceding section 1.4, printed p.7, describes the transport action.
Worker 13 read these original passages. The present construction is an
ordinary-topological counterpart: its elements are precisely compact
sections fixed by an open subgroup. It does not identify this construction
with Berkovich's analytic etale sheaf category or assert a categorical
colimit comparison.

The existing `Langlands.smoothPart`, `smoothMap`, `smoothInclusion` and
`smoothLift` are reused from
`Langlands.Representation.Smooth.SmoothPart.Definitions`, verified in the
current Library. Their intrinsic construction fields supply the conjugation
argument and preservation of smooth vectors under intertwiners. This module
specializes them to the previously constructed compact-section action.
The smooth representation category and its inclusion are imported from
`Langlands.Representation.Category.Basic`; the lift uses Mathlib's
`ObjectProperty.lift`. Both imported project interfaces are present in Library
commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`.

Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The ordinary compact-support and moving-space equivariance prerequisites are
published in Library commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`.
The analytic site, smooth equivariant etale category, derived equivariant
cohomology, and Harris specialization remain separate obligations.
