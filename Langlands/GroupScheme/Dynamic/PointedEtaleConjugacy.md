# Étale conjugacy of dynamic parabolics from a prescribed fibre transporter

Worker 598.

This internal module derives étale conjugacy for two subgroup images that
already have global dynamic cocharacter presentations over an affine base.
It does not assume that the presenting homomorphisms are monomorphisms, nor
that the ambient smooth affine group is reductive.

`PointwiseSchemeAction.IsTransporter.comp_innerIso_eq` identifies the
all-test transporter relation at a base section with equality under its inner
automorphism. The transporter convention is `ψ(h)g = gχ(h)`, so the resulting
equality is `χ ≫ innerIso(g) = ψ`.

`PointwiseSchemeAction.exists_pointed_etale_hom_conjugacy` transfers the
published pointed diagonalizable transporter lift through an actual source
isomorphism. It constructs a pointed étale neighbourhood and a conjugator
between the actual base-changed homomorphisms. Its recovery equation says that
the specified residue-field conjugator is recovered as a morphism into the
original ambient group.

`Dynamic.range_comp_innerIso_eq_of_presentations` turns an equality of
conjugated cocharacters into equality of the conjugated subgroup images.
It uses the published isomorphism functoriality of dynamic parabolics and
constructs the two pointwise range implications, using the inverse inner
automorphism for the reverse implication.

`Dynamic.exists_etale_conjugacy_of_presentations` applies these facts to
cocharacters by identifying `G_m` with a diagonalizable group. The input
consists of two actual dynamic presentations and a prescribed transporter
between the raw base changes of the cocharacters over the residue field.
Dynamic parabolics and represented subgroup ranges commute with base change,
so the lifted homomorphism conjugacy gives conjugacy of the actual subgroup
images. The residue-valued point of the neighbourhood shows that its image
contains the chosen base point.

`Dynamic.EtaleSubgroupConjugacyData` records an étale neighbourhood with a
point over the specified base point, an actual section of the ambient group,
and the equality of conjugated subgroup images.
`Dynamic.etaleConjugacyOfPresentations` chooses these data from the preceding
existence theorem. The data constructor is the module's primary construction.

The provenance is internal: every assertion follows from existing transporter,
base-change, and dynamic functoriality theorems. This module does not assert
that arbitrary relative parabolics admit suitably compatible presentations.
