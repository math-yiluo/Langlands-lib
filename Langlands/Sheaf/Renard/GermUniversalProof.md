# Actual germ universal property proof

Worker 1215, with Worker 6's source audit and local-representative proof design.

This proof targets the published closed `GermUniversalStatement.{u,v}`. It uses
the actual germ functors, canonical units, corrected descent, and universe lifts.
The original source is Renard 2026, II.2.1, printed pp.35–37 / PDF pp.41–43,
registered as `renard-2026-representations-groupes-reductifs-padiques`.
These three original pages were read directly for this proof.

The extensionality lemma compares two sheaf morphisms on any germ section by
choosing a contained local original-section representative at each point.
Naturality identifies restrictions of both images with images of that original
section's canonical germ family. Their equality there gives equal target germs;
the published equality detection for a genuine target sheaf yields equality of
its sections. The source presheaf remains arbitrary. Empty domains are included
by the same target equality detection. No intersection is required to be a basis
open.

Direct and lifted uniqueness follow by evaluating equality of unit composites
on an original section (or its actual ULift). The direct Hom equivalence uses
unit precomposition and literal `germDesc`; its inverse laws are uniqueness and
the published factorization law. The lifted equivalence lowers only the
unit-precomposed morphism between actual lifted presheaves. Its inverse laws use
lifted uniqueness, factorization, and the two published lift/lower inverse laws.
Both forward naturality laws follow by applying the inverse equivalence and the
published descent precomposition and postcomposition identities.

The direct adjunction is constructed by Mathlib's `Adjunction.mkOfHomEquiv`
from this proved equivalence, its inverse source naturality and its forward
target naturality. The constructor establishes both actual triangle identities
from the inverse laws and naturality. The proof identifies its entire unit with
the actual `germSheafUnit`, its Hom equivalence with the explicit direct family,
and its counit with literal descent of the identity.

The printed source equality of arbitrary source representatives in (II.2.1.3)
is invalid. The imported corrected descent glues their images using separation
only in the actual target sheaf, on every smaller basis open in an overlap.
This proof likewise separates only target sections. It retains independent space
and original-value universes, every supplied topology and chosen basis, arbitrary
normalized source presheaves and all empty cases. The direct adjunction is at
value universe max u v; the arbitrary original-v family uses the actual lifts.

Unit invertibility on sheaves, basis/all-open equivalence, compact sections and
scalar-module extensions remain separate obligations.
