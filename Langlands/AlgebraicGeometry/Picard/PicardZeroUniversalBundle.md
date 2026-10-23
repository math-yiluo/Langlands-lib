# Universal geometric Picard-zero bundles

This module defines a universal-property predicate for a specified rigidified
line bundle on an abelian scheme, restricted to the geometric-fibre
Picard-zero condition. It derives a representation of the previously
constructed set-valued presheaf from that predicate. No existence of such a
bundle or representing scheme is assumed as a theorem.

## The universal property

Fix `A : AbelianScheme S`, an `S`-scheme `P : Over S`, and an actual
rigidified relative line bundle `L : RigidifiedFamily A P`. The proposition
`IsUniversalPicardZero A L` is the conjunction of two requirements:

1. `L` satisfies `IsPicardZeroFamily A L`.
2. For every test `S`-scheme `T` and every `q : PicardZeroClasses A T`,
   there exists a unique `h : T ⟶ P` whose actual pullback class of `L`
   equals `q.val`.

The classification map in the second requirement is the existing
`RigidifiedLineBundle.classifyingMap`, constructed from the actual relative
pullback functor. No arbitrary equivalence or natural transformation is
supplied as data. The predicate needs no preservation or coherence
hypothesis: all classes and maps occurring in it are already defined.

`isUniversalPicardZero_iff` expresses the second requirement on actual
families `M` satisfying `IsPicardZeroFamily`: there is a unique parameter map
whose pulled-back rigidified bundle is isomorphic to `M`. In the forward
direction it applies the class property to the class of `M`; in the reverse
direction quotient induction chooses a representative. In both directions,
`RigidifiedLineBundle.classifyingMap_eq_iff` converts equality of classes
to existence of a rigidified isomorphism. Uniqueness concerns the parameter
map, not the isomorphism witnessing equality of bundle classes.

## Actual classification and representation

The following constructions take the explicit parameter
`stability : PicardZeroPullbackStatement`. Given `L` and a proof `hL` that
it satisfies the geometric-fibre condition, `picardZeroClassifyingMap`
restricts actual pullback of its class to the Picard-zero subtype.
`picardZeroClassifyingMap_val` identifies its underlying class with the
existing ambient classification map by reflexivity.

`picardZeroClassifyingMap_bijective` derives bijectivity when `L` is
universal. The universal property supplies a unique preimage of each subtype
element; subtype extensionality converts the class equality to equality
in the subtype, and applying `Subtype.val` gives the converse implication
needed for uniqueness. `picardZeroClassifyingEquiv` uses
`Equiv.ofBijective` on this map. Thus its forward function is actual bundle
pullback, and its inverse is derived from the universal property.

With the additional explicit parameter
`coherence : RigidifiedModule.PullbackCoherenceStatement`, the lemmas
`picardZeroClassifyingMap_comp` and `picardZeroClassifyingMap_id` follow
from the corresponding ambient classification lemmas by subtype
extensionality. The coherence parameter is retained in their types.
`picardZeroRepresentableBy` packages the derived classification equivalences
and composition law into Mathlib's `RepresentableBy` for
`picardZeroPresheaf stability A coherence`.

`picardZeroComparisonIso` applies Mathlib's `RepresentableBy.uniqueUpToIso`
to two such representations. It constructs an isomorphism of the parameter
schemes in `Over S`. This definition alone does not assert a unique
isomorphism satisfying a specified bundle compatibility condition; that
stronger formulation is a separate statement and proof obligation.

## Provenance and boundaries

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §1, paragraph (6.2), printed p.88 (PDF p.92), states the universal
property of the Poincaré bundle in terms of the unique parameter morphism
and actual rigidified pullback. The point formula for `φ_L`, printed p.95
(PDF p.99), and Corollary (7.22), printed p.106 (PDF p.110), motivate the
geometric-fibre criterion used in parent-task item 3.

This module is a derived restriction of that universal-property construction
to the already defined Picard-zero classes, together with formal consequences
of the property. It does not claim to generalize a representability theorem
from those passages. The base scheme is arbitrary; the conclusion is
conditional on an actual universal family and the two stated compatibility
proofs. It supplies no tensor group law, sheaf comparison, identity-component
comparison, representability existence, or abelian-scheme structure on `P`.
