# Group compatibility of the canonical dual base-change comparison

`DualAbelianBaseChangeStatement` is the precise obligation that the already
constructed canonical comparison of dual schemes preserves their constructed
group structures. For a morphism `b : S' → S` and an abelian scheme `A/S`,
its conclusion is an isomorphism of abelian schemes

`(A^dual)_{S'} ≅ (A_{S'})^dual`.

The source is the actual base change of `dualAbelianSchemeFromEvaluation A`.
The target is the same dual construction applied to the actual base change
of `A`. The underlying forward morphism in `Over S'` is required to equal
`dualSchemeBaseChangeIso universality b A hA hA'`. This is the canonical
scheme isomorphism characterized by pullback of the chosen new Poincare
family to the explicit base change of the old Poincare family. Thus the
conclusion prescribes the map on the full schemes and all test schemes,
including nonreduced ones.

All inputs are quantified explicitly. They include actual universal-family
existence for both duals, smoothness, properness and geometric connectedness
of those very parameter schemes, ordinary inverse line bundles of the two
Poincare bundles, and their tensor evaluation isomorphisms. The seven named
tensor-preservation, pullback-coherence and Picard-zero-stability propositions
are the inputs used to construct both group laws. The base-change universality
proposition is the input used to construct the canonical scheme comparison.
There is no hypothesis that this comparison is a homomorphism. Neither an
abelian-scheme comparison nor an unrelated identification of targets is
supplied as data.

The two bases are arbitrary schemes in the same universe. No noetherian,
quasi-separated, projective or field hypothesis is imposed here: the
geometric properties and universal families are already explicit premises.
The conclusion applies to every pair of the stated inverse/evaluation
choices. It does not identify the chosen duals by definitional equality.

## Internal provenance and remaining proof

This is an internal compatibility statement between the Library's existing
constructions. `DualSchemeBaseChange` constructs the unique compatible scheme
isomorphism from the actual universal-family property.
`DualGroupScheme` constructs the group law by classifying tensor products,
and `DualAbelianScheme` equips that group scheme with the supplied geometry.
The expected argument transports tensor products and trivial families
through the actual pullback functors, then uses unique classification to
show that the canonical comparison preserves multiplication and the unit.
The inverse scheme map should then give the inverse group homomorphism.
These comparisons are proof obligations, not results of this file.

The declaration is a `Prop`-valued statement. It proves neither the group
compatibility nor unconditional dual existence, geometry, base-change
universality, or coherence under successive base changes. A separate proof
task must establish its exact type. Its purpose is to expose the missing
compatibility explicitly when transporting a homomorphism to a dual on
geometric fibres.
