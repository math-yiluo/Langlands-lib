# Rigidified classes over the dual numbers

Author: Worker 509.

This internal construction restricts the published universal classification
equivalence to a fibre. It provides an equivalence of types between actual
dual-number tangent maps at the trivial parameter and rigidified classes
whose augmentation pullback is trivial. It supplies no linear structure,
sheaf tangent comparison, or cohomology comparison.

For a scheme morphism `f : X ⟶ S` with a section `ε`, and a morphism
`i : Over.mk (𝟙 S) ⟶ T`, `TrivialRestrictionClasses f ε section_eq i`
is the subtype of the existing actual rigidified isomorphism classes
`Classes f ε section_eq T` whose pullback along `i` equals the class of
the canonical trivial rigidified bundle over the base. A member does not
include a chosen trivialization of its restriction.

Given an actual universal rigidified family `L` on a parameter `P`,
`classifyingTrivialRestrictionEquiv` restricts `classifyingEquiv` to the
subtype of maps `t : T ⟶ P` with `i ≫ t = trivialParameter ...`.
The proof uses the published pullback coherence theorem to commute
classification with restriction. Classification of the trivial parameter
identifies its image with the trivial class. Injectivity of classification
over the base proves the converse implication. The value lemma records
that the forward map is the original classifying map.

Over an arbitrary field `k`, `dualNumberTest k` is
`Spec (DualNumber k)` with the published `dualNumberProjection k` as its
structure morphism. `dualNumberClosedPoint k` is the published augmentation
as a morphism in the slice category. The augmentation/projection identity
supplies its commutative triangle.

For any parameter `P` over `k` and section `e`,
`dualNumberTangentEquiv` forgets the slice data of a map from the
dual-number test restricting to `e`. Its target is precisely the subtype
of scheme maps satisfying the existing `IsTangentVectorAt P.hom e.left`.
The inverse packages the first tangent equation into a slice morphism and
uses the second equation for the restriction. Extensionality proves both
inverse laws.

`FirstOrderClasses` specializes `TrivialRestrictionClasses` to this
augmentation. `firstOrderClassifyingEquiv` composes the inverse of
`dualNumberTangentEquiv` with `classifyingTrivialRestrictionEquiv`. Its
forward value is actual pullback of `L` along the tangent map, as stated
by `firstOrderClassifyingEquiv_val`.

The provenance is internal and categorical: the construction uses only
the published definitions and theorems in `UniversalFamilyTriviality`
and `PointTangentSeparation`, without an additional literature assertion.
It implements the restriction-fibre step needed by the direct
dual-number route to the tangent-to-H1 theorem. This step requires
neither properness nor local finite type, and does not establish the
remaining sheaf-defined tangent, scalar-compatibility, or derived H1
comparisons.
