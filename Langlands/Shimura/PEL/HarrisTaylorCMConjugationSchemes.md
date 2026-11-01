# Conjugate small levels and normalized CM scheme isomorphisms

This module constructs conjugation isomorphisms for the existing normalized CM
scheme tower. It retains the actual central simple unitary datum, CM-compatible
signature charts, original opposite finite-adelic similitude group and every
named prerequisite of `HarrisTaylorCMSchemeLevels`. The scheme construction
requires exact representation of the already constructed moduli presheaves.

## Compact-open conjugation

For any topological group `G`, `CompactOpenLevel.conjugate U g` is the actual
compact-open subgroup `g⁻¹ U g`. Its underlying subgroup is the inverse image of
`U` under `x ↦ g x g⁻¹`. Openness follows from continuity of this group
automorphism. Compactness follows by taking the inverse image of the compact
set `U` under the homeomorphism obtained from left multiplication by `g`
and right multiplication by `g⁻¹`. The theorem `mem_conjugate` states exactly
this membership condition.

`conjugationIso U g` is an isomorphism in the existing transporter category.
Its forward arrow has element `g`, and its inverse has element `g⁻¹`.
The arrow condition for a map from `U` to `V` is `g⁻¹ U g ≤ V`.
Thus the two membership proofs and inverse laws follow from the group laws.
The element formulas are definitional equalities. Given a subgroup inclusion
`U ≤ V`, `conjugateInclusion` gives the inclusion between their conjugates.
The theorem `conjugationIso_naturality` proves the forgetting square by
extensionality of transporter arrows and the equations `g * 1 = g = 1 * g`.

## The same smallness place

For the original opposite finite-adelic group attached to an algebra with
involution, `LevelSmallAt.conjugate` proves that the same finite place witnesses
smallness of the conjugate level. If `x ∈ g⁻¹ U g`, put
`a = pointsMap (finiteEvaluation v) (unop g)` and let `b` be the corresponding
projection of `unop x`. Reversal of multiplication by `unop` identifies the
projection of `g x g⁻¹` with `a⁻¹ b a`. Its finite order follows from finite
order of `b` by the group homomorphism for conjugation by `a⁻¹`. Smallness of
`U` makes `a⁻¹ b a` equal to `1`; conjugating this equality back gives `b = 1`.
This proves local smallness without selecting another finite place.
`LevelSufficientlySmall.conjugate` retains the original existential witness.

`smallCMConjugateLevel` applies this construction to `SmallCMLevel D` in
`D.rationalInvolution.FiniteAdelicPoints` with opposite multiplication.
The finite-dimensional rational algebra instance needed for the topology is
derived from `D.finite` and `Module.Finite.trans F A`. No additional arithmetic
finiteness assumption is introduced. The definitions
`smallCMConjugationIso` and `smallCMConjugateInclusion` lift the actual
transporters to the existing full subcategory of sufficiently small levels.
Their element formulas and forgetting square are proved by the generic
constructions. This does not prove existence or cofinality of small levels.

## Represented bases and schemes

Let `R U` be an exact `CMLevelRepresentation` for every small level `U`.
This is the representation type already used in `HarrisTaylorCMSchemeLevels`:
it includes an actual componentwise admissible scheme over `Spec F`, the
specified smoothness and projective immersion, and a natural isomorphism from
its lifted Yoneda presheaf to the fixed CM moduli presheaf.
The representing bases themselves belong to that test category.

`representedCMBaseConjugationIso` and
`representedCMSchemeConjugationIso` apply the existing base and scheme tower
functors to the small-level isomorphism. Hence the forward and inverse maps
are actual morphisms of the represented bases and Mathlib schemes, with both
inverse identities supplied by `Functor.mapIso`. Neither scheme map nor an
isomorphism of arbitrary schemes is supplied as a new input.

The `_hom_over` and `_inv_over` theorems prove that both scheme morphisms
commute with their actual structure morphisms to `Spec F`. The two `_classes`
theorems quantify over every test in the exact
`ComponentwiseAdmissibleCMBaseCategory` and every morphism from that test to
the corresponding representing base. Under the representing natural
isomorphisms, postcomposition by the forward map is the already constructed
class transition at `g`; postcomposition by the inverse is the transition at
`g⁻¹`. These are instances of `representedCMBaseTower_map_classes`.
The underlying scheme maps are precisely the forward and inverse maps above.
The formulas preserve the existing geometric-family and componentwise moduli
interpretation and assert no representation on arbitrary `F`-schemes.

`representedCMSchemeConjugationIso_naturality` proves the forgetting square
by mapping the established small-level square through the scheme tower and
using `Functor.map_comp`. For another family `R'` representing the same exact
presheaves, the `_hom_comparison` and `_inv_comparison` theorems use naturality
of the same canonical `representedCMSchemeTowerComparison R R'`.
Both comparison squares therefore arise from identity of the fixed moduli
presheaves. The existing tower supplies the comparison identity and cocycle
laws.

Finally, `cmSchemeConjugationIso` takes a proof of exactly the existing
`CMRepresentabilityStatement`, chooses its witnesses by
`chosenCMLevelRepresentation`, and gives an isomorphism between the objects
of the existing `cmSchemeTower` at `U` and `g⁻¹ U g`.

## Source and remaining scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed p.90 (one-based PDF p.98), specifies the
local finite-order smallness condition. Printed p.91 (PDF p.99) gives the
map from level `V` to level `U` under `g⁻¹ V g ⊆ U`, acting on the frame
by composition with `g`. Taking equality of these levels motivates the
conjugation isomorphisms here. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This is a derived construction by Worker 57. Its implemented proof uses
topological conjugation, the same-place smallness argument, genuine transporter
inverse laws, and the existing exact represented Yoneda tower and canonical
comparisons. It does not prove the source's representability or cover
assertions. Source division/global applicability, comparison with the original
moduli problem, representer admissibility, geometric existence, finite
etaleness, Galois covers, canonical models, complex uniformization and
coefficient descent remain separate obligations. In particular, the transporter
category retains elements: this module proves no target-level triviality and
no quotient-group action on the schemes.

The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
