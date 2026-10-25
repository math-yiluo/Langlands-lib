# Group compatibility of the canonical dual base-change comparison

`Langlands.AbelianScheme.dualAbelianBaseChange` proves the exact published
`Langlands.AbelianScheme.DualAbelianBaseChangeStatement`. For arbitrary schemes
`S`, `S'`, a morphism `b : S' → S`, and an abelian scheme `A/S`, the actual base
change of the constructed dual abelian scheme is isomorphic to the constructed
dual of the actual base change of `A`. The forward morphism in `Over S'` is
exactly the prescribed `dualSchemeBaseChangeIso universality b A hA hA'`.

The theorem retains all premises of the statement: the seven named tensor,
coherence, and Picard-zero-pullback propositions; Picard-zero base-change
universality; existence and geometry of both universal parameter schemes; and
each choice of inverse line bundle and tensor evaluation isomorphism. The proof
works for every test scheme in `Over S'`, including nonreduced schemes. It proves
compatibility of these existing group laws and does not establish unconditional
dual existence, geometry, the supplied coherence propositions, or base-change
universality.

## Implemented proof

The proof reuses the published family naturality comparison and then implements
the following argument through private helpers.

1. The published [family base-change naturality](FamilyBaseChangeNaturality.md)
   module supplies `familyBaseChangeSpaceMap_naturality` and
   `familyBaseChangeNaturality`. The proof uses the inverse of the latter
   natural isomorphism to compare the two orders of pullback on classes.

2. `familyClassesBaseChange` sends a rigidified line-bundle class to its pullback
   class along the actual base-change map. Functoriality makes this well-defined
   on isomorphism classes. The preceding natural isomorphism gives its
   compatibility with parameter pullback. The rigidified
   `pullbackTensorIso`, with the stated preservation, composition, and left-unit
   coherence premises, proves that this class map preserves tensor products.

3. `baseChangeFamily_classifyingMap` identifies classification by a base-changed
   family with base change of the old classified class. Applying this to the
   Poincare family and using `dualSchemeBaseChangePullbackIso` yields
   `dualBaseChange_point_class`: composition with the prescribed comparison
   induces precisely this base-change map on rigidified classes.

4. For each test scheme `T`, the old point classification is composed with
   `GroupScheme.baseChangePointsEquiv` and the inclusion of Picard-zero classes
   into rigidified classes. This is a monoid homomorphism `F`. The new dual's
   classification followed by the corresponding inclusion gives an injective
   monoid homomorphism `G`. The preceding identity says
   `G (p ≫ e.hom) = familyClassesBaseChange b A T (F p)`, where `e` is the
   prescribed scheme isomorphism. Tensor preservation and injectivity of `G`
   show that composition with `e.hom` preserves multiplication.

5. `isoOfPointMultiplication` upgrades an underlying scheme isomorphism with
   this multiplication property to an abelian-scheme isomorphism. Composition
   with the scheme isomorphism and its inverse gives a multiplicative
   equivalence on each point group. Its preservation of one, evaluated on the
   terminal test object, gives the unit equation. Multiplication preservation
   on the product test object, evaluated at its two projections, gives the
   group-object multiplication equation. `Grp.mkIso` supplies the group-object
   isomorphism, which is then viewed as an abelian-scheme isomorphism.

The final theorem uses this upgrade on `dualSchemeBaseChangeIso`. The required
equality of its forward underlying map is proved by reflexivity, so no replacement
scheme map or transported group law is introduced.

## Internal provenance

This is a derived compatibility proof between the Library constructions imported
by `DualAbelianBaseChangeStatement` and `FamilyBaseChangeNaturality`.
`FamilyBaseChange` and `PoincareBaseChange`
provide the actual family maps; `DualSchemeBaseChange` provides the canonical
scheme comparison and its Poincare pullback isomorphism. `DualGroupScheme`,
`DualAbelianScheme`, and `KernelBaseChange` provide the multiplicative point
classifications and base-change point equivalence. The proof uses Mathlib's
cartesian monoidal group-object infrastructure to lift the resulting equations.
It makes no separate claim to an external source theorem.
