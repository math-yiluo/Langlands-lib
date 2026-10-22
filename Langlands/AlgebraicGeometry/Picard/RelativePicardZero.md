# Geometric Picard-zero classes in the rigidified relative family

For an abelian scheme `A/S`, this module constructs the subset of isomorphism
classes of rigidified relative line bundles satisfying the geometric-fibre
Picard-zero condition. The base `S` is arbitrary, with schemes in universe
`u`. No presheaf or group structure on this subset is claimed here.

## The unit section and the fibre-product convention

`AbelianScheme.unitSection A` is the underlying scheme morphism of the
identity element of `Over.mk (𝟙 S) ⟶ A.X`. This is the actual identity point
in the group-valued functor of points. `unitSection_comp` is its slice-morphism
equation: composing with the structure morphism of `A` gives the identity of
`S`.

`RigidifiedFamily A T` and `RigidifiedClasses A T` specialize the existing
relative rigidified line-bundle category and its quotient by rigidified
isomorphism to this section. They add no new quotient relation or arbitrary
bundle data. The relative category uses the total space `T ×_S A` and the
induced section `(id_T, unitSection A ∘ T.hom)`.

The existing abelian-scheme base change has total space `A ×_S T`.
`familyLineBundle A L` first forgets the rigidification and then pulls the
underlying line bundle back along the inverse of
`relativeSpaceSymmetry A.X.hom T : T ×_S A ≅ A ×_S T`. This direction is
`A ×_S T → T ×_S A`, so its pullback has exactly the total space of
`(AbelianScheme.baseChange T.hom).obj A`. It is an actual line bundle, not an
identification of types asserted without a scheme map.

## Predicates and the subset of classes

`IsPicardZeroFamily A L` applies `IsGeometricallyPicardZero` to this underlying
bundle on `A_T`. Explicitly, for every algebraically closed field `K : Type u`
and every morphism `Spec K → T.left`, the restriction to the resulting
geometric fibre of `A_T` is invariant under translation by all its `K`-points.
The condition does not depend on the rigidification, but the surrounding
category and its isomorphisms retain that rigidification.

`isPicardZeroFamily_iff_of_iso` first maps a rigidified isomorphism through
the forgetful functor and the pullback along the inverse symmetry. It then
applies isomorphism invariance of the geometric-fibre condition.
`IsPicardZeroClass` descends this predicate to `RigidifiedClasses` by
`Quotient.lift`. Propositional extensionality converts the preceding
if-and-only-if into the equality of propositions required for the descent.
`isPicardZeroClass_classOf` is the resulting definitional equivalence on any
representative, proved by `Iff.rfl`.

`PicardZeroClasses A T` is the subtype of rigidified classes satisfying this
predicate. `isPicardZeroFamily_trivial` uses the canonical isomorphism from
the pullback of the structure line bundle to the structure line bundle, and
transports the known geometric-fibre condition along its inverse.
`trivialPicardZeroClass` packages the canonically rigidified structure line
bundle and this proof into an element of that subtype.

## Provenance and remaining obligations

This is derived infrastructure combining the relative rigidified classes of
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter VI §1,
paragraph (6.2), printed p.88 (PDF p.92), with the geometric-fibre criterion
chosen by item 3 of the parent task. The latter is motivated by the point
formula for `φ_L` on printed p.95 (PDF p.99) and the identity-component/kernel
criterion in Corollary (7.22), printed p.106 (PDF p.110). The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The source's relative functor uses `A ×_S T`; the explicit symmetry above
accounts for our existing relative category's reversed factors. Its additional
hypotheses for triviality of rigidified automorphisms and comparison with the
Picard sheaf are not needed to form these categories and subsets. Neither
comparison is asserted. The field identity-component criterion motivates the
chosen predicate; it is not proved or used as an imported formal theorem.

Preservation of this condition under relative pullback remains a separate
statement and proof obligation. In particular, this module does not yet turn
the subsets into a subfunctor, supply a tensor-product group law, or establish
representability or a dual abelian scheme. The quotient construction itself
requires no proof of the separate rigidified pullback coherence proposition.
