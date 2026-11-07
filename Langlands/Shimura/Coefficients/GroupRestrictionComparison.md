# Identity comparisons for successive group restriction

Let `I` be any category, let `D`, `E`, and `F` be diagrams of groups on
`I`, and let `C` be any category. Suppose that natural group maps
`φ : D ⟶ E`, `ψ : E ⟶ F`, and `χ : D ⟶ F` satisfy
`(ψ.app i).hom.comp (φ.app i).hom = (χ.app i).hom` at every index.

`Langlands.EquivariantDiagram.groupRestrictionCompIso` constructs the
isomorphism from restriction first along `ψ` and then along `φ` to
restriction along `χ`, for every equivariant diagram over `F`.
Both underlying natural transformations are the identity on the entire
original `I`-diagram. Thus objects, original transition maps, and index
arrows are retained.

The equivariance proofs evaluate the given equality of group homomorphisms
on each group element and apply the original coefficient action. The inverse
uses the symmetric equality. The isomorphism laws reduce to the identity
laws in the functor category. The two projection lemmas state the identity
formulas explicitly.

`groupRestrictionCompIso_naturality` proves that these identity comparisons
commute with every equivariant coefficient morphism over `F`. Its proof
forgets the actions using `Hom.ext` and applies the two category identity
laws. It does not require the coefficient morphism to be invertible.

This is an internal categorical construction derived from the existing
`EquivariantDiagram.groupRestriction`. There is no new assertion from the
literature. The group homomorphism equality is a precise input; this module
does not construct any arithmetic quotient maps or assert equality of
unrelated coefficient systems. The universes of groups, the indexing category,
and the coefficient category are independent.
