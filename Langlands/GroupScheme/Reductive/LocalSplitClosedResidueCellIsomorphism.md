# Big-cell gluing from local algebras with closed residue fields

This internal derived criterion strengthens the local-algebra gluing reduction
by restricting its tests to local coefficient algebras with separably closed
residue fields. The base ring is arbitrary and may have nilpotents.

`LocalSplitClosedResidueCellIsomorphismStatement.{u}` concerns two reductive
group schemes over `Spec R`, with common coordinate split torus, supplied
additive-group families, finite root enumerations and open cell maps. For every
commutative local `R`-algebra `A : Type u` with separably closed residue field,
assume a homomorphism between their actual `A`-point groups,
matching all torus points and each supplied additive-group parametrization.
Then the group schemes are isomorphic, with exact agreement on the common
cell. No inverse or naturality of the homomorphisms is required. The module proves this
proposition at full universe.

`CellGluing.hom_ext_of_injective_specMap` proves that an injective ring map
`A → B` detects equality of maps `Spec A → Y` to an affine target. Composing
with `Y → Spec Γ(Y)` represents the maps by ring homomorphisms. Faithfulness of
`Spec` and injectivity of `A → B` cancel the extension.

For each local ring `A`, the imported closed-residue extension construction gives
a faithfully flat local algebra `B` in the same universe with algebraically
closed residue field. Its algebra map is injective, so equality after extending
`Spec A` to `Spec B` gives equality over `Spec A`. The existing stalk test
criterion now detects equality into any affine scheme using only the restricted
local rings. This does not pass to residue fields or discard nilpotents.

Apply this equality criterion to the multiplication relations defining cell
compatibility. First, the imported local-point homomorphism theorem makes each
matching homomorphism bijective: its kernel is trivial by the target cell's
monomorphism and it is surjective by inverse-first two-cell factorization.
It thus defines a multiplicative equivalence. For each permitted local ring,
this comparison transfers the relation in one direction; its inverse transfers
it in the other.
Reductivity supplies affineness, smoothness and geometrically irreducible fibres.
The published open-cell gluing theorem then supplies the isomorphism with exact
cell agreement. Finally, every structure map `Spec A → Spec R` defines an
`R`-algebra structure on the same local ring, and identity transport gives the
canonical algebra-test formulation.

The provenance is the explicit injective extension argument above, combined
with the local-ring stalk test, cell-relation transport, automatic point-homomorphism
bijectivity and existing open-cell gluing theorem. Existence of actual torus/root
matching homomorphisms remains a hypothesis.
This criterion does not construct them or prove the unrestricted local split
Isomorphism Theorem.
