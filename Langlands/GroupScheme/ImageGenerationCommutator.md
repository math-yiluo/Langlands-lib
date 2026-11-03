# Actual commutator source and equivariance

This internal construction provides the actual commutator source for the
general geometric prerequisite of Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), Lemma 3.3.4 and the paragraph preceding
Proposition 3.3.5, printed pp.108–109 (PDF pp.134–135), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. It makes no assertion about
weights, semigroups or geometric integrality.

`PointwiseSchemeAction.prod` is the diagonal action on the actual binary product of
two arbitrary source schemes. Its action morphism is the product lift of the
two coordinate actions. Evaluation, projection, unit and associativity laws
follow from the product lifting identities and the component action laws.

For actual homomorphisms `j₁ : H₁ ⟶ G` and `j₂ : H₂ ⟶ G`, `commutatorMap`
is the morphism from `H₁.X ⊗ H₂.X` into `G.X` obtained by composing the
coordinate homomorphisms with the categorical group commutator. It evaluates
on every test scheme as `j₁(x) * j₂(y) * j₁(x)⁻¹ * j₂(y)⁻¹`. The implemented
proof uses the published categorical commutator evaluation law and
precomposition with product lifts.

The commutator morphism is the identity on both slices with an identity
coordinate. In particular, the pair of identity points supplies a base
rational point mapped to the ambient identity. The slice identities follow
by the group laws and preservation of identity by actual homomorphisms.

If the input groups carry automorphic actions and both homomorphisms
intertwine them with one ambient action, `commutatorMap_equivariant` proves
equivariance for the diagonal source action. The proof uses the coordinate
equivariance equations and preservation of products and inverses by the
ambient action. Geometric integrality and finite type of a smooth connected
affine group product are separate source targets.
