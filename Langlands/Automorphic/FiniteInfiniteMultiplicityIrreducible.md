# Irreducibility of the archimedean multiplicity space

This internal result for Task 7294 equips the finite-factor multiplicity
space with the genuine complexified archimedean Lie action and proves
irreducibility for its combined compact and Lie actions. The finite factor
is supplied as an actual nonzero irreducible admissible subrepresentation.
The full actual realization is assumed irreducible for its concrete operator
algebra. No local inverse-transpose pairing is constructed.

The Lie action is the composition of the existing enveloping action on
multiplicities with the genuine enveloping generator. Evaluating on a
finite-factor vector gives exactly the original realization's complex Lie
action.

The irreducibility proof adapts the published
`TwoFactorExistence.isIrreducible_multRep` tensor argument to the compact and
enveloping operator families. The inclusion of the finite factor witnesses
that its multiplicity space is nonzero. Let `N` be a nonzero multiplicity
subspace stable under the compact and Lie actions. Lie stability extends to
the enveloping algebra by lifting to the tensor algebra and induction on
scalars, generators, products and sums.

The evaluation image of `A ⊗ N` is stable under finite translation, compact
translation and all enveloping operators. Evaluation at one nonzero vector
of `A` is injective on finite intertwiners, so this image is nonzero.
Full-operator irreducibility therefore makes the image the whole actual
carrier. Tensor evaluation is also injective by the existing density and
admissible Schur result. For any multiplicity vector `f`, a preimage of
`f(a)` must thus be the tensor `a ⊗ f`. Applying a linear functional on `A`
equal to one at `a` shows that `f` belongs to `N`. Consequently `N` is the
whole multiplicity space.

The construction and its irreducibility property retain a free field universe
and arbitrary matrix size. Cuspidality is not a premise. The separate
cuspidal decomposition construction supplies the finite-factor inputs for
each actual cuspidal realization.
