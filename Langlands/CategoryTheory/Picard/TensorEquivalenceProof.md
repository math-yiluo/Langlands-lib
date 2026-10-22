# Tensor inverses and equivalences: proof

Authors: Worker 153 and Worker 266.

The theorem `Langlands.CategoryTheory.Picard.tensorInvertibilityEquivalence`
proves exactly the published proposition
`Langlands.CategoryTheory.Picard.TensorInvertibilityEquivalenceStatement C`,
imported unchanged from `Langlands.CategoryTheory.Picard.TensorEquivalenceStatement`.
It holds for every braided monoidal category `C` with object universe `u` and
independent morphism universe `v`. No hypothesis beyond the category, monoidal
and braided structures of the target is used, and neither an inverse nor an
equivalence is taken as input data.

## Implemented proof

Fix an object `L`.

*Tensor inverse implies equivalence.* Suppose `e : L ⊗ N ≅ 𝟙_ C`. Composing the
braiding `β_ N L : N ⊗ L ≅ L ⊗ N` with `e` gives `e' : N ⊗ L ≅ 𝟙_ C`. The proof
then builds two natural isomorphisms of endofunctors of `C`:

- `η : 𝟭 C ≅ tensorLeft L ⋙ tensorLeft N`, the composite of the inverse of
  Mathlib's left unitor `leftUnitorNatIso C : tensorLeft (𝟙_ C) ≅ 𝟭 C`, the
  image `(tensoringLeft C).mapIso e'.symm : tensorLeft (𝟙_ C) ≅ tensorLeft (N ⊗ L)`,
  and `tensorLeftTensor N L : tensorLeft (N ⊗ L) ≅ tensorLeft L ⋙ tensorLeft N`,
  which comes from the associator;
- `ε : tensorLeft N ⋙ tensorLeft L ≅ 𝟭 C`, the composite of
  `(tensorLeftTensor L N).symm`, the image `(tensoringLeft C).mapIso e` and
  `leftUnitorNatIso C`.

`Functor.IsEquivalence.mk'` takes the candidate inverse `tensorLeft N` with `η`
and `ε` and concludes that `tensorLeft L` is an equivalence. It does not require
the triangle identities, so no coherence computation is needed.

*Equivalence implies tensor inverse.* An equivalence is essentially surjective.
`(tensorLeft L).objPreimage (𝟙_ C)` is an object `N`, and
`(tensorLeft L).objObjPreimageIso (𝟙_ C)` is an isomorphism
`(tensorLeft L).obj N ≅ 𝟙_ C`. Since `(tensorLeft L).obj N` is definitionally
`L ⊗ N`, this witnesses the existential. The braiding is not used in this
direction.

## Scope

This proves only the categorical abstraction of the equivalence of (1) and (2)
in Stacks Project Lemma 17.25.2, as described in the statement's Markdown. It
supplies no sheaf tensor product or scheme instance. It also says nothing about
local freeness, internal Hom inverses or Picard groups.
