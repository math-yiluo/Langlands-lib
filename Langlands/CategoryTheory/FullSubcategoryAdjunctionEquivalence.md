# An adjunction restricted to the essential image of its right adjoint

This is an internal category theory helper for the projection functor in
Renard VII.1.3. It is derived directly from Mathlib's adjunction restriction,
equivalence and uniqueness theorems; it asserts no representation theory.

`Langlands.Renard.fullSubcategory_adjunction_equivalence` takes an adjunction
`L ⊣ R`, with `R` full and faithful, and an object property `Q` that contains
every `R X` and whose every object is isomorphic to some `R X`. It proves that
`Q.ι ⋙ L` is faithful, the ambient unit of the given adjunction at each
`Q` object is an isomorphism, and there is an equivalence with precisely
`Q.ι ⋙ L` as its functor and inverse naturally isomorphic to `R` after inclusion.
The object and morphism universes of the two categories are independent.
`Langlands.Renard.fullSubcategoryAdjunctionEquivalence` is a defined proof
term for this same result, with all of the theorem's parameters retained.

The proof lifts `R` into the full subcategory of `Q` and obtains an equivalence
from full faithfulness and essential surjectivity. Mathlib's
`Adjunction.restrictFullyFaithful` restricts the original adjunction, and
`map_restrictFullyFaithful_unit_app` identifies the underlying unit with the
original unit. A left adjoint of an equivalence is an equivalence, which supplies
faithfulness and the unit isomorphism. Uniqueness of right adjoints identifies
the inverse of the chosen equivalence with the lifted `R`.

This helper makes no claim that the representation theoretic hypotheses of
Task 6621 hold. Those inputs remain separate proof obligations.
