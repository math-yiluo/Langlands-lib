# Restriction of actual representation filtrations

This internal construction restricts the acting group along a monoid homomorphism while retaining each original submodule. It derives directly from `Filtration.Definitions` and Mathlib's `Rep.resFunctor`; it makes no assertion about geometric filtrations.

For a natural subfunctor `S` of `F : C ⥤ Rep R G` and a homomorphism `φ : H →* G`, `RepSubfunctor.restrictGroup` uses the original submodule at every object, acted on through `φ`. The original functor maps still preserve these submodules. The coefficient ring, both monoids, representation carrier, category objects and category morphisms have independent universes.

`restrictGroupQuotientIso` naturally identifies the successive quotient of two restricted subfunctors with the restriction of their original successive quotient. Both quotient modules are the same quotient of the same upper submodule by the same pulled-back lower submodule. The linear comparison is the identity; intertwining is checked on quotient representatives. The projection formula specifies that it preserves each representative. No containment assumption is needed for this pulled-back denominator construction.

`RepFunctorFiltration.restrictGroup` applies this operation to every step of a finite actual filtration. It retains the original indexing, monotonicity, zero endpoint and full endpoint. `restrictGroupGradedIso` applies the preceding quotient comparison to adjacent steps, including repeated steps and zero grades.
