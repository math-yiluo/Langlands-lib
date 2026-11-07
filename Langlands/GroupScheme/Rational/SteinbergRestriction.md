# Restricting canonical class functions to the supplied Steinberg product

Author: Worker 1284. Provenance: internal and derived from the published affine coordinate and canonical class-function interfaces.

For every affine test morphism `f : Spec A → G`, `ClassFunctions.restriction G f` is evaluation of the actual coordinate algebra at `f`, composed with the actual invariant-algebra inclusion. Its spectrum is exactly `f ≫ ClassFunctions.rho G`, by the published quotient-point coordinate equation. Full faithfulness of relative spectrum and the algebra equivalence associated to a bijective algebra homomorphism prove that this composite is an isomorphism if and only if restriction is bijective.

`SplitPinning.steinbergRestriction e x n` specializes this construction to the published ordered product. Its codomain is the actual standard polynomial algebra `MvPolynomial (Fin r) k`. The spectrum identity and the equivalence with bijective restriction hold for every field in arbitrary universe `u`, each ordering and all supplied root maps and representatives. They require no simple connectedness or further structural premise.

The last helper is conditional: if a family `c` freely generates the actual invariant algebra and its restriction gives a bijective polynomial endomorphism, then the exact supplied product followed by the canonical `rho` is an isomorphism. The proof transfers injectivity through surjectivity of the generating map and transfers surjectivity from the composite. The helper constructs neither fundamental representations nor such a generating family, and proves no unconditional Steinberg quotient theorem. Those are the substantive mathematical obligations retained by `SplitSteinbergQuotientStatement`.

No source-dependent structural theorem is used, and all imported Lean/Markdown pairs remain unchanged.
