# Inverse image and the relative complex Hom functor

This internal supporting construction compares the actual Hom and sections
maps underlying arbitrary sheaf-cohomology pullback. Let `R` be a commutative
ring, `X` and `Y` schemes over `Spec R`, and `f : Y ⟶ X` a morphism over it.
Write `U_X` and `U_Y` for the underlying abelian-sheaf functors, `P` for
inverse image of abelian sheaves along `f.left.base`, and `Z_X`, `Z_Y` for
the constant integer sheaves used in Mathlib's cohomology definition.

`homGlobalSectionsIso_pullback_counit` states that for every abelian sheaf
`B` on `Y` and arrow `b : Z_X ⟶ f_* B`, the global section represented by
`a ≫ P.map b ≫ ε_B` is the section represented by `b`. Here `a` is the
inverse of the actual `constantPullbackIso` at the lifted integer group,
and `ε` is the actual inverse-image/direct-image counit. Global sections of
`f_* B` agree definitionally with those of `B` in this setting. The proof
uses the unit equation for uniqueness of left adjoints, followed by the
hom-equivalence formula for a composite adjunction.

`relativePullbackCounit f K` is the chain map
`P(U_X(f_* K)) ⟶ U_Y(K)` for every integer-indexed module complex `K`.
Its degree components are exactly `ε_(U_Y(K^i))`. Its chain-map equation
and `relativePullbackCounit_naturality` both follow from naturality of
that counit.

For every integer `n`, `relativeComplexHomPullback f n` is a natural
transformation from `complexHom U_X Z_X n` evaluated on `f_* K` to
`complexHom U_Y Z_Y n` evaluated on `K`, for bounded below module
complexes `K`. On a derived morphism `z : Z_X[0] ⟶ Q(U_X(f_* K))[n]`,
it is the composite of:

1. the singleton map of `a : Z_Y ⟶ P(Z_X)`;
2. the inverse of `P.mapDerivedCategorySingleFunctor` at `Z_X`;
3. `ShiftedHom.map z P.mapDerivedCategory`;
4. the shifted exact-functor localization comparison
   `P.mapDerivedCategoryFactors.hom`;
5. the shifted localization of `relativePullbackCounit f K`.

Additivity follows from additivity of shifted Hom under an exact additive
functor and of composition. Naturality follows from shifted-Hom
composition, naturality of the exact-functor localization comparison, and
naturality of the chain-level counit. The usual standard derived category
of abelian sheaves has morphism universe `u+1`; this agrees with the
explicit `complexHom.{u+1}` specialization in the declaration.

The provenance is internal: these are consequences of the imported
adjunctions and localization constructions, not a transcription of an
external theorem. No geometric restriction is imposed on `f`. Exactness
is used only for abelian-sheaf inverse image. This unit does not yet prove
compatibility with `complexComparison`, identify the derived comparison
with `relativeHAddEquiv`, or prove the assigned arbitrary pullback theorem.
