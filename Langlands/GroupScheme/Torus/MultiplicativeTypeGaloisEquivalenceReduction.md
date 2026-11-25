# Finite Galois character anti-equivalence from full faithfulness

This module proves that the published proposition
`Langlands.GroupScheme.MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}`
implies the published proposition
`Langlands.GroupScheme.MultiplicativeTypeGaloisEquivalenceStatement.{u}`:

```text
theorem multiplicativeTypeGaloisEquivalence_of_fullFaithfulness
    (hFF : MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}) :
    MultiplicativeTypeGaloisEquivalenceStatement.{u}
```

It is an internal adapter between those two statements; it adds no
mathematical content beyond the published results it combines. Essential
surjectivity is proved unconditionally from the published theorem
`Langlands.GroupScheme.multiplicativeTypeGaloisModuleRealization`
(module `Langlands.GroupScheme.Torus.GaloisModuleRealizationProof`). Fullness
and faithfulness are derived from the hypothesis `hFF`. The hypothesis is used
exactly as published: for every finite Galois `L/k`, any two actual commutative
`k`-group schemes with specified diagonalizable `L`-models of finitely
generated abelian groups (torsion allowed), and any additive map of their
actual `L`-character groups. No smoothness, connectedness, freeness or
characteristic hypothesis is introduced anywhere.

The source of the functor is `(SplitMultiplicativeType k L)ᵒᵖ`, where
`SplitMultiplicativeType k L` is the full subcategory of actual commutative
`k`-group schemes satisfying the existential property
`multiplicativeTypeSplitBy k L`; the target is
`Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L)`. The functor is the published
`SplitMultiplicativeType.characterFunctor k L`, with object assignment
`characterAction` and map assignment `characterPullback` (precomposition with
the base change of the actual ground-field homomorphism).

## Declarations

All declarations are in `Langlands.GroupScheme.SplitMultiplicativeType`, except
the final theorem, which is in `Langlands.GroupScheme`.

- `characterAction_hom_equivariant`: for a morphism
  `φ : characterAction k L H ⟶ characterAction k L G` in the action category,
  the underlying linear map commutes with the canonical Galois representations
  `characterLattice.galoisRepresentation k L H.obj` and
  `characterLattice.galoisRepresentation k L G.obj`. This is the `comm` field
  of `φ`, evaluated at a character, using `FGModuleCat.hom_hom_comp` and the
  published `characterAction_ρ_apply`.
- `characterActionAddHom φ` is the underlying additive map of such a morphism,
  with `characterActionAddHom_apply` its evaluation (by `rfl`).
- `actionRepresentation A`: for an object `A` of the action category, the
  representation `σ ↦ (A.ρ σ).hom.hom` of `L ≃ₐ[k] L` on the carrier of `A.V`,
  stated for the canonical `ℤ`-module structure `AddCommGroup.toIntModule`
  of its additive group (the form required by the realization statement;
  the two `ℤ`-module structures are equal since `Module ℤ` is a subsingleton,
  but they are not syntactically the same instance). `map_one` and `map_mul`
  follow from `A.ρ` being a monoid homomorphism into endomorphisms, with
  `End.mul_def` giving composition order. `actionRepresentation_apply`
  evaluates it (by `rfl`).
- `characterFunctor_faithful_of hFF`: given `f g : X ⟶ Y` in the opposite
  category with equal images, extract the existential splitting witnesses of
  `X.unop` and `Y.unop` (models `M`, `M'`, isomorphisms `i`, `i'`). Apply `hFF`
  to `T := Y.unop.obj`, `T' := X.unop.obj`, these witnesses and the additive
  map `F` underlying the image of `f`. `F` is equivariant by
  `characterAction_hom_equivariant`, so `hFF` gives a unique `a : T ⟶ T'`
  whose character pullback is `F`. Both `f.unop.hom` (by definition) and
  `g.unop.hom` (by the equality of images) have pullback `F`, hence both equal
  `a`; so `f = g` by `Quiver.Hom.unop_inj` and `ObjectProperty.hom_ext`.
- `characterFunctor_full_of hFF`: given a morphism `φ` of character actions,
  apply `hFF` in the same way to its additive map, obtain `a : Y.unop.obj ⟶
  X.unop.obj` with pullback equal to `φ`, and take the preimage
  `(ObjectProperty.homMk a).op`. Equality of action morphisms is checked on
  characters (`Action.hom_ext`, `FGModuleCat.hom_ext`, `LinearMap.ext`); there
  it is exactly the existence clause of `hFF`, since the functor's map is
  precomposition by the base change of `a` (published
  `characterFunctor_map_apply`, by `rfl`).
- `characterFunctor_essSurj`: for an object `A`, the carrier of `A.V` is a
  finitely generated abelian group (`Module.Finite.iff_addGroup_fg`, after
  identifying the two `ℤ`-module structures by `Subsingleton.elim`). The
  published realization theorem applied to it and `actionRepresentation A`
  gives an actual `T`, an isomorphism `i : T_L ≅ D_L(A.V)` and an additive
  equivalence `e : A.V ≃+ X^*(T_L)` intertwining `actionRepresentation A`
  with the canonical Galois representation. The pair `(A.V, i)` witnesses
  `multiplicativeTypeSplitBy k L T`, so `T` is an object `X` of the source.
  The isomorphism `(characterFunctor k L).obj (op X) ≅ A` is `Action.mkIso` of
  the `FGModuleCat` isomorphism `ObjectProperty.isoMk _
  (LinearEquiv.toModuleIso e.symm.toIntLinearEquiv)`; its compatibility with
  the actions at `σ` is checked on `χ = e m`, where it is the intertwining
  identity `e (ρ σ m) = galoisRepresentation k L T σ (e m)`.
- `characterFunctor_isEquivalence_of hFF`: the three properties above give
  `Functor.IsEquivalence`, for fields `k L : Type u` with
  `FiniteDimensional k L` and `IsGalois k L`.
- `multiplicativeTypeGaloisEquivalence_of_fullFaithfulness hFF`: quantifies the
  previous theorem over all such `k`, `L` and instances, which is exactly
  `MultiplicativeTypeGaloisEquivalenceStatement.{u}`.

The only assumptions of the final theorem beyond `hFF` are Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Both statements are the published finite-level derivations of J. S. Milne,
*Algebraic Groups* (2017), Theorem 12.23 (source `milne-2017-algebraic-groups`);
their own Markdown records the exact locators and the correspondence. This module
is internal: it is the routine categorical step that a functor which is fully
faithful and essentially surjective is an equivalence, together with the
adapters between the bundled action category and the unbundled hypotheses of
the two component theorems.
