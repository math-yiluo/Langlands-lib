# Spreading bialgebra isomorphisms along scalar extensions

This is an internal helper for the local-to-neighborhood step in Task 6940.
Its main theorem is `Langlands.BialgebraSpreading.exists_bialgEquiv`.

Let `G i` be a directed system of commutative `R`-algebras indexed by a
nonempty directed preorder. Let the commutative `R`-algebra `L`, with compatible
`G i`-algebra structures, be its direct limit in the explicit sense of the
published `IsDirectLimit` predicate. Let `A` and `B` be commutative bialgebras
over `R`, finitely presented as `R`-algebras. If

`L ⊗[R] A ≃ₐc[L] L ⊗[R] B`,

then for some stage `i` there is a bialgebra equivalence

`G i ⊗[R] A ≃ₐc[G i] G i ⊗[R] B`.

The theorem uses one arbitrary universe `u` for the index, rings and algebras.
It asserts existence at a stage; it does not assert that the resulting
bialgebra equivalence has a specified comparison with the initially supplied
equivalence. The intermediate algebra equivalence does carry the comparison
needed in the proof. No flatness, domain, noetherian, local-ring, or finite-module
hypothesis is imposed. Hopf algebras are among the bialgebras to which it applies.

## Scalar-extension constructions

`tensorSquareIso R S A` is the actual algebra equivalence

`(S ⊗[R] A) ⊗[S] (S ⊗[R] A) ≃ₐ[S] S ⊗[R] (A ⊗[R] A)`.

It sends `(s ⊗ a) ⊗ (t ⊗ b)` to `(s*t) ⊗ (a ⊗ b)`. It is built from
Mathlib's interchange of tensor factors and the identity `S ⊗[S] S ≃ S`.
The definitions `comul R S A` and `counit R S A` are scalar extensions of the
original algebra maps for comultiplication and counit. Their targets are
respectively `S ⊗[R] (A ⊗[R] A)` and `S ⊗[R] R`.
`tensorSquareIso_comul` and `rid_counit` identify them with the actual coalgebra
maps of `S ⊗[R] A`, using the preceding tensor-square equivalence and
`S ⊗[R] R ≃ S`.

`transition f A` changes the coefficient ring along `f : S →ₐ[R] T`.
`extend f φ` extends an algebra map between `S`-scalar extensions to the
`T`-scalar extensions. It is constructed using the tensor-product universal
property. `extend_transition` gives its comparison with the original map;
identity and composition lemmas give the algebra equivalence `extendEquiv`.

`tensorSquareMap φ` conjugates `φ ⊗ φ` by the tensor-square comparisons.
The transition lemmas prove that the counit, comultiplication, and
`tensorSquareMap` commute with change of coefficients whenever the relevant
maps are compatible. These are proved by induction on pure tensors.
`ofFlatEquations` converts an algebra equivalence satisfying the two equations
in these scalar-extension targets into a bialgebra equivalence.
`counit_comp_bialgEquiv` and `comul_comp_bialgEquiv` prove those equations for
any supplied bialgebra equivalence.

## Implemented spreading proof

The proof first applies the published
`Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit`
to descend the underlying algebra equivalence to a stage `i`. This provides
compatibility with the given equivalence after mapping to `L`.

At that stage, compare the two counit maps into `G i ⊗[R] R` and the two
comultiplication maps into `G i ⊗[R] (B ⊗[R] B)`. Compatibility, the transition
lemmas, and the fact that the equivalence over `L` is a bialgebra equivalence
show that both pairs become equal over `L`. The published
`Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit`
makes each equality true after a further transition. This uses finite type of
`A`, which follows from its algebra finite presentation; it needs no finiteness
of the target of either pair of maps.

Directedness supplies a common later stage. Extend the stage algebra
equivalence to that stage with `extendEquiv`. The transition formulas carry
both equalities to it. Equality on the tensors `1 ⊗ a`, together with equality
on scalar coefficients, gives the two algebra-map equations on the whole
scalar extension. `ofFlatEquations` then supplies the bialgebra equivalence.

The provenance is internal. The proof combines the two named, published
algebra descent theorems (imported through the Library's Anthropic-FLT port)
with Mathlib's bialgebra and tensor-product APIs. It neither assumes an
unproved Hopf-spreading statement nor supplies local reconstruction of a
Hopf algebra from its group-like elements. Application to prime localization
also requires an actual direct-limit description by principal localizations;
that specialization is not part of this module.
