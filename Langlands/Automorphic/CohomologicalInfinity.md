# The cohomological condition at infinity for automorphic realizations

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.Automorphic`. The module defines when an actual automorphic operator realization
of `GL_n` over a number field is *cohomological*. Up to a quadratic twist at the real places,
its archimedean part must have nonzero relative Lie algebra cohomology with coefficients in a
finite-dimensional algebraic representation of `Res_{F/ℚ} GL_n`. The module uses the
published relative Lie algebra cohomology `TensorAlgebraicHorizontalCohomology` of the
algebraic coefficient modules (`ArchimedeanAlgebraicCoefficientHorizontalComparison`). It
computes no cohomology, and it asserts neither that cohomological representations exist nor
any relation to regular algebraicity.

## Setting

`F : Type uF` is a number field and `n` a positive natural rank (`[NeZero n]`, as the published
horizontal cohomology requires). `S : OperatorRealization F n` is an actual realization.

- `EmbeddingLabel F` is `Fin (Fintype.card (EmbeddingIndex F))`. Through the published
  `fullEmbeddingEnumeration F` it labels all complex embeddings `ι : F → ℂ`: one label at each
  real place and both orientations at each complex place.
- `AlgebraicCoefficient F n m` is the type of matrix representations
  `MatrixRepresentation (GeneralLinearProductDualNumber.groupScheme (fun _ : EmbeddingLabel F =>
  Fin n) (CommRingCat.of ℂ)) m`, that is, algebraic representations on `ℂ^m` of the complex
  group scheme `∏_{ι : F → ℂ} GL_n`. That group scheme is `Res_{F/ℚ} GL_n ⊗ ℂ`.
- For such a `W`, `TensorAlgebraicHorizontalCohomology (fullEmbeddingEnumeration F) W S q` is
  the published degree-`q` cohomology of the complex of alternating maps
  `Λ^q 𝔤̃ → S ⊗ W` that vanish on the compact Lie algebra `𝔨` and are equivariant for the
  full standard compact group `K_∞ = ∏_{v real} O(n) × ∏_{v complex} U(n)`. Here `𝔤̃` is the
  reduced complex Lie algebra of `GL_n(F_∞)`, which removes the split centre. `GL_n(F_∞)` acts
  on `W` through the embedding coordinates, so this is the relative Lie algebra cohomology
  `H^q(𝔤̃_∞, K_∞; S ⊗ W)`.

## Declarations

- `OperatorRealization.HasNonzeroCoefficientCohomology S` holds when there are a finite type
  `m`, an algebraic coefficient `W : AlgebraicCoefficient F n m` and a degree `q` with
  `Nontrivial (TensorAlgebraicHorizontalCohomology (fullEmbeddingEnumeration F) W S q)`.
- `OperatorRealization.IsCohomological S` holds when there is a Hecke character `χ` of finite
  order (`HeckeCharacter.HasFiniteOrder`) such that the published determinant twist
  `S.determinantTwist χ hχ` has nonzero coefficient cohomology.
- `injective_of_comp_eq_id` is a general lemma: an intertwining map with a left inverse is
  injective.
- `OperatorRealization.injective_tensorAlgebraicHorizontalCohomologyMap`: for a full
  equivalence `e : S.Equivalence T`, the published induced map
  `tensorAlgebraicHorizontalCohomologyMap` on coefficient cohomology is injective. The map
  induced by `e.symm` is a left inverse, by the published identity and composition laws.
- `HasNonzeroCoefficientCohomology.of_equiv` and `IsCohomological.of_equiv`: both conditions
  are transported along full equivalences. The second also uses the published
  `determinantTwist_congr`.
- `OperatorRealization.IsoClass.IsCohomological` (with `isoClass_isCohomological`),
  `CuspidalOperatorRealization.IsoClass.IsCohomological` and
  `PositiveRankCuspidalClass.IsCohomological` are the descended properties of isomorphism
  classes, actual cuspidal classes and mixed-rank cuspidal classes.

## Source correspondence

L. Clozel, *Motifs et formes automorphes : applications du principe de fonctorialité*, in
*Automorphic Forms, Shimura Varieties, and L-functions*, Vol. I (1990), literature ID
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`, SHA256
`ed6ec30fc1f53f7c8ac4276ef449e1cad3ab42457bf5b7ee90a33413345ff96c`. This is a scanned volume;
the PDF page is the printed page plus eleven. The following passages were read from rendered
page images.

- Printed pp.112–113 (PDF pp.123–124): attached to the type at infinity of `π` is a rational
  representation `τ = ⊗_ι τ_ι` of `L = Res_{F/ℚ} GL(n)`. For each infinite place `v`, `𝔤_v` is
  the complex Lie algebra of `GL(n, F_v)`, and `A_v` is the identity component of the split real
  torus Clozel takes, with `𝔞_v = Lie(A_v) ⊗ ℂ`. The Langlands decomposition is
  `𝔤_v = 𝔞_v × 𝔤̃_v`, where `𝔤̃_v` consists of the matrices with imaginary trace and is invariant
  under the standard maximal compact subgroup `K_v`. The published reduced Lie algebra is this
  real-part-of-trace kernel.
- Printed p.114 (PDF p.125): `K_v` is `O(n)` or `U(n)`, and `H^•(𝔤̃_v, K_v; π_v ⊗ τ_v)` denotes
  `(𝔤̃_v, K_v)`-cohomology. Lemma 3.14: for every infinite place `v` there is a character
  `ε_v` of `F_vˣ` of order 2 such that `H^•(𝔤̃_v, K_v; π_v ⊗ ε_v ⊗ τ̃_v)` is nonzero; it is
  computed explicitly. In the complex case `ε_v = 1`.
- Printed p.111 (PDF p.122), Definition 3.12: regularity of `π ∈ Alg(n)`. Lemma 3.14 applies to
  regular `π`. This module does not define or use regularity.

### Derived formulation

1. **A definition from Lemma 3.14.** Clozel proves nonvanishing of this cohomology for regular
   algebraic `π`. The module takes the nonvanishing as the definition of *cohomological*. This
   is a separate notion and does not replace regular algebraicity. The two notions are not
   compared here.
2. **Global cohomology.** The condition is stated for the whole archimedean
   `(𝔤̃_∞, K_∞)`-module of `S` and a coefficient of `∏_ι GL_n`. For an irreducible
   realization, Künneth's formula and the factorization of `S` give
   `H^•(𝔤̃_∞, K_∞; π_∞ ⊗ W) = ⊗_v H^•(𝔤̃_v, K_v; π_v ⊗ W_v)` for `W = ⊗_v W_v`, up to
   multiplicity. So nonvanishing for some `W` is nonvanishing at every infinite place, as in
   Clozel's lemma. This is an explanation and is not proved.
3. **Quadratic twists.** Clozel twists each `π_v` by a local `ε_v` of order at most 2. The
   module twists `S` by `χ ∘ det` for a global Hecke character `χ` of finite order. Its
   archimedean components are of order at most 2 at real places and trivial at complex places.
   Conversely, every family `(ε_v)` of signs at the real places is the archimedean component of
   some finite-order (even quadratic) Hecke character, by class field theory; this is not used.
   Twisting at finite places does not affect the archimedean cohomology.
4. **Arbitrary algebraic coefficients.** Clozel's `τ` is irreducible, and the lemma uses its
   contragredient `τ̃`. The definition allows every finite-dimensional algebraic
   representation `W`. Since `W` ranges over all of them, including contragredients, and
   cohomology is additive in `W`, this does not change the condition.
5. **Disconnected compact group.** As in Clozel, `K_v = O(n)` at real places, including its
   non-identity component. This is why the quadratic twist is needed.

## Scope

The module does not prove:

- that cohomological representations exist;
- that regular algebraic cuspidal representations are cohomological (Clozel's Lemma 3.14);
- the converse, or any computation of the cohomology;
- independence of the choice of quadratic twist.

These are theorem obligations.
