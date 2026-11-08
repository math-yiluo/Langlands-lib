# The degree of multiplication by `k` on an abelian variety

This module proves that on an abelian variety `A` of dimension `g` over an algebraically
closed field `K`, if `A` has an ample line bundle, then multiplication by a natural number
`k` with `(k : K) ≠ 0` has rank `k ^ (2 * g)` at every point. Rank means the published native
rank `Scheme.Hom.finrank`. The condition `(k : K) ≠ 0` says that the characteristic of `K`
does not divide `k`; it forces `k > 0`. The published cube theorem statement
`FieldCubePullbackStatement.{u}` is a hypothesis and is not proved here.

The module does not use the published `FieldMultiplicationIsogenyStatement.{u}` (the isogeny
property of `[k]` for every `k > 0` in every characteristic). For `(k : K) ≠ 0` the published
`multiplication_isIsogeny_of_ne_zero` (`AbelianScheme/FieldMultiplicationFiniteEtale.lean`)
provides it.

## Provenance

J. S. Milne, *Abelian Varieties* (1986 article, author revision 2022), Theorem 8.2 (p. 13),
states that `n_A : A → A` is an isogeny of degree `n^{2g}` for every positive integer `n`.
Milne's proof uses an ample symmetric invertible sheaf `L` (his (7.2)) and the isomorphism
`n_A^* L ≅ L^{n^2}` (his (6.6)). It then compares intersection numbers:
`deg(n_A) (D^g) = ((n_A^* D)^g) = n^{2g} (D^g)` with `(D^g) ≠ 0`.

The proof here follows the same first two steps. The intersection-number comparison is
replaced by the published `polarizedFiniteFlatRank` (`Picard/PolarizedFiniteFlatRankProof.lean`).
It shows that a finite flat endomorphism pulling an ample `L` back to `L^{⊗q}` has native
rank `q ^ g`, and it is proved from Euler characteristics. Its use here, and the
symmetrization below, are derived content that combines published Library statements.

The Lean result is narrower than Milne's theorem. It covers only `k` with `(k : K) ≠ 0`, the
field must be algebraically closed, `A` must carry an ample line bundle, and it states the
degree as the native rank at each point. It does not prove that `[k]` is an isogeny; for
these `k` that is the published `multiplication_isIsogeny_of_ne_zero`.

## Declarations

### Symmetrization (section `Symmetrization`, any abelian scheme `A` over any base `S`)

The module's local notations `cls` and `pb` stand for `LineBundle.isoClass` and
`LineBundle.pullbackHom` with the published proof `pullbackTensorComparisonIsIso` that
pullback preserves tensor products. They come from
`Picard/LineBundleIsoClassGroup.lean`, where the isomorphism classes of line bundles form a
commutative group and pullback is a group homomorphism.

- Instance `isIso_multiplication_neg_one_left`: the underlying scheme morphism of
  `multiplication A.toGrp (-1)` is an isomorphism. It is the image of the published
  `multiplicationNegOneIso` (`AbelianScheme/MultiplicationSign.lean`) under the forgetful
  functor `Grp (Over S) ⥤ Scheme`.
- `multiplication_neg_one_left_comp`: this morphism composed with itself is the identity,
  from the `hom_inv_id` field of `multiplicationNegOneIso`.
- `symmetrization A H`: the line bundle `H ⊗ (-1)^* H`, built with `LineBundle.tensor` and
  `LineBundle.pullback`.
- `isAmple_symmetrization`: if `H` is ample then so is `H ⊗ (-1)^* H`. The published
  `closedImmersionPullbackAmple` applies because an isomorphism is a closed immersion, so
  `(-1)^* H` is ample. The published `ampleTensor` then shows that the tensor product is
  ample.
- `symmetrization_symmetric`: `(-1)^* (H ⊗ (-1)^* H) ≅ H ⊗ (-1)^* H`. In the group of
  classes the left side is `pb(cls H) * pb(pb(cls H))`. By `pullbackHom_comp_eq` with
  `multiplication_neg_one_left_comp` and by `pullbackHom_id`, this is
  `pb(cls H) * cls H`, and `mul_comm` finishes the proof. `isoClass_eq_iff` turns the
  equality of classes back into an isomorphism of line bundles. `LineBundle.forget`
  then gives the isomorphism of underlying modules required by the published
  `FieldSymmetricMultiplicationPullbackStatement`.

### Degree (section `Degree`, `K` a field)

- `locallyOfFinitePresentation_of_isFinite A f`: a finite endomorphism of the underlying
  scheme of an abelian scheme over a field is locally of finite presentation. The scheme
  is locally of finite type over `Spec K`, hence locally noetherian
  (`LocallyOfFiniteType.isLocallyNoetherian`). Mathlib then derives finite presentation
  from finite type.
- `multiplication_finite_flat_of_ne_zero A k hk`: for `(k : K) ≠ 0`, the morphism `[k]` is
  finite, flat and locally of finite presentation. The first two come from the published
  `multiplication_isIsogeny_of_ne_zero` (the published `IsIsogeny` unfolds to finite, flat
  and surjective), and the third from the previous lemma.
- `finrank_multiplication_eq_of_ne_zero A cube g hg H hH k hk x` (`K` algebraically closed,
  `hg : A.HasRelativeDimension g`, `H` ample, `hk : (k : K) ≠ 0`): the native rank of `[k]`
  at `x` is `k ^ (2 * g)`. First `k > 0`, since `(0 : K) = 0`. The published
  `fieldSymmetricMultiplicationPullbackOfCube cube`, applied to the symmetric bundle
  `symmetrization A H`, gives `[k]^* (H ⊗ (-1)^* H) ≅ (H ⊗ (-1)^* H)^{⊗ (k * k)}`. With
  `isAmple_symmetrization` and the finiteness and flatness from
  `multiplication_finite_flat_of_ne_zero`, `polarizedFiniteFlatRank` gives rank
  `(k * k) ^ g`, which equals `k ^ (2 * g)` by `pow_two` and `pow_mul`.

## Checks

The module compiles with no errors or warnings. `finrank_multiplication_eq_of_ne_zero`
depends only on
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
