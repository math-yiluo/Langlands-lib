# The Mumford family is geometrically Picard zero, assuming the cube identity

Author: Worker 255. P3-033 documentation correction: Worker 1054, following
the 2026-10-29 external audit.

This module reduces the target proposition
`Langlands.AbelianScheme.MumfordBundlePicardZeroStatement` to two published
propositions:

- `Langlands.GroupScheme.FieldCubePullbackStatement`, the cube-pullback
  identity for commutative, smooth, proper, geometrically connected group
  schemes over a field;
- `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement`,
  saying that every line bundle on `Spec K` is isomorphic to the structure
  sheaf.

The main result is the explicitly conditional theorem

`Langlands.AbelianScheme.MumfordPicardZero.mumfordBundlePicardZero_of_cube
  (cube : FieldCubePullbackStatement) (triviality : FieldLineBundleTrivialityStatement) :
  MumfordBundlePicardZeroStatement`.

The module neither proves nor assumes either hypothesis anywhere else. The
triviality proposition is proved elsewhere in the Library, as
`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality` (module
`Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof`). The
cube-pullback proposition has no unconditional proof in the Library:
`Langlands.GroupScheme.fieldCubePullbackOfIsomorphism` (module
`Langlands.AbelianScheme.FieldCubePullbackAssembly`) derives it only from the
further proposition
`Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismStatement`, which is
not proved. So the target is not yet proved. A proof of the cube-pullback
proposition, passed to this theorem together with `fieldLineBundleTriviality`,
would prove it. All declarations are in the namespace
`Langlands.AbelianScheme.MumfordPicardZero`.

## Tensor and pullback helpers

- `tensorIsoOf e d` tensors two isomorphisms of module sheaves by applying the
  tensor bifunctor to the pair `(e, d)`.
- `middleFourIso A B C D : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D)` is built
  from the published associator `tensorAssociator` and symmetry `tensorComm`.
- `pullbackTensorIso preservation f M N : f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` is the
  component at `(M, N)` of the fixed comparison `pullbackTensorComparison f`,
  which the hypothesis `preservation` makes invertible.
- `pullbackCompIso f g h w M : h^*M ≅ f^*(g^*M)`, for `w : f ≫ g = h`, combines
  `Scheme.Modules.pullbackCongr` and `Scheme.Modules.pullbackComp`.

## Constant bundles and the theorem of the square

`isTranslationInvariant_pullback_hom G P` shows that for a group scheme `G`
over any base `S` and a line bundle `P` on `S`, the pullback of `P` along the
structure map of `G` is translation invariant. Every translation is a morphism
over `S` (`Over.w`), so pulling back along it composes with the structure map
to the structure map again. This lemma needs neither hypothesis.

The section `Square` works over `Spec K` for an arbitrary field `K`.

- `constantIso triviality G b N` identifies the pullback of `N` along the
  constant map `G.X → Spec K → G.X` with value the point `b` with the structure
  sheaf. It factors the constant map through `Spec K`, applies `triviality` to
  `b^*N`, and uses the published `pullbackUnitIso`.
- `squareIso triviality G a x N cubeIso` gives an explicit isomorphism
  `t_x^*(t_a^*N) ⊗ N ≅ t_a^*N ⊗ t_x^*N`. Here `cubeIso` is the cube
  isomorphism for the three points `f = a`, `g = x` (both constant on `G.X`)
  and `h = 𝟙`. Its source `t_x^*(t_a^*N)` comes from the identity
  `t_a ∘ t_x = t_{a+x}`, proved with `points_translation`. The three factors
  of the cube identity pulled back along constant maps, namely `a`, `x` and
  `a + x`, are replaced by the structure sheaf using `constantIso` and the
  unitors.
- `isTranslationInvariant_square preservation cube triviality G a N N' evaluation`
  proves that for an abelian scheme `G` over `Spec K`, a `K`-point `a`, line
  bundles `N, N'` and an evaluation `N ⊗ N' ≅ O`, the bundle `t_a^*N ⊗ N'` is
  translation invariant. For each point `x` it obtains the cube isomorphism
  from `cube` (whose smoothness, properness, geometric connectedness and
  commutativity hypotheses are the fields of `G`), then computes
  `t_x^*(t_a^*N ⊗ N') ≅ (t_x^*t_a^*N ⊗ t_x^*N') ⊗ (N ⊗ N')`. Using
  `middleFourIso` and `squareIso` this becomes
  `(t_a^*N ⊗ N') ⊗ (t_x^*N ⊗ t_x^*N')`, and the pulled-back evaluation
  `pullbackTensorEvaluation` cancels the last factor.

## The geometric fibre of the Mumford family

The section `Fibre` fixes an abelian scheme `A` over `S`, a field `K` and a
morphism `s : Spec K → A`. It uses the same transparency options as the
published `Langlands.AbelianScheme.KernelBaseChange`, so that the bundled base
changes unfold to their pullback descriptions.

- `paramChange A` is the base change of `A` along its own structure map, the
  abelian scheme `A ×_S A` over the parameter factor `A`.
  `fibre A s` is its base change along `s`, the fibre of the family at `s`.
  These are exactly the objects in `IsPicardZeroFamily` and
  `IsGeometricallyPicardZero` for the Mumford family.
- `fibreToProduct A s` is the map from the fibre to the parameter-first
  self-product `mumfordProduct A`. It is the first fibre-product projection
  followed by the inverse product symmetry, the map along which
  `familyLineBundle` and `fibreLineBundle` pull back.
- `fibreInclusion A s` is the map from the fibre to `A` by its non-parameter
  coordinate. `fibrePoint A s` is the `K`-point of the fibre given by `s`
  itself, so `fibrePoint_inclusion` states that it maps to `s`.
- `fibreToProduct_fst`: the parameter coordinate is constant, equal to the
  structure map of the fibre followed by `s`. `fibreToProduct_snd`: the second
  coordinate is `fibreInclusion A s`.
- `fibreToProduct_addition` proves that `mumfordAddition A`, restricted to
  the fibre, is translation by `fibrePoint A s` followed by the inclusion. The
  proof composes the two published multiplicative point equivalences
  `Langlands.GroupScheme.baseChangePointsEquiv` (for `s` and for the structure
  map of `A`). This sends a point `y` of the fibre to a point of `A` whose
  underlying map is `y ≫ fibreInclusion A s`. The restricted first and second
  projections are the images of the constant point and of the identity
  (`MonObj.comp_mul`), and multiplicativity identifies their product with the
  image of the translation.
- `mumfordFibreIso preservation L₀ M` is an explicit isomorphism from the
  fibre restriction of `(m^*L₀ ⊗ p1^*M) ⊗ p2^*M` to
  `π^*(s^*M) ⊗ (t^*(ι^*L₀) ⊗ ι^*M)`. Here `π` is the structure map of the
  fibre, `t` is translation by `fibrePoint A s` and `ι = fibreInclusion A s`.
  It uses pullback composition, the tensor comparison and the three lemmas
  above, then a symmetry and an associator.

## The conditional theorem

`mumfordBundlePicardZero_of_cube` takes a proof `preservation`, `S`, `A`, `L`,
`M`, `evaluation`, an algebraically closed field `K` and `s`. By
`mumfordBundle_forget`, the underlying line bundle of the Mumford family is
definitionally `(m^*L₀ ⊗ p1^*M) ⊗ p2^*M` with `L₀` the underlying line bundle
of `L`. Through `mumfordFibreIso`, its fibre at `s` is isomorphic to
`π^*(s^*M) ⊗ (t^*(ι^*L₀) ⊗ ι^*M)`. The first factor is translation invariant by
`isTranslationInvariant_pullback_hom`. The second is translation invariant by
`isTranslationInvariant_square` applied to `fibre A s`, `fibrePoint A s`, the
restrictions `ι^*L₀, ι^*M` and the restricted evaluation
`pullbackTensorEvaluation preservation ι _ _ evaluation`. The published
`isTranslationInvariant_tensor` and `isTranslationInvariant_of_iso` conclude.
Algebraic closedness of `K` is not used.

## Provenance and scope

The provenance is internal: the module consists of interface constructions and
a conditional derivation from existing Library declarations, and it attributes
no new theorem to the literature. Its route is the derivation recorded in
`MumfordBundlePicardZeroStatement.md`, from Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, Theorem (2.9) (theorem of the square) and
Definition (2.15) with the paragraph after it. There, the square is deduced
from the field cube identity with `h` the identity, which is how `squareIso`
uses `cube`.

The only proved assertions are the stated isomorphisms and lemmas and the
conditional theorem. The module does not prove the cube identity, the
triviality of line bundles over a field, or the target unconditionally. It
also makes no claim about Picard groups, representability or dual abelian
schemes.
