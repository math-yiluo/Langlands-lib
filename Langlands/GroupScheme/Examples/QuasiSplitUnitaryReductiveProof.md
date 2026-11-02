# The quasi-split unitary group `U(1,1)` is connected reductive: proof

Author: Worker 866. Proof for task `f169f1c7-f9ca-40b5-a35a-3295c717e3e2`.

The theorem `Langlands.GroupScheme.QuasiSplitUnitary.isConnectedReductive` proves
the unchanged Library proposition `IsConnectedReductiveStatement.{u}` from
`QuasiSplitUnitaryReductiveStatement.lean`. Fix fields `F`, `E` in universe `u`
with `[Algebra.IsQuadraticExtension F E]`, a finite basis `b` of
`Matrix (Fin 2) (Fin 2) E` over `F`, and a conjugation `c ≠ AlgEquiv.refl`. Write
`G = groupScheme b c` and `φ = Spec.map (CommRingCat.ofHom (algebraMap F E))`.
The base change `G_E = baseChangeGroupScheme b c` of `G` along `φ` has total
space `pullback G.X.hom φ`. The Library isomorphism
`splittingIso b c hc : G_E ≅ GL₂` over `Spec E` (module
`QuasiSplitUnitarySplitting`) does most of the work. The proof builds the four
fields of `IsConnectedReductive` separately, as the theorems below.

## `scalarMap_fpqc`

`φ` is surjective, flat and quasi-compact. Mathlib's
`flat_and_surjective_SpecMap_iff` reduces flatness and surjectivity to
faithful flatness of `algebraMap F E`. By `RingHom.faithfullyFlat_algebraMap_iff`
this is `Module.FaithfullyFlat F E`, which instance search finds because `E` is a
nonzero free module over the field `F`. A morphism of affine schemes is
quasi-compact, also by instance search. The Library proof
`Langlands.Shimura.rationalComplexBaseMap_fpqc` is the model.

## `smooth_groupScheme`

`G_E.X.hom` is smooth. `GroupScheme.smooth_of_over_iso` moves the smoothness of
`GL₂` over `Spec E` (`GeneralLinear.smoothStatement`) along the underlying
isomorphism over `Spec E` of `splittingIso`. The morphism `G_E.X.hom` is
`pullback.snd G.X.hom φ`. Smoothness descends along surjective, flat,
quasi-compact morphisms (Mathlib's `DescendsAlong` instance in
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`). So
`MorphismProperty.of_pullback_snd_of_descendsAlong` with `scalarMap_fpqc` gives
smoothness of `G.X.hom`.

## `isAffineHom_groupScheme`

The Library instance `SchemeModel.unitaryGroupScheme_isAffine` says that
`G.X.left` is affine, and `Spec F` is affine. Mathlib's `isAffineHom_of_isAffine`
then shows that `G.X.hom` is an affine morphism.

## `connectedSpace_groupScheme`

`G_E.X.left` is connected. The underlying morphism of schemes of `splittingIso`
is an isomorphism (`isIso_left_of_iso`). Its homeomorphism
`Scheme.homeoOfIso` carries connectedness of `GL₂` over the field `E`
(`connectedSpace_generalLinear`) to `G_E.X.left`. This is the argument of the
Library's `IsPseudoReductive.of_iso`. Since `φ` is surjective, Mathlib's base
change instance makes the projection `pullback.fst G.X.hom φ` surjective. Its
underlying map is continuous, so `Function.Surjective.connectedSpace` shows that
`G.X.left` is connected.

## `hasTrivialGeometricUnipotentRadical_groupScheme`

The base change of `G` to `Spec (AlgebraicClosure F)` has trivial unipotent
radical. `E` is finite over `F`, since it is free of rank `2`
(`Module.finite_of_finrank_eq_succ`). Hence `E` is algebraic over `F`, and
`IsAlgClosed.lift` gives an `F`-algebra map `ι : E →ₐ[F] AlgebraicClosure F`. Let
`ψ = Spec.map (CommRingCat.ofHom ι.toRingHom)`. `Spec.map_comp`,
`CommRingCat.ofHom_comp` and `ι.commutes` give
`toAlgebraicClosure F = ψ ≫ φ`. After this rewrite the goal is about the base
change of `G` along `ψ ≫ φ`. This group scheme is isomorphic to `GL₂` over
`AlgebraicClosure F` through the composite of these isomorphisms of group schemes:

1. `(Functor.mapGrpNatIso (Over.pullbackComp ψ φ)).app G ≪≫
   Functor.mapGrpCompIso.app G`, from the base change along `ψ ≫ φ` to the base
   change along `ψ` of `G_E`. This is the same isomorphism as the Library's
   `GroupScheme.baseChangeCompIso φ ψ G`, written inline to avoid importing
   `Langlands.AbelianScheme.Tate.BaseChangeCoherence`;
2. `(GroupScheme.baseChange ψ).mapIso (splittingIso b c hc)`, to the base change
   along `ψ` of `GL₂` over `E`;
3. `GeneralLinear.baseChangeIso (Fin 2) ψ`, to `GL₂` over `AlgebraicClosure F`.

`HasTrivialUnipotentRadical.of_iso` moves the trivial unipotent radical of `GL₂`
over the field `AlgebraicClosure F` (`hasTrivialUnipotentRadical_generalLinear`,
Milne 19.16 and 19.19 in the Library) back along this composite.

## Scope and provenance

This internal proof follows the route in the statement's Markdown (section
"Intended proof"). The field inputs are Milne, *Algebraic Groups* (2017),
Example 19.19 for `GL_n` and Proposition 19.13 for invariance of reductivity
under field extension. Here they are realised directly in Lean, by smooth
descent along `Spec E ⟶ Spec F`, by the surjective projection for connectedness,
and by factoring `F → AlgebraicClosure F` through `E`. The final theorem keeps
the statement's hypotheses exactly. The hypothesis `hc : c ≠ AlgEquiv.refl`
enters through `splittingIso`. The quadratic hypothesis enters through
`splittingIso` and through finiteness of `E` over `F`. There is no restriction on
the characteristic of `F`, so characteristic `2` is covered.
