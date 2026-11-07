# Finite unramified splitting from quasi-splitness and torus reduction

Authors: Worker 303.

This module proves the published statement
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedSplittingStatement`
(module `Langlands.GroupScheme.SimplyConnected.LocalUnramifiedSplittingStatement`)
from two published propositions that are not yet proved:

- `HenselianDiscreteQuasiSplitStatement` (module
  `Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitStatement`):
  every connected reductive group over a field `K` is quasi-split, if `K`
  carries a surjective valuation to `ℤ ∪ {0}` (written multiplicatively) with
  Henselian valuation ring and algebraically closed residue field.
- `QuasiSplitCocycleTorusReductionStatement` (module
  `Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionStatement`):
  every cocycle of a quasi-split semisimple group over a field `K` on a finite
  Galois cover `Spec L ⟶ Spec K` has an actual torus reduction.

The module proves neither hypothesis. It also proves the conclusion only under
these two hypotheses; it is not an unconditional proof of the splitting
statement.

## Results

- `exists_finIntermediateField_whiskerLeft_comp_eq k Ω U X g`: let `Ω / k` be
  an algebraic field extension. Let `U` be quasi-compact and quasi-separated
  over `Spec k`, and `X` locally of finite presentation over `Spec k`. Every
  morphism `g : U ⊗ Spec Ω ⟶ X` over `Spec k` factors as
  `(U ◁ (Spec Ω ⟶ Spec E)) ≫ gE`, for some finite-dimensional intermediate
  field `E` of `Ω / k` (`FinIntermediateField k Ω`) and some
  `gE : U ⊗ Spec E ⟶ X`. Here `⊗` is the fibre product over `Spec k`.
- `localSimplyConnectedUnramifiedSplitting_of_steinberg hqs hred`: the two
  propositions above imply
  `LocalSimplyConnectedUnramifiedSplittingStatement.{u}`.

## Proof of the factorization

This adapts the private `exists_scheme_map` of
`Langlands.GroupScheme.Descent.FiniteStageHom`. The published cone
`baseChangeCone U.left U.hom` of
`Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit` has
apex `U.left ×_k Spec Ω`, which is `(U ⊗ Spec Ω).left` by definition. It is a
limit cone of the cofiltered diagram of the `U.left ×_k Spec E`, with affine
transition maps (`isLimitBaseChangeCone`, which uses that `Ω / k` is
algebraic). Each stage is quasi-compact and quasi-separated because `U.hom`
is. Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
then gives a stage `E` and `h : U.left ×_k Spec E ⟶ X.left`, compatible with
the structure maps to `Spec k`, whose composite with the cone projection is
`g.left`. The cone projection is the underlying map of the whiskering
`U ◁ (Spec Ω ⟶ Spec E)`, and `gE := Over.homMk h`.

## Proof of the reduction

Let `F` be a nonarchimedean local field, and `G` simply connected over `F`.
Let `M / F` be finite Galois, and `ξ` a cocycle on `U = Spec M` over `Spec F`.
Let `K = inertiaFixedField F`, the maximal unramified extension inside
`SeparableClosure F`, and let `P = Spec K` over `Spec F`.

1. *Trivialization over `K`.* Let `G_K` be the base change of `G` along
   `Spec K ⟶ Spec F`. It is semisimple by
   `IsSemisimple.baseChange_of_algebraicExtension`. It is quasi-split by `hqs`,
   applied to the published normalized valuation
   `Geometry.Building.MaximalUnramified.valuation F`, using its published
   surjectivity, Henselian valuation ring and algebraically closed residue
   field. Torus cocycles over `K` are trivial by the published
   `dimensionLEOneTorusCocycleVanishing` and `henselianDiscreteDimensionLEOne`.
   Write `M` as the splitting field of a separable polynomial `p` over `F`
   (`IsGalois.is_separable_splitting_field`). Let `L` be the splitting field of
   the image of `p` over `K`. Then `L / K` is finite Galois, and
   `IsSplittingField.lift` gives an `F`-algebra map `M ⟶ L`, hence a morphism
   `r : Spec L ⟶ Spec M` over `Spec F`. The cocycle
   `Cocycle.baseChange b₀ ξ (Spec L) r` of `G_K` on `Spec L ⟶ Spec K` is
   trivial by the published `cocycle_isTrivial_of_torusReduction` with `hred`.
   `Cocycle.exists_of_baseChange_isTrivial` turns this into `f` on `Spec L`.
   `f` is compatible with `ξ` on pairs of points with the same image in
   `Spec K`. `Spec L ⟶ Spec K` is fpqc (`fieldExtension_fpqc`), so
   `Cocycle.exists_isTrivialOver` gives `gK : U ⊗ Spec K ⟶ G.X`, a
   trivialization of `ξ` relative to `Spec K`.
2. *A finite stage.* `G.X` is smooth, hence locally of finite presentation,
   over `Spec F`. `U` is affine over `Spec F`, and `K / F` is algebraic. So the
   factorization gives a finite intermediate field `E` of `K / F` and
   `gE : U ⊗ Spec E ⟶ G.X` with `(U ◁ (Spec K ⟶ Spec E)) ≫ gE = gK`.
   `Spec K ⟶ Spec E` is fpqc, so `Cocycle.IsTrivialOver.of_whiskerLeft` shows
   that `gE` trivializes `ξ` relative to `Spec E`.
3. *Transport.* `E' = IntermediateField.lift E` is an intermediate field of
   `SeparableClosure F` contained in `K` (`IntermediateField.lift_le`). The
   algebra equivalence `IntermediateField.liftAlgEquiv E : E ≃ₐ[F] E'` makes
   `E'` finite-dimensional over `F`, and gives an isomorphism
   `e : Spec E' ≅ Spec E` over `Spec F`. Applying
   `Cocycle.IsTrivialOver.of_whiskerLeft` to `e.inv` shows that
   `(U ◁ e.hom) ≫ gE` trivializes `ξ` relative to `Spec E'`. This is exactly
   the conclusion of the statement for `E'`.

## Provenance

Internal route to a derived statement. The statement is the finite-stage form
of the vanishing of `H¹(F^ur, G)`. Kaletha–Prasad, Proposition 2.3.5, proves
this vanishing for connected reductive groups over Henselian discretely valued
fields with algebraically closed residue field. The route implemented here is
Steinberg's (Serre, *Galois Cohomology*, III.2.3): the group is quasi-split, a
cocycle of a quasi-split semisimple group reduces to a maximal torus, and
torus cocycles vanish over fields of dimension at most one. The quasi-split
input and the torus-reduction input are the two hypotheses. The torus
vanishing and the field-theoretic facts about `F^ur` are published Library
results. Passing from `F^ur` to a finite stage `E ≤ F^ur` uses the Library's
limit over finite intermediate fields, together with Mathlib's limit
factorization for schemes locally of finite presentation.
