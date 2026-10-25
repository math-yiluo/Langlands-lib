# The geometric fibre functor preserves epimorphisms of finite étale covers

`Langlands.AlgebraicGeometry.FiniteEtale.geometricEpimorphismPreservation` proves exactly
the published target `GeometricEpimorphismPreservation s hfin` from
`Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements`, that is,
`Functor.PreservesEpimorphisms (fiberFunctor s hfin)`. It keeps the statement's parameter
list: `S : Scheme.{u}` with `[ConnectedSpace S]` and `[IsLocallyNoetherian S]`,
`Ω : Type u` with `[Field Ω]` and `[IsAlgClosed Ω]`, a point `s : Spec (.of Ω) ⟶ S`, and
`hfin : ∀ Y : Cover S, Finite (Fiber s Y)`.

`Cover S`, `cover`, `Fiber s Y`, `pointFunctor s` and `fiberFunctor s hfin` are the
published constructions of `Langlands.AlgebraicGeometry.FiniteEtale.Definitions`. The
statement pair and its imports are unchanged. The proof assumes no Galois-category
structure. Connectedness and local noetherianity of `S` belong to the signature but are not
used. Algebraic closure of `Ω` is used to lift points (see below).

The module imports the published
`Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof` and reuses
three of its declarations: the abbreviation `finiteEtale` for `@IsFinite ⊓ @Etale`, the
instance `finiteEtale_hasOfPostcompProperty`, and `etale_coprod_desc`. It also imports
Mathlib's `AlgebraicGeometry.AlgClosed.Basic` and `AlgebraicGeometry.Morphisms.UniversallyOpen`.
Like that module, it sets `backward.isDefEq.respectTransparency.types false` for the whole
file, so that instance search finds the instances for `@IsFinite` and `@Etale`.

The helper lemmas live in the namespace
`Langlands.AlgebraicGeometry.FiniteEtale.EpiPreservation`. The final theorem is in
`Langlands.AlgebraicGeometry.FiniteEtale`. The module adds no instances.

## Morphisms of covers are finite étale with clopen image

For a morphism of covers `f : X ⟶ Y`, write `f.hom.left : X.obj.left ⟶ Y.obj.left` for the
underlying morphism of schemes.

- `finiteEtale_hom_left`: `f.hom.left` is finite étale. Its composite with the structure
  morphism of `Y` is the structure morphism of `X` (`Over.w f.hom`). Both structure
  morphisms are finite étale, so `MorphismProperty.of_postcomp` applies, with the
  postcomposition property `finiteEtale_hasOfPostcompProperty`.
- `isClopen_range_hom_left`: the range of `f.hom.left` is closed and open. It is closed
  because finite morphisms are closed maps (`Scheme.Hom.isClosedMap`, using Mathlib's
  instances that make finite morphisms universally closed). It is open
  because étale morphisms are flat and locally of finite presentation, so universally open
  (Mathlib's `UniversallyOpen.of_flat`), hence open maps (`Scheme.Hom.isOpenMap`).

## An epimorphism of covers is surjective

`surjective_hom_left_of_epi` proves that `f.hom.left` is surjective when `f` is an
epimorphism in `Cover S`. The argument does not assume that a categorical epimorphism of
covers is an epimorphism of schemes.

Let `U` be the open subscheme of `Y.obj.left` on the range of `f.hom.left`, and `V` the one
on its complement; both are open by the previous section. Their inclusions `U.ι` and `V.ι`
have complementary ranges, so Mathlib's `nonempty_isColimit_binaryCofanMk_of_isCompl`
exhibits `Y.obj.left` as the coproduct of `U` and `V`. Let `T` be the cover
`cover (coprod.desc Y.obj.hom Y.obj.hom)` with underlying scheme
`Y.obj.left ⨿ Y.obj.left`. That morphism is finite by a Mathlib instance and étale by
`etale_coprod_desc`. Define two morphisms of covers `g₁ g₂ : Y ⟶ T`:

- `g₁` has underlying morphism `coprod.inl`;
- `g₂` has underlying morphism `d`, the map out of the coproduct `U ⨿ V = Y.obj.left` equal
  to `U.ι ≫ coprod.inl` on `U` and to `V.ι ≫ coprod.inr` on `V`. It lies over `S` because
  this holds on `U` and on `V` (`BinaryCofan.IsColimit.hom_ext`).

The morphism `f.hom.left` factors through `U.ι` (`IsOpenImmersion.lift`), and `U.ι ≫ d`
equals `U.ι ≫ coprod.inl`. Hence `f ≫ g₁ = f ≫ g₂`; equality of morphisms of covers is
checked on the underlying morphisms (`ObjectProperty.hom_ext`, `Over.OverMorphism.ext`).
Since `f` is an epimorphism, `g₁ = g₂`, so `coprod.inl = d` as morphisms of schemes.
Precomposing with `V.ι` gives `V.ι ≫ coprod.inl = V.ι ≫ coprod.inr`. If some point `y` of
`Y.obj.left` were outside the range, then `y` would be a point of `V`. Evaluating both
sides at `y` would give a point in the images of both coprojections, contradicting
Mathlib's `inl_ne_inr`. So every point lies in the range.

## Lifting geometric points

`exists_lift_of_epi` proves: if `f : X ⟶ Y` is an epimorphism of covers and `y : Fiber s Y`,
then some `x : Fiber s X` satisfies `x ≫ f.hom = y`.

Let `P` be the scheme fibre product of `f.hom.left` and `y.left : Spec Ω ⟶ Y.obj.left`, and
`g : P ⟶ Spec Ω` its second projection.

- `P` is nonempty. Pick a point `pt` of `Spec Ω`. By surjectivity some `x` satisfies
  `f.hom.left x = y.left pt`, and Mathlib's `Scheme.Pullback.exists_preimage_pullback`
  gives a point of `P` above `x` and `pt`.
- `P` has a closed point `p`. `f.hom.left` is finite, hence affine, and `Spec Ω` is
  affine, so `P` is affine by a Mathlib instance and its underlying space is compact.
  Schemes are T0 spaces, so `IsClosed.exists_closed_singleton` gives `p`.
- `g` is finite, as a base change of the finite morphism `f.hom.left`, hence locally of
  finite type. Since `Ω` is algebraically closed, Mathlib's `pointOfClosedPoint g p hp`
  is a section `σ : Spec Ω ⟶ P` of `g` (`pointOfClosedPoint_comp`: `σ ≫ g = 𝟙`).

Then `σ ≫ pullback.fst ≫ f.hom.left = σ ≫ g ≫ y.left = y.left` by `pullback.condition`.
The morphism `σ ≫ pullback.fst : Spec Ω ⟶ X.obj.left` lies over `S`: its composite with the
structure morphism of `X`, which is `f.hom.left ≫ Y.obj.hom`, equals `y.left ≫ Y.obj.hom`,
that is `s` (`Over.w y`). So `Over.homMk (σ ≫ pullback.fst)` is a point `x : Fiber s X`.
The identity above gives `x ≫ f.hom = y` (`Over.OverMorphism.ext`).

## Conclusion

- `preservesEpimorphisms_pointFunctor`: `pointFunctor s` preserves epimorphisms. The
  published `pointFunctor s` maps `f` to postcomposition with `f.hom`. A morphism of types
  is an epimorphism exactly when it is surjective (Mathlib's `epi_iff_surjective`), and
  surjectivity is `exists_lift_of_epi`.
- `geometricEpimorphismPreservation`: the published `fiberFunctor_comp_incl` states that
  `fiberFunctor s hfin ⋙ FintypeCat.incl = pointFunctor s` holds by `rfl`, so the
  composite preserves epimorphisms. The inclusion `FintypeCat.incl` is faithful, so it
  reflects epimorphisms (Mathlib's instance dual to `reflectsMonomorphisms_of_faithful`).
  Mathlib's `Functor.preservesEpimorphisms_of_preserves_of_reflects` then shows that
  `fiberFunctor s hfin` preserves epimorphisms.

## Provenance

This is an internal proof of a derived target of the statement module. That module cites
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter X §3,
Definitions (10.25)–(10.26), printed p.150 (PDF p.154), and Theorem (10.28), printed p.151
(PDF p.155). It isolates this condition from Mathlib's `PreGaloisCategory` and
`FiberFunctor`. The Lean route is internal: it shows that a morphism of finite étale
covers has open and closed image, uses a two-valued test map to show that a categorical
epimorphism is surjective, and lifts geometric points through closed points of a fibre
over the algebraically closed field `Ω`. It imports the published definitions, statement
and limits proof by Lean name. It adds no axioms and no instances.

Worker 239 authored this proof pair.
