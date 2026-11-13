# Reduction of Artinian ideal H² injectivity to the residue field

This module reduces
`Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.{u}`
to two published `Prop` targets:

- `Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.NaturalityStatement.{u}`,
  a finite coordinate comparison of elementary ideal cohomology with
  residue-field structure cohomology, natural in every compatible
  coefficient pullback;
- `Langlands.AbelianScheme.FieldH2PrimitiveInjectivityStatement.{u}`,
  the field case for structure-sheaf H².

The Prop-valued definition
`Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityReductionStatement.{u}`
is

```text
NaturalityStatement.{u} → FieldH2PrimitiveInjectivityStatement.{u} →
  ArtinianH2PrimitiveInjectivityStatement.{u}
```

and the theorem
`Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.of_naturality`
proves it. The module proves neither hypothesis and does not prove the
Artinian statement unconditionally. No statement it imports is changed.

## Structure-module pullback

The namespace `Langlands.AbelianScheme.ArtinianH2Reduction` proves three
facts about the published definition `ElementaryArtinianIdealCohomology.structurePull`,
the `K`-linear map on actual structure-sheaf relative cohomology over a field
`K`. That map is the canonical `relativeCohomologyPullback` followed by the
canonical `pullbackUnitIso` comparison.

- `structurePull_id`: `structurePull (𝟙 X) n = LinearMap.id`. Under the
  published `pullbackUnitIdentity`, the unit comparison for `𝟙` is the
  component of `pullbackId`. The published identity law
  `relativeCohomologyPullback_identity` then gives the identity.
- `structurePull_comp`: for `h : Y ⟶ X` and `k : Z ⟶ Y`,
  `structurePull (k ≫ h) n = (structurePull k n).comp (structurePull h n)`.
  The proof rewrites with the published composition law
  `relativeCohomologyPullback_comp`. The published `pullbackUnitComposition`
  identifies the unit comparison of `k ≫ h` with the pulled-back
  comparison for `h` followed by the comparison for `k`. The published
  coefficient naturality `relativeCohomologyPullback_naturality` moves the
  comparison for `h` past the pullback along `k`.
- `structurePull_injective_of_iso`: for an isomorphism `e : Y ≅ X`, the map
  `structurePull e.hom n` is injective. By the two previous laws,
  `structurePull e.inv n` is a left inverse.

## Base change of the group law to a field

Let `R` be a commutative ring, `K` a field, `s : Spec K ⟶ Spec R`, and `A` an
abelian scheme over `Spec R`. Write `F = Over.pullback s` and
`A_K = (AbelianScheme.baseChange s).obj A`, whose underlying object is
`F.obj A.X`.

- `prodIso s A : F.obj (A.X ⨯ A.X) ≅ A_K.X ⨯ A_K.X` is Mathlib's
  `PreservesLimitPair.iso`. The functor `Over.pullback s` is a right adjoint
  and preserves binary products.
- `prodIso_hom_fst` and `prodIso_hom_snd` are Mathlib's `prodComparison_fst`
  and `prodComparison_snd`.
- `prodIso_hom_mul` states
  `(prodIso s A).hom ≫ (prod.fst * prod.snd) = F.map (prod.fst * prod.snd)`.
  The right side is `F.map prod.fst * F.map prod.snd` by `Functor.map_mul` for
  the monoidal functor `F`, and `MonObj.comp_mul` with the two previous
  lemmas gives the left side. The group structure on `A_K.X` used here is
  the one given by `AbelianScheme.baseChange`, which is defined through
  `GroupScheme.baseChange s = (Over.pullback s).mapGrp`. It is therefore
  the structure transported by `F`.
- `residue_injective`, assuming `FieldH2PrimitiveInjectivityStatement.{u}`,
  proves injectivity of

  ```text
  structurePull (F.map (prod.fst * prod.snd)) 2
    - structurePull (F.map prod.fst) 2 - structurePull (F.map prod.snd) 2
  ```

  on `H²(F.obj A.X, O)`. Each `F.map g` is `(prodIso s A).hom ≫ g_K`, where
  `g_K` is the corresponding arrow for `A_K`. By `structurePull_comp`, the
  displayed map is `structurePull (prodIso s A).hom 2` composed with the
  reduced coproduct of `A_K`. The field statement applied to `K` and
  `A_K` makes the reduced coproduct injective, and
  `structurePull_injective_of_iso` makes the first factor injective.

## Flatness and properness of the self-product

`prod_flat_proper` proves that for `X Y : Over S` with flat proper structure
morphisms, `(X ⨯ Y).hom` is flat and proper. Mathlib's
`Over.isPullback_of_binaryFan_isLimit` exhibits the first projection as a base
change of `Y.hom`, so it is flat and proper. `(X ⨯ Y).hom` is that projection
followed by `X.hom`. For an abelian scheme `A`, `A.X.hom` is smooth, hence flat,
and proper, so this applies to `A.X ⨯ A.X`.

## The reduction

`ArtinianH2PrimitiveInjectivityStatement.of_naturality` takes the data of the
Artinian statement: `φ : B' →+* B`, the abelian scheme `A`, and compatible
coefficient maps `km`, `k1`, `k2` for `m`, `p1`, `p2` on `P = A.X ⨯ A.X`. It
applies `NaturalityStatement` with `X = A.X`, `Y = P` and `n = 2`, using
`prod_flat_proper` for `P`. This yields `d` and additive equivalences `eX`,
`eY` onto `Fin d`-indexed families in residue structure cohomology. For each
compatible pair `(f, k)` and coordinate `l`, they satisfy
`eY (pull f k x) l = structurePull ((residuePullback φ).map f) 2 (eX x l)`.
The target's `pull f k` is by definition `idealPull φ f k 2`, and its
`compatible` predicate is `Compatible φ`.

Suppose the reduced coproduct takes the same value on `x` and `y`. Apply `eY`
and evaluate at a coordinate `l`. Additivity of `eY` and the coordinate
equations give equal values of the residue reduced coproduct on `eX x l` and
`eX y l`. Here `residuePullback φ` is `Over.pullback (residueBaseMap φ)`, so
`residue_injective` with `s = residueBaseMap φ` gives `eX x l = eX y l`. This
holds for every `l`, so `eX x = eX y`. Injectivity of `eX` gives `x = y`.

## Provenance and authorship

This is internal derived mathematics. It formalizes the step in D. Mumford,
J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, 3rd edition (1994),
Chapter 6, proof of Proposition 6.7, p.118, that is recorded in the paired
Markdown of `ArtinianH2PrimitiveInjectivityStatement`. That step identifies the
three coefficient maps with residue-fibre maps tensored with `ker φ` and
deduces injectivity from the abelian-variety case. Here the tensor
identification is replaced by the finite coordinate system of
`NaturalityStatement`, and the abelian-variety case is
`FieldH2PrimitiveInjectivityStatement`. The structure-pullback functoriality,
base-change comparison and flatness facts are elementary consequences of
published Library laws and Mathlib.

Worker 858 wrote this module on Task 5896. Worker 210 authored the
`NaturalityStatement` target and the definitions of `structurePull` and
`residuePullback` used here.
