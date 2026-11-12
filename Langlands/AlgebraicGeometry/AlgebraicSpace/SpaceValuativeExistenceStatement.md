# The valuative criterion for separated universally closed morphisms of algebraic spaces

Author: Worker 78.

`SpaceValuativeExistenceStatement` states the implication (1) ⇒ (3) of Lemma 67.42.3
(Tag 0A3Y) of the Stacks Project, chapter *Morphisms of Algebraic Spaces*. The module only
states it and contains no proof.

## Source

The registered source is `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, the
retained folder `literature/Stacks Project - Properties of Algebraic Spaces and Morphisms of
Algebraic Spaces, full chapter PDFs (version ed88ff78)/` (folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`). The cited file is
`spaces-morphisms.pdf` (SHA-256
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`), Stacks Project
version ed88ff78.

Lemma 67.42.3 (Tag 0A3Y) is on printed pp. 90–91. It reads: "Let `S` be a scheme. Let
`f : X → Y` be a morphism of algebraic spaces over `S`. Assume `f` is quasi-compact and
separated. Then the following are equivalent (1) `f` is universally closed, (2) the existence
part of the valuative criterion holds as in Definition 41.1, and (3) given any commutative
solid diagram

```
Spec(K) ──→ X
   │        │
   ↓        ↓
Spec(A) ──→ Y
```

where `A` is a valuation ring with field of fractions `K`, there exists a dotted arrow, i.e.,
`f` satisfies the existence part of the valuative criterion as in Schemes, Definition 20.3."
The dotted arrow is a morphism `Spec(A) → X` making both triangles commute.

The point of form (3) is that no extension of the fraction field is needed. In the general
existence part of Definition 41.1 (printed pp. 82–83) one may have to pass to a field
extension `K'/K` and a valuation ring `A' ⊂ K'` dominating `A`; Lemma 41.5 (Tag 0A3W,
printed pp. 86–87) removes the extension for separated morphisms, and Example 41.6 (Tag 03KI,
printed p. 87) shows that it cannot be removed in general. Lemma 44.1 (Tag 0A40, printed
p. 95) is the corresponding valuative criterion for proper morphisms.

## Objects

All objects are the Library's actual ones.

- `S : Scheme.{u}` is an arbitrary scheme, and `X Y : AlgebraicSpace S` are algebraic spaces
  over `S` in the sense of `Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`: fppf sheaves
  on schemes over `S` with representable diagonal and a surjective étale scheme atlas, as in
  the Stacks Project (no quasi-separatedness condition). `f : X ⟶ Y` is a morphism of
  algebraic spaces over `S`.
- `IsQuasiCompactMorphism f`, `IsSeparatedMorphism f` and `IsUniversallyClosedMorphism f` are
  the published predicates of `SpaceMorphismProperties.lean`, which follow the Stacks Project
  definitions (Tags 03HE, 03HL and 03HI). Separatedness says that the relative diagonal
  `X ⟶ X ×_Y X` is a representable closed immersion. Universal closedness says that for every
  scheme `T` over `S` and every `g : h_T ⟶ Y` the map of topological spaces of points
  `|X ×_Y h_T| → |h_T|` (the Library's `Points` with `pointTopology`, Stacks Tag 03BX) is
  closed; Stacks Lemma 67.9.5 shows that testing on schemes suffices.
- `A : Type u` is a commutative ring that is a domain and a valuation ring (Mathlib's
  `ValuationRing`), and `K : Type u` is a field with `[Algebra A K] [IsFractionRing A K]`, so
  `K` is the field of fractions of `A`. These are the hypotheses of Mathlib's
  `AlgebraicGeometry.ValuativeCommSq` for schemes.
- `s : Spec A ⟶ S` is the structure morphism of `Spec A`. The scheme `Spec K` is viewed over
  `S` through `Spec K ⟶ Spec A ⟶ S`, where the first map is `Spec` of `algebraMap A K`.
  `Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl` is this morphism
  `Spec K ⟶ Spec A` in `Over S`.
- A morphism from `Spec K` (resp. `Spec A`) to `X` over `S` is a section of the sheaf `X` over
  that scheme over `S` (Yoneda), so `x : X.sections (Over.mk (Spec.map (...) ≫ s))` is the
  upper arrow `Spec K → X` and `y : Y.sections (Over.mk s)` is the lower arrow `Spec A → Y`.
  `mapSections f _` applies `f` to sections and `X.pullback`, `Y.pullback` restrict sections
  along a morphism of schemes over `S`.

## The statement

`SpaceValuativeExistenceStatement` says: for every scheme `S`, every morphism `f : X ⟶ Y` of
algebraic spaces over `S` with `IsQuasiCompactMorphism f`, `IsSeparatedMorphism f` and
`IsUniversallyClosedMorphism f`, every valuation ring `A` with fraction field `K`, every
`s : Spec A ⟶ S`, every section `x` of `X` over `Spec K` and every section `y` of `Y` over
`Spec A` such that `f(x)` equals the restriction of `y` to `Spec K` (commutativity of the
solid square), there is a section `a` of `X` over `Spec A` whose restriction to `Spec K` is
`x` and with `f(a) = y` (the dotted arrow, making both triangles commute).

## Relation to the source and derived content

The statement is exactly the implication (1) ⇒ (3) of Tag 0A3Y, with the same hypotheses:
`f` quasi-compact and separated, and universally closed. The converse implications are not
stated. The universe convention is the Library's: `S`, the valuation ring and its fraction
field live in the universe `u` of the base schemes, as do all test schemes of the algebraic
spaces. Morphisms from schemes to algebraic spaces are sections, by the Yoneda lemma, which
is how the Library expresses them throughout (`RingPoints`, `SpaceMorphismProperties`).

Derived here: only the name of the statement and the encoding of the diagram by sections.

## Use

This statement is the input to the planned proof of Conrad's Corollary 5.6 for algebraic
spaces, `LocalFieldProperPointMapStatement`: a proper morphism of algebraic spaces is
quasi-compact, separated and universally closed (`IsProperMorphism`), and the valuative
lift replaces Conrad's use of Chow's lemma for algebraic spaces.
