# Projection of a standard Levi representation onto one cuspidal inertia block

Worker 76. Supporting reduction for proof task
`2a804ec7-6b5f-4bbe-93ab-39527f9b50a9` (Renard VI.7.2 Proposition,
`Langlands.CuspidalSupport.BernsteinBlockCharacterizationStatement`). This
module reduces the Levi-side projection step of the fixed-Levi embedding
argument to one published proposition that is not yet proved: Renard VI.3.3.1,
`Langlands.CuspidalSupport.RationalCuspidalInertiaDecompositionStatement`
(proof task `5c59bed4-0f33-47e1-aaa6-1d1145b8b25f`). It does not prove
VI.3.3.1, and every Bernstein-side result below keeps it as an explicit
hypothesis `hSplit`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
VI.7.2 Proposition and proof, printed pp. 184–185 / PDF pp. 190–191; VI.3.3,
equation (VI.3.3.1), printed p. 145 / PDF p. 151.

## Provenance

No source states these results separately; they are derived. The proof of
VI.7.2 (i) decomposes a representation of the Levi `M` as `W = W_D ⊕ W^D`
following (VI.3.3.1) and uses the component `W_D`. The proposition proved here
records the part of that decomposition the fixed-Levi embedding uses: a map
`p : W → W_D` that does not kill any nonzero map from an object of the block
`M(M)_D`. Its conclusion is, word for word, the body of the proposition
`BernsteinLeviBlockProjection` in Worker 5352's module
`Langlands.Representation.CuspidalSupport.BernsteinFixedLeviEmbeddingReduction`
(staged as candidate `f43d37f5-0f82-4414-9079-dc0b0e7ed49d`, not yet
published). This module cannot import an unpublished candidate, so it states
that body inline. Once both modules are published, the conclusion is supplied
by `bernsteinLeviBlockProjectionOfRationalInertiaDecomposition.{uF, uV} i ν family hSplit`.
A private compilation test with a copy of that definition and the same local
instances checked this.

## Declarations

- `exists_rationalInertiaBlockProjection` (any affine group scheme `G` over a
  nonarchimedean local field, any `π`, any smooth `W`). If the inertia block of
  `π` and its complement form an actual category decomposition
  (`IsRationalInertiaCategoryDecomposition G π`), then there are an object `τ`
  with `rationalInertiaBlockProperty G π τ`, a map `p : W ⟶ τ` and a map
  `j : τ ⟶ W` such that `f ≫ p ≫ j = f` for every object `Y` with
  `rationalInertiaBlockProperty G π Y` and every `f : Y ⟶ W`.
- `bernsteinLevi_isRationalInertiaCategoryDecomposition (hSplit) a`: VI.3.3.1
  on the actual standard Levi of a Bernstein cuspidal datum `a`, that is
  `IsRationalInertiaCategoryDecomposition (bernsteinLeviScheme i ν a.roots) a.representation`.
- `bernsteinLeviInertiaProjection (hSplit) a W`: for a smooth representation
  `W` of the literal standard Levi subgroup `levi i ν a.roots`, there are a
  block object `τ` of the Levi scheme, `p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ`
  and `j` back, such that `f ≫ p ≫ j = f` for every block object `Y` and every
  `f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W`.
- `bernsteinLeviInertiaProjection_ne_zero (hSplit) a W`: the same `τ` and `p`,
  with the conclusion `f ≠ 0 → f ≫ p ≠ 0` instead.
- `bernsteinLeviBlockProjection_of_rationalInertiaDecomposition (hSplit)`: the
  previous result for all `a` and `W`, in the form

  ```
  ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)),
    ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
      (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
      ∀ Y, rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
        ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≠ 0 → f ≫ p ≠ 0
  ```

- `bernsteinLeviBlockProjectionOfRationalInertiaDecomposition`: the main
  declaration, the same theorem as a `def` whose type is the implication from
  `RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV}` to the
  displayed proposition. The `linter.defProp` warning is disabled for this
  declaration only.

Here `i`, `ν` and `family : BernsteinStandardFamily i ν` are the published
standard-family objects. The field universe `uF` and the representation
universe `max uF uV` are those of the published target, and VI.3.3.1 is used
at universes `uF, max uF uV`.

## The proof

1. `exists_rationalInertiaBlockProjection`. The first field of the
   decomposition gives a cofan `A` on `W` with components `A true` (block
   property) and `A false` (complement property) and a colimit proof `hc`. Take
   `τ = A true`, `p` the library projection `SmoothRep.cofanProjection hc true`
   and `j` the coproduct inclusion. The library lemma
   `SmoothRep.comp_cofanComponent` (module
   `Representation.Category.DecompositionCentralProjectors`) uses the second
   field of the decomposition (no nonzero maps between the block and the
   complement) to give `f ≫ p ≫ j = f` for every `f` out of a block object.
2. `bernsteinLevi_isRationalInertiaCategoryDecomposition`. The datum's
   cuspidality `a.cuspidal` concerns the literal transport
   `bernsteinLiteralLeviRep i ν a.roots a.representation`. The published
   `rationalLeviCuspidalityTransport` moves it to the pullback along
   `leviRationalPointHomeomorph`. `IsCuspidalFor.of_iso` with
   `SmoothRep.pullbackSymmIso` identifies that pullback with
   `a.representation`. The Levi scheme has the standard family
   `bernsteinLeviStandardFamily i ν family a.roots`, which supplies its
   connected reductive structure, maximal split torus, generic cocharacter,
   parabolic decomposition and closed unipotent radical; its relative root
   system is `relativeRootSystem` of these data. `hSplit` is applied to these
   data, to `a.irreducible` and to the cuspidality just obtained.
3. `bernsteinLeviInertiaProjection`. Put `e = leviRationalPointHomeomorph i ν a.roots`.
   Apply step 1 on the Levi scheme to `SmoothRep.pullback e W`, with the
   decomposition from step 2. Pull `p'` and `j'` back along `e.symm` and
   compose with the isomorphism `SmoothRep.pullbackSymmIso e W`. For a block
   object `Y` and `f`, the object `SmoothRep.pullback e (bernsteinLiteralLeviRep i ν a.roots Y)`
   is again a block object (`rationalInertiaBlockProperty_of_iso` with
   `SmoothRep.pullbackSymmIso e.symm Y`). Step 1 applied to the pullback of `f`
   gives an equation of linear maps, and `SmoothRep.hom_ext'` turns it into
   `f ≫ p ≫ j = f`.
4. `bernsteinLeviInertiaProjection_ne_zero`. If `f ≫ p = 0`, then
   `f = f ≫ p ≫ j = 0`.
5. The last two declarations apply step 4 to every `a` and `W`. The universes
   are given explicitly, as `.{uF, uV}`.

`lean_check` reports no errors or warnings.

## Scope

The only unproved input is VI.3.3.1 (`hSplit`). No admissibility,
finite-length, finite-generation or Jacquet-module hypothesis is added. VI.10.3
and VI.4.1 are not used here; they enter only on the group side of the
fixed-Levi embedding, in Worker 5352's module. The local instances have names
specific to this module. The Levi point topology is
`rationalPointTopology F (bernsteinLeviScheme i ν I).X`, as in
`BernsteinBlockCharacterizationReduction`. The local compactness and
nonarchimedean instances on the Levi points are transported from the literal
Levi subgroup through `leviRationalPointHomeomorph`.
