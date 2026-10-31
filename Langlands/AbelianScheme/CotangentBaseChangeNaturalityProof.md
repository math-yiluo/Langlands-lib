# Naturality of the actual cotangent base-change maps

For every `S : AlgebraicGeometry.Scheme.{u}`, with arbitrary universe `u`,
`Langlands.cotangentBaseChangeNaturalityStatements S` proves the unchanged
published proposition `Langlands.CotangentBaseChangeNaturalityStatements S`.
Its first component is the naturality square for arbitrary group schemes
and their actual homomorphisms. Its second component is the specialization
to actual abelian-scheme homomorphisms through `AbelianScheme.groupHom`.

For `b : T ⟶ S`, `G,H : GroupScheme S`, and `f : G ⟶ H`, the pointwise lemma
`Langlands.GroupScheme.cotangentBaseChangeMap_naturality b f` states

```text
(pullback b).map (cotangentMap f) ≫ cotangentBaseChangeMap b G =
  cotangentBaseChangeMap b H ≫ cotangentMap ((baseChange b).map f).
```

These are the published maps in `LieFunctor` and `LieBaseChange`, acting
on the actual module sheaves. There are no extra geometric assumptions,
and the proof does not require any of the differential or cotangent
comparison maps to be invertible.

## Implemented proof

The private `sectionPullbackIso` identifies pullback along a chosen arrow
`eY : K ⟶ Y` with successive pullback along `g : X ⟶ Y` and `eX : K ⟶ X`
when `eX ≫ g = eY`. It is the inverse equality comparison followed by the
inverse composition comparison. The proof of `sectionPullbackIso_comp`
follows the generic section calculation in the published `LieFunctor`
implementation: substitute the two section equations, evaluate Mathlib's
`pseudofunctor_associativity` on a module, and cancel the composition
isomorphisms. `sectionPullbackIso_pullback` derives the compatibility with
precomposing both chosen arrows by an arbitrary `k : L ⟶ K`.

The private `sectionSquareMap` abbreviates that section comparison
followed by pullback of the actual `relativeDifferentialsSquareMap` for a
commutative square. It is proof bookkeeping; its map is determined by the
published construction, and no naturality witness is supplied as data.
`sectionSquareMap_comp` uses naturality of the section comparison, its
composition law, and the published `relativeDifferentialsSquareMap_comp`.
`sectionSquareMap_pullback` combines the section pullback calculation with
naturality of `pullbackComp`. Equality of the horizontal and base arrows
gives `sectionSquareMap_congr` by substitution.

The two private identification lemmas express the published `cotangentMap`
and `cotangentBaseChangeMap` in this notation. The former is the
fixed-base differential square pulled back along the identity sections.
The latter is `pullbackComp b eG` followed by the section-pulled square
for the first projection of the actual scheme fiber product; the equation
of chosen arrows is precisely `identitySection_baseChange_fst`.

For the group-scheme square, use these identifications and
`sectionSquareMap_pullback`, then apply `sectionSquareMap_comp` on both
sides. Cancel the common `pullbackComp b eH` comparison. The remaining
maps agree because the underlying base-changed homomorphism satisfies
the first-projection equation `pullback.lift_fst`. The two base arrows
are `b ≫ 𝟙 S` and `𝟙 T ≫ b`, both equal to `b`; congruence finishes
the equality.

`Langlands.GroupScheme.cotangentBaseChangeNaturality` packages the general
square as its published proposition. In the abelian namespace, the
pointwise lemma applies the group lemma to `groupHom f`: the existing
abelian and commutative-group base-change definitions have exactly the
same underlying group objects and homomorphisms. Thus the specialization
needs no additional comparison. The two proposition proofs supply the
conjunction in `Langlands.cotangentBaseChangeNaturalityStatements`.

## Provenance and scope

This is an internal coherence consequence of the published actual
constructions and Mathlib's module pullback pseudofunctor. It imports
`CotangentBaseChangeNaturalityStatement` and
`RelativeDifferentialsBaseChangeTransport`; no independent assertion
is translated from original literature here. The target and all its
imported Lean/Markdown pairs are unchanged.

Worker 310 authored this proof and explanation, using the published
generic section-composition proof pattern from `LieFunctor`.
The separate Lie base-change existence, Lie naturality, and determinant
transport obligations remain separate tasks.
