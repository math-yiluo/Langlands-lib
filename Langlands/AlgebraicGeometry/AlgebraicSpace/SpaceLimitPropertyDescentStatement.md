# Descent of properties of morphisms of algebraic spaces along cofiltered limits

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Printed p.13, start of Section 5: "The first step is to verify that Theorem 3.4
is valid with finitely presented algebraic spaces in place of finitely
presented schemes. This is proved by an étale descent argument ... and is
explained in (the proof of) [Ols, Prop. 2.2] apart from the property of having
fibers non-empty and geometrically connected of pure dimension d." Conrad then
reduces nonemptiness and pure dimension to the scheme case through étale scheme
covers, and treats geometric connectedness of fibres through Lemma 5.1.

Theorem 3.4(2), printed p.5, for a directed system of rings `A_i` with colimit
`A`: "A map `f_{i₀} : X_{i₀} → Y_{i₀}` acquires property **P** upon base change
to some `A_i` if and only if the induced map `f : X → Y` over `A` has property
**P**, where **P** is any of the following properties: closed immersion,
separated, proper, smooth, affine, flat, open immersion, finite, fibers
non-empty and geometrically connected of pure dimension `d`." The objects are
finitely presented, as in Theorem 3.4(1).

## `SpaceLimitPropertyDescends`

`SpaceLimitPropertyDescends P` is a proposition about a property `P` of
morphisms of algebraic spaces over an arbitrary scheme. It quantifies, in one
arbitrary universe `u`, over

- a small cofiltered category `I` and a diagram `D : I ⥤ Scheme` of affine
  schemes, with an actual limit cone `c` (`IsLimit c`);
- a stage `i : I`, algebraic spaces `X` and `Y` over `D.obj i`, and a morphism
  `f : X ⟶ Y`.

Both `X` and `Y` are assumed finitely presented, encoded as in the Library's
`SpaceLimitModelExistenceQuasiSeparated`: each is quasi-separated
(`IsQuasiSeparated`) and has a surjective étale scheme atlas whose structure map
to `D.obj i` is locally of finite presentation and quasi-compact
(`HasAtlasProperty (LocallyOfFinitePresentation ⊓ QuasiCompact)`). It asserts

`P (baseChangeMap (c.π.app i) f) ↔ ∃ (j : I) (g : j ⟶ i), P (baseChangeMap (D.map g) f)`.

The left side is the base change of `f` to the limit along the cone leg; the
right side says that the base change of `f` along a transition map `D.map g` to
some stage `j` has `P`. This is Conrad's "acquires **P** upon base change to
some `A_i` if and only if `f` has **P**".

Conrad's ring setting is the case where `D` is the diagram of spectra of a
directed system of rings and `c.pt` is the spectrum of its colimit. Every
cofiltered diagram of affine schemes is the spectrum of a filtered diagram of
rings, so the general diagram is a derived restatement of the same setting.

## `SpaceLimitPropertyDescentStatement`

`SpaceLimitPropertyDescentStatement` is the conjunction of
`SpaceLimitPropertyDescends P` for the following eight properties, all already
defined in the Library for morphisms `f` of algebraic spaces:

1. closed immersion: `AlgebraicSpace.IsClosedImmersion (hom f)`, the
   underlying transformation is representable and every represented scheme
   projection is a closed immersion;
2. separated: `IsSeparatedMorphism f`, the relative diagonal is a representable
   closed immersion;
3. proper: `IsProperMorphism f`, separated, quasi-compact, locally of finite
   type and universally closed;
4. smooth: `IsSmoothMorphism f`, a commutative square from a smooth scheme
   morphism with étale surjective source chart and étale target chart;
5. affine: `IsAffineMorphism (hom f)`, representable with every represented
   scheme projection affine;
6. open immersion: `AlgebraicSpace.IsOpenImmersion (hom f)`, representable with
   every represented scheme projection an open immersion;
7. finite: `AlgebraicSpace.IsFinite (hom f)`, representable with every
   represented scheme projection finite;
8. fibres nonempty and geometrically connected:
   `HasGeometricallyConnectedFibres f`. For every field `K`, every structure
   morphism `Spec K ⟶ S` and every `K`-point of the target, the points of the
   fibre form a connected space. A connected space is nonempty, so every such
   fibre is nonempty.

## Scope

Two parts of Conrad's list are not stated here: flatness, and the pure
dimension `d` in the last property. The Library has no definition of a flat
morphism of algebraic spaces that need not be representable, and no definition
of fibre dimension for algebraic spaces. They are left for a later unit with
those definitions. Item 8 is the remaining part of Conrad's last property,
"fibers non-empty and geometrically connected", which is the part his Lemma 5.1
is needed for.

No proof is supplied here.

## Provenance

The properties and the equivalence are Conrad's, transported to the Library's
algebraic spaces and their existing morphism predicates. The derived choices
are the general cofiltered diagram of affine schemes, the encoding of finite
presentation, and the omission of flatness and pure dimension explained above.
