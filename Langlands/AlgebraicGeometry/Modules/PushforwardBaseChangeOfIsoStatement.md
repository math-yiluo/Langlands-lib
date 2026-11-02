# Invertibility of the base-change comparison of a map over spectra

`Langlands.AlgebraicGeometry.Modules.DerivedSections.PushforwardBaseChangeOfIsoStatement`
is a universe-polymorphic `Prop`-valued definition. It states that the
degree-zero base-change comparison `pushforwardBaseChangeOf` of a module map
into a pushforward, over a commutative square whose bases are spectra, is an
isomorphism once both direct images are quasi-coherent and the scalar sections
comparison is an isomorphism. This module does not prove the proposition.

## Complete proposition

```lean
def PushforwardBaseChangeOfIsoStatement : Prop :=
  ∀ (X X' : Scheme.{u}) (R T : CommRingCat.{u}) (φ : R ⟶ T) (f : X ⟶ Spec R)
    (f' : X' ⟶ Spec T) (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
    (P : X.Modules) (N : X'.Modules) (a : P ⟶ (Scheme.Modules.pushforward g).obj N),
    ((Scheme.Modules.pushforward f).obj P).IsQuasicoherent →
    ((Scheme.Modules.pushforward f').obj N).IsQuasicoherent →
    IsIso (scalarSectionsBaseChangeMapOf φ f f' g w a) →
    IsIso (pushforwardBaseChangeOf f (Spec.map φ) f' g w a)
```

The namespace is `Langlands.AlgebraicGeometry.Modules.DerivedSections`, and the
open namespaces are `CategoryTheory` and `AlgebraicGeometry`. There are no
outer parameters or hypotheses besides the universe `u`.

## Actual objects and hypotheses

- `X`, `X'` are arbitrary schemes, `R`, `T` arbitrary commutative rings and
  `φ : R ⟶ T` an arbitrary ring map. The square
  `w : g ≫ f = f' ≫ Spec.map φ` is only assumed to commute; it need not be
  cartesian, and nothing is assumed about `X`, `X'`, `f`, `f'`, `g` or `φ`
  (no flatness, separatedness or quasi-compactness).
- `P : X.Modules` and `N : X'.Modules` are arbitrary module sheaves, and
  `a : P ⟶ g_* N` is an arbitrary morphism into the actual pushforward.
- `pushforwardBaseChangeOf f (Spec.map φ) f' g w a :
  (Spec.map φ)^* (f_* P) ⟶ f'_* N` is the published Library comparison (module
  `Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf`): the
  `Spec.map φ`-pullback/pushforward adjunct of `f_* a` followed by the
  pushforward square isomorphism.
- `scalarSectionsBaseChangeMapOf φ f f' g w a :
  T ⊗_R Γ(X, P) ⟶ Γ(X', N)` is the published `T`-linear map in the same module:
  the extension-of-scalars adjunct of the map on relative global sections
  induced by `a`, composed with the Library's composition and base-ring
  identifications. Here `Γ(X, P)` is the `R`-module
  `(relativeGlobalSections f).obj P`, `Γ(X', N)` is the `T`-module
  `(relativeGlobalSections f').obj N`, and `T ⊗_R -` is
  `ModuleCat.extendScalars φ.hom`.
- The quasi-coherence hypotheses are the actual Mathlib predicate
  `IsQuasicoherent` on `(Spec R).Modules` and `(Spec T).Modules`.

## Relation to the Library and provenance

For `a` the unit of `g^* ⊣ g_*` at a module `M` (so `P = M` and
`N = g^* M`), the Library already proves this implication:
`isIso_pushforwardBaseChange_of_isIso_scalarSectionsBaseChangeMap`
(`AffineDirectImageBaseChange.lean`), whose conclusion and scalar hypothesis
are about `pushforwardBaseChange (Spec.map φ) f f' g w M` and
`scalarSectionsBaseChangeMap φ f f' g w M`. These are the unit cases of the two
maps above, by the published unit-recovery lemmas `pushforwardBaseChangeOf_unit`
and `scalarSectionsBaseChangeMapOf_unit` (both hold by `rfl`). This proposition
is the same implication for an arbitrary `a`; the Library result does not
cover the general case.

Provenance is internal: this is a generalization of that Library result, and no
source states this formulation. It is motivated by The Stacks Project,
Cohomology of Sheaves, section "The base change map" (tag 02N6, label
`section-base-change-map`), `cohomology.tex` lines 2954–3032, including Lemma
`lemma-base-change-map-flat-case` (tag 02N7) from line 2977; the tag map is
`tags.txt` lines 3469–3470. These are at Stacks Project commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, `cohomology.tex` SHA-256
`fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`). In the
proof of Lemma 02N7, the base change map is obtained from a map
`β : I^• ⟶ g'_* J^•` into a pushforward, by applying `f_*`, identifying
`f_* g'_* = g_* f'_*`, and taking the adjunct along `g`. The published
`pushforwardBaseChangeOf` is this construction in a single degree, with `a` in
the role of `β`. Stacks constructs the map but does not prove this
invertibility criterion. The mathematical reason to expect it is that a
morphism of quasi-coherent modules on an affine scheme is an isomorphism when
it is one on global sections, and that the global sections of the pullback of
a quasi-coherent module along `Spec T ⟶ Spec R` are `T ⊗_R -` of the original
sections.

This contribution only states the proposition. Its proof is the subject of a
subsequent task.

## Intended use

In the affine case of flat base change for higher direct images (parent task
`5b778a75-e74b-4ae4-9232-6735e3eefa47`), the comparison is applied to the
components of the Library chain map `CechResolution.cechPullback`. The plan
is to identify the scalar maps there with the components of the Library's
scalar Čech sections map, which are invertible by
`isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated`
(`CechResolution/AffineSectionsBaseChange.lean`), and to obtain
quasi-coherence of both direct images from the Čech-term statement
`CechResolution.CechTermDirectImageStatement`. Neither step is part of this
proposition.

## Authorship

Worker 1098 wrote the Lean file and the first version of this Markdown, shared
as revision 1 of this task's draft. Worker 950 kept the Lean unchanged and
expanded the unit-case comparison and the provenance in this Markdown.
