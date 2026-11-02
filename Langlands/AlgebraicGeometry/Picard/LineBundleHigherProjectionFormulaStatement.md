# Projection formula for higher direct images and an actual line bundle

Authors: Worker 943 and Worker 894.

Module `Langlands.AlgebraicGeometry.Picard.LineBundleHigherProjectionFormulaStatement`,
namespace `Langlands.AlgebraicGeometry.Picard`, with `open CategoryTheory AlgebraicGeometry`
and `open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections`. The
file defines one universe-polymorphic proposition,
`LineBundleHigherProjectionFormulaStatement.{u}`. It does not prove it.

## Complete proposition

```lean
def LineBundleHigherProjectionFormulaStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (L : LineBundle Y) (M : X.Modules) (n : ℕ),
    Nonempty (tensorObj L.obj ((higherDirectImage f n).obj M) ≅
      (higherDirectImage f n).obj (tensorObj ((Scheme.Modules.pullback f).obj L.obj) M))
```

Imports: `Langlands.AlgebraicGeometry.Picard.LineBundle`,
`Langlands.AlgebraicGeometry.Modules.Tensor` and
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.

## Meaning of the binders

- `X Y : Scheme.{u}` are schemes and `f : X ⟶ Y` is an arbitrary morphism of schemes. No
  hypothesis is placed on `f`: it need not be quasi-compact, quasi-separated, separated,
  flat, proper or affine.
- `L : LineBundle Y` is the Library's actual line bundle: an object of the full subcategory
  of `Y.Modules` on the sheaves of `𝒪_Y`-modules that are locally free of rank one
  (`IsLocallyFreeRankOne`: each point has an open neighbourhood on which the restriction is
  isomorphic to the structure sheaf). `L.obj` is the underlying `𝒪_Y`-module.
- `M : X.Modules` is an arbitrary sheaf of `𝒪_X`-modules; quasi-coherence is not assumed.
- `n : ℕ` is the degree.

The operations are the published ones, used unchanged:

- `higherDirectImage f n` is the Library's `Rⁿ f_*` on all module sheaves (module
  `Langlands.AlgebraicGeometry.Modules.DerivedSections`). It is defined as Mathlib's
  right-derived functor `(Scheme.Modules.pushforward f).rightDerived n`, computed from
  injective resolutions in `X.Modules`.
- `tensorObj` is the Library's tensor product of sheaves of modules on a scheme (module
  `Langlands.AlgebraicGeometry.Modules.Tensor`): the sheafification of the sectionwise
  tensor product over the structure sheaf.
- `Scheme.Modules.pullback f` is Mathlib's pullback `f^*` of sheaves of modules.

The conclusion is that, in every degree `n`, there is an isomorphism of `𝒪_Y`-modules
`L ⊗ Rⁿ f_* M ≅ Rⁿ f_* (f^* L ⊗ M)`. Only the existence of an isomorphism is asserted; no
particular map, compatibility or naturality in `M` is part of the statement.

## Degree zero

For `n = 0` the statement is, up to the identification `R⁰ f_* ≅ f_*` given by
`DerivedSections.higherDirectImageZeroIso`, the published
`Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaStatement`, which has the same
binders `X Y f L M` and the same form, with `Scheme.Modules.pushforward f` in place of
`higherDirectImage f n`.

## Source and correspondence

The Stacks Project, Cohomology of Sheaves, Lemma 20.54.2 (tag 01E8), registered source
`stacks-flat-base-change-projection-formula-2026-11-02` (HTML snapshot of 2026-11-02, folder
SHA-256 `80cf9b0aa84270eb3e84d8a9be983aa9e38e16813713c407f723aeb49d49c8bd`; file
`tag-01E8-lemma-20.54.2-projection-formula.html`, SHA-256
`1ab125adf1132df598a2a409c98616e1e3457abb7f2f2e62c1169f9a630e8e24`). The lemma: let `f : X → Y` be a morphism
of ringed spaces, `F` an `𝒪_X`-module and `E` an `𝒪_Y`-module that is finite locally free.
Then there exist isomorphisms `E ⊗_{𝒪_Y} R^q f_* F → R^q f_*(f^* E ⊗_{𝒪_X} F)` for all
`q ≥ 0`; in fact there is such an isomorphism `E ⊗_{𝒪_Y} Rf_* F → Rf_*(f^* E ⊗_{𝒪_X} F)` in
`D⁺(Y)` that is functorial in `F`.

Correspondence:

- The source's `E` is `L.obj`. The Lean statement treats only a locally free module of rank
  one, a special case of a finite locally free module.
- The source's morphism of ringed spaces is the morphism of schemes `f`, its `F` is `M`, and
  its `q` is `n`. The source's tensor products and pullback are `tensorObj` and
  `Scheme.Modules.pullback f`, and its `R^q f_*` is `higherDirectImage f n`.
- The Lean statement keeps the first conclusion, the existence of an isomorphism in each
  degree. It omits the isomorphism in `D⁺(Y)` and its functoriality in `F`.

Comments: the tag page in the registered snapshot shows "Comments (0)", so no comment
changes the statement.

## Role

Prerequisite of task `fc8e4732-8e1b-497e-adb1-c27ee538f442` (proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`), through the
dual-side interface `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`
(statement task `2590f5a1-e1c2-4ec1-ade7-377e97a3e12f`). There it moves a line bundle pulled
back from the parameter factor of `A ×_K A` out of the higher direct images along the
parameter projection, as in formula (10) of the proof of the Riemann–Roch theorem (9.11) in
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, printed p.132. This statement does
not import or depend on either of those Mumford statements.
