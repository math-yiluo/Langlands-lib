# Relative dual geometry from field smoothness, flatness and local finite presentation

This module states a reduction of
`Langlands.AbelianScheme.RelativeDualSchemeGeometryStatement` to three
published proposition definitions and proves it. It also proves one auxiliary
smoothness lemma over an arbitrary base. It proves none of the three inputs
and does not establish dual existence: `HasDualScheme A` stays a hypothesis
throughout.

Unlike the published
`RelativeDualSchemeGeometryStatement.of_flat_finitePresentation_proper`
(module `RelativeDualSchemeGeometryReduction`), this reduction needs neither
`RelativeDualSchemeProperStatement` nor full field geometry. Properness now
comes from the published theorem `relativeDualSchemeValuativeExistence`, and
field smoothness is enough on the fibres.

## The reduction statement

`Langlands.AbelianScheme.RelativeDualSchemeGeometryFlatReductionStatement.{u}`
is the proposition

```
FieldDualSchemeSmoothStatement.{u} →
  RelativeDualSchemeFlatStatement.{u} →
    RelativeDualSchemeFinitePresentationStatement.{u} →
      RelativeDualSchemeGeometryStatement.{u}
```

All four propositions are published Library statements, used unchanged:

- `FieldDualSchemeSmoothStatement`: for every field `k : Type u`, every
  abelian scheme `A` over `Spec k` and every `hA : HasDualScheme A`, the
  structure morphism of `dualScheme A hA` is smooth;
- `RelativeDualSchemeFlatStatement`: for every `S : Scheme.{u}` with
  `[QuasiSeparatedSpace S]`, every abelian scheme `A` over `S` and every
  `hA : HasDualScheme A`, the structure morphism of `dualScheme A hA` is flat;
- `RelativeDualSchemeFinitePresentationStatement`: the same quantification,
  with conclusion that this morphism is locally of finite presentation;
- `RelativeDualSchemeGeometryStatement`: the same quantification, with
  conclusion `DualSchemeGeometry A hA`, that this morphism is smooth, proper
  and geometrically connected.

The quasi-separatedness hypothesis on the base is that of the target and of
the two relative inputs; no noetherian, reducedness or projectivity hypothesis
is added.

## Smoothness over an arbitrary base

`dualScheme_smooth_of_flat_of_locallyOfFinitePresentation` takes a proof
`fieldSmooth : FieldDualSchemeSmoothStatement.{u}`, any scheme
`S : Scheme.{u}` (not necessarily quasi-separated), an abelian scheme `A` over
`S`, a proof `hA : HasDualScheme A`, and instances that the structure morphism
of `dualScheme A hA` is flat and locally of finite presentation. It proves
that this morphism is smooth.

Proof. Mathlib's `Smooth.of_smooth_fiberToSpecResidueField` reduces
smoothness of a flat morphism locally of finite presentation to smoothness of
its fibre morphism over every residue field. The published
`FieldDualSchemeGeometryStatement.of_smooth` turns `fieldSmooth` into
`FieldDualSchemeGeometryStatement.{u}`. The published lemma
`dualScheme_fiberToSpecResidueField` then gives, for each point `s`, that
`(dualScheme A hA).hom.fiberToSpecResidueField s` is smooth (its first
component). That lemma identifies the fibre with the chosen dual of the base
change of `A` to `Spec κ(s)` through `dualSchemeResidueFieldIso`, which rests
on the published universal base-change theorem.

## Proof of the reduction

`relativeDualSchemeGeometryFlatReduction` proves
`RelativeDualSchemeGeometryFlatReductionStatement.{u}`. Fix the three inputs,
a quasi-separated base `S`, an abelian scheme `A` over `S` and
`hA : HasDualScheme A`.

1. The flatness and finite-presentation inputs, applied to `S`, `A` and `hA`,
   give `Flat` and `LocallyOfFinitePresentation` instances for the structure
   morphism of `dualScheme A hA`.
2. The lemma above gives the `Smooth` instance.
3. The published `dualSchemeGeometry_of_smooth`, applied to the published
   theorem `relativeDualSchemeValuativeExistence`, gives
   `DualSchemeGeometry A hA` from that `Smooth` instance and the
   quasi-separatedness of `S`. Inside that lemma, properness is the published
   `dualScheme_isProper_of_smooth_of_valuativeExistence` and geometric
   connectedness is the published unconditional
   `dualScheme_geometricallyConnected` (both in `DualSchemeGeometryAssembly`).

## Provenance and source scope

This is an internal derived reduction. It composes accepted Library
constructions and Mathlib's results about scheme morphisms and invokes no new
literature theorem. The mathematical scope of the final target remains
Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*
(revised March 14, 2021), Theorem 1.3.2.3, printed p.74 (PDF p.102), as
documented in `RelativeDualSchemeGeometryStatement.md`: arbitrary
quasi-separated bases. That source scope does not discharge any of the three
proposition inputs. Separate proof tasks own them: field smoothness (task
`4ef972f8-8ae6-4f1a-b440-857530de2ca6`), relative flatness (task
`b6a7f057-6bd6-4d77-ab24-9b79698666f8`) and relative local finite
presentation (task `209d4877-85e0-4ba7-b1d3-e6e393df82d2`). No new axiom is
introduced, and the target, `HasDualScheme`, `dualScheme` and their
dependency closure are unchanged.
