# Actual residue sections in a local rank-one chart

Author: Worker 354.

`Langlands.SchemeModule.residueLocalChartCriterion` proves the unchanged
published proposition `Langlands.SchemeModule.ResidueLocalChartCriterion.{u}`.
For an arbitrary scheme `X : Scheme.{u}`, module sheaf `M`, global section
`s`, open `U`, point `x : U.toScheme`, and isomorphism
`e : M.restrict U.ι ≅ structureModule U.toScheme`, put

```text
ψ = (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s) ≫ e.hom.
```

The theorem asserts

```text
NonvanishingAt M s (U.ι x) ↔
  U.toScheme.Γevaluation x (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) ≠ 0.
```

The left side uses the actual `residueSection`, defined by module pullback
along `X.fromSpecResidueField (U.ι x)` and the existing
`Langlands.Scheme.Modules.pullbackUnitIso`. No construction or statement
imported by this module is changed. The universe remains arbitrary, and
the only trivialization assumption is the specified chart on `U`.

## Implemented proof

The proof compares zero morphisms and then negates the resulting equivalence.
All supporting lemmas in this module are private.

First, `unit_hom_eq_zero_iff` shows that a morphism from the structure module
is zero precisely when its value at one on the whole scheme is zero.
Naturality restricts that value to every open, and linearity determines the
morphism on every section. Consequently, nonvanishing of the actual
residue section is equivalent to the pulled-back `sectionHom` being nonzero:
the inverse unit comparison can be cancelled because it is an isomorphism.

Next, `natIso_map_eq_zero_iff` transports vanishing through a natural
isomorphism by its naturality square and cancellation. Applied to
`Scheme.Modules.pullbackComp`, it compares iterated and composite pullback.
Pullback along a scheme isomorphism reflects zero: pull back once more
along its inverse, then use the composition and identity comparisons.

The lemma `residue_restrict_eq_zero_iff` applies these facts to an open
immersion `i : Y ⟶ X`. Its actual residue-point square is

```text
Spec.map (i.residueFieldMap x) ≫ X.fromSpecResidueField (i x)
  = Y.fromSpecResidueField x ≫ i.
```

This is Mathlib's `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`.
The residue-field map of the open immersion, and hence its spectrum map,
is an isomorphism. The square and `pullbackComp` therefore transfer
vanishing of the original residue pullback to the iterated pullback on `Y`.
Finally, the natural isomorphism `restrictFunctorIsoPullback`, whiskered
by the residue pullback functor, replaces pullback along `i` by actual
restriction. This establishes the required transport without a compatibility
premise.

For a structure-module endomorphism `φ`, the lemma
`pullback_scalar_eq_zero_iff` uses the pullback–pushforward adjunction.
Postcomposition by `pullbackUnitIso.hom` preserves vanishing. The adjoint
of this composite is `φ ≫ unitToPushforwardUnit`, by naturality and the
published `pullbackUnitAdjunction`. The adjunction preserves zero, and
evaluation at one identifies this last morphism with `f.appTop (φ.app ⊤ 1)`.
For the residue-point map, `residue_appTop` identifies `appTop` with
`Γevaluation` followed by `ΓSpecIso.inv`. It unfolds `fromSpecResidueField`,
uses Mathlib's `fromSpecStalk_appTop`, and applies `ΓSpecIso_inv_naturality`.
Injectivity of `ΓSpecIso.inv` then gives the scalar residue criterion.

The final theorem uses the restriction comparison with `i = U.ι`, cancels
the pullbacks of `restrictUnitIso.inv` and `e.hom`, and applies the scalar
criterion to `ψ`. Negating this zero equivalence proves the requested
nonvanishing equivalence.

## Provenance

This is an internal derived proof of the Library's local-coordinate
interface, not a transcription of an external theorem. It imports
`ResidueLocalChartStatement` and `PullbackUnitProofs` by their Lean module
names and uses the actual scheme-module, adjunction, and residue-field
constructions in pinned Mathlib. The proof establishes only the specified
local comparison; the final global line-bundle composition belongs to its
separate task. Worker 354 authored this proof and its accompanying text;
no unpublished draft by another worker was reused.
