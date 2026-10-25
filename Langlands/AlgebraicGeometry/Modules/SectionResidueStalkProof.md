# Actual residue nonvanishing detects stalk frames of line-bundle sections

The theorem `Langlands.SchemeModule.lineBundleResidueStalkCriterion` proves
the published proposition `LineBundleResidueStalkCriterion.{u}`. For every
scheme `X : Scheme.{u}`, actual locally free rank-one module
`L : LineBundle X`, global section `s : GlobalSections L.obj`, and point
`x : X`, it gives

```text
NonvanishingAt L.obj s x ↔ IsStalkFrame L.obj s x.
```

The left side is the existing actual residue section: pull back the section
morphism along `X.fromSpecResidueField x`, precompose with
`pullbackUnitIso.inv`, and evaluate at one. The right side says that
`sectionHom L.obj s` induces an isomorphism on the underlying abelian-group
stalk at `x`. The theorem preserves arbitrary universe and arbitrary-base
scope, with no additional compatibility or local-chart assumption.

The proof chooses a neighborhood `U` of `x` and an isomorphism
`e : L.obj.restrict U.ι ≅ structureModule U.toScheme` from `L.property x`.
Writing `y : U.toScheme` for the same point, it defines the endomorphism

```text
ψ = (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (sectionHom L.obj s) ≫ e.hom.
```

Applying the underlying-presheaf and stalk functors to this composite,
functoriality and cancellation of the two mapped isomorphisms identify
invertibility of the stalk map of `ψ` with invertibility of the restricted
section map. The published `isIso_stalk_restrict_iff` then identifies this
condition with `IsStalkFrame L.obj s x`.

The published `residueLocalChartCriterion` identifies the actual residue
nonvanishing at `x` with nonzero residue of `ψ.app ⊤ 1` at `y`. Its imported
proof establishes the transport through actual residue pullback and open
restriction using the residue-point square, the restriction/pullback
comparison, and the pullback-unit adjunction. Thus the present proof uses a
proved comparison rather than introducing a compatibility premise.
The published `unitEnd_stalkIso_iff_residue_ne_zero`, applied to `ψ` and
`y`, identifies that scalar nonvanishing with invertibility of its stalk
map. Composing these equivalences with the stalk identification above
proves the target.

This is an internal derived proof of the Library's residue/stalk interface.
It imports the unchanged `SectionResidueStatements`,
`ResidueLocalChartProof`, and `UnitEndResidueStalkProof` modules by Lean
name. The local chart and stalk cancellation argument adapts Worker 311's
published `LineBundleFrameOpen`; Worker 149 assembled this proof, with
Worker 311 credited for that argument. The imported actual residue-chart
proof is by Worker 354. This module proves the pointwise residue/stalk
criterion; the full open-locus equality is a separate statement.
