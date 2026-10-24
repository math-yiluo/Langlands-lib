# Residue-field nonvanishing in a local rank-one chart

`Langlands.SchemeModule.ResidueLocalChartCriterion` is a proposition for
every scheme `X : Scheme.{u}`, module sheaf `M : X.Modules`, global section
`s : GlobalSections M`, open `U : X.Opens`, point `x : U.toScheme`, and
isomorphism `e : M.restrict U.ι ≅ structureModule U.toScheme`.
The isomorphism is a rank-one trivialization on this open; no global
local-freeness assumption on `M` is needed.

The let-bound endomorphism `ψ` of the structure module on `U.toScheme` is
the composite

```text
(Scheme.Modules.restrictUnitIso U.ι).inv ≫
  (Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s) ≫ e.hom.
```

Thus `ψ` first identifies the structure module with the restriction of
the structure module on `X`, then applies the restricted section
morphism, and finally uses the chosen trivialization. Its value at one
is a global function on `U.toScheme`. The proposition states exactly

```text
NonvanishingAt M s (U.ι x) ↔
  U.toScheme.Γevaluation x (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) ≠ 0.
```

On the left, `NonvanishingAt` is the unchanged definition from
`SectionResidue`: the section obtained by actual module pullback along
`X.fromSpecResidueField (U.ι x)` is nonzero. That section is constructed
using `Langlands.Scheme.Modules.pullbackUnitIso.inv`, the pullback of
`sectionHom M s`, and evaluation at one. On the right, Mathlib's
`Γevaluation` takes the local function to its value in the residue field
of `x` on `U.toScheme`. The assertion compares nonvanishing; it does not
identify elements of the two different section spaces by an unprovided
equality.

This is an internal derived local-coordinate interface built from
`SectionResidue`, `SectionLocus`, and Mathlib's actual scheme-module
restriction and residue-field constructions. It isolates the transport
of the actual pulled-back section needed for the published statement
`Langlands.SchemeModule.LineBundleResidueStalkCriterion` in
`SectionResidueStatements`. Together with the separate scalar criterion
`UnitEndResidueStalkCriterion`, it supplies the local comparisons needed
in a proof of that line-bundle statement. This categorical formula is not
claimed to be a literal statement from the literature.

The declaration only states the comparison; its proof is a separate
obligation. In particular, it neither assumes a pullback-compatibility
condition nor replaces the residue section by abstract fibre data or a
stalk-frame hypothesis. The universe `u` is arbitrary, and no affine,
quasi-compactness, or separation restriction is imposed. Existing Library
declarations are unchanged.
