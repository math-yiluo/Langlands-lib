# Canonical fixed-part duality proof

Worker 1149 proves the published closed proposition
`Langlands.Algebra.NonUnitalModuleDualFixedPart.FixedPartDuality`
at independent universes `uA`, `uM` and `uN`. The imported statement pair
retains Worker 1156 and Worker 6 attribution; the imported canonical scalar
and fixed-part map constructions retain Worker 1149 and Worker 1156 attribution.
No imported pair is changed.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The fixed-part isomorphism and its splitting proof are in I.4.1, printed
page 23 / one-based PDF page 29. The definition of the nondegenerate dual
is on printed page 22 / PDF page 28; the splitting is in I.3.1, printed
page 19 / PDF page 25. Original nonunital action conventions are on printed
pages 5–7 / PDF pages 11–13, and the canonical complex structures are
in I.2.1, printed page 14 / PDF page 20. These passages were read directly.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF pages 1–2. Its nearby corrections concern induction,
bidual injection, duality comparison and admissibility, and do not change
the restriction and projection-extension used here. The French 2026 edition
governs. No source-specific Renard erratum file was found in the bounded
project and current Library notes filename search.

The theorem `fixedPartDuality` has exactly the already published closed
proposition as its type. It introduces the specified complex idempotented
algebra, its original nondegenerate nonunital module, and an actual idempotent.
It selects the published canonical complex module on the original carrier,
`NonUnitalModuleCorner.complexModule` on its actual fixed subgroup, and
`NonUnitalModuleDualFixedPartMaps.rightFixedModule` on the actual nested
fixed subtype of the nondegenerate dual. These are local choices of the
prescribed structures, and introduce no further hypotheses.

Write `F_M` for the actual fixed subgroup, `R_M` for the right fixed part,
`rho_M` for published restriction, and `eta_M` for published extension.
For the first inverse equation, linear-map extensionality twice reduces
`rho_M.comp eta_M = LinearMap.id` to

```text
ell(projection e x.val) = ell(x).
```

The projection has value `e • x.val`, so the fixed-subgroup membership
equation and subtype extensionality give `projection e x.val = x`.
For the second inverse, linear-map extensionality, extensionality through
both actual subtype layers, and functional extensionality reduce
`eta_M.comp rho_M = LinearMap.id` to

```text
phi.val.val(e • m) = phi.val.val(m).
```

This is the published `rightFixedPart_fixed_apply` consequence of the
original right action. Thus both equalities hold as entire complex-linear
maps. The proof bundles these maps using `LinearEquiv.ofLinearMap`;
both its entire forward linear map and its inverse linear map are
definitionally the prescribed restriction and extension.

For an independently sized original nondegenerate module `N` and original
intertwiner `f`, the proof explicitly selects the original `fullAction` and
`dualAction` on both duals. It lets `raw` be exactly

```text
NonUnitalModuleCorner.restrict (oppositeIdempotent e)
  (NonUnitalModuleDual.pullback hA hM hN f).
```

The linear map `T` uses this actual map as its function, its existing
additivity proof, and a complex homogeneity proof by extensionality through
the two subtype layers and evaluation of the included full functional.
Complex scalars are pointwise there, and pullback is precomposition with
`f`, so the scalar equation is definitional. In particular,
`T.toAddMonoidHom = raw.toAddMonoidHom` is a definitional equality of
entire additive maps; no linearity witness is assumed.

The restriction naturality square is proved by extensionality twice:
both sides evaluate as `phi.val.val(f x.val)`. For the extension square,
extensionality through the map, both subtype layers and the included
functional reduces the equation to

```text
ell(projection e (f m)) = ell(f_e(projection e m)),
```

where `f_e` is the published `restrictLinear`. The underlying subgroup
elements agree because `f(e • m) = e • f(m)`, which is the original
intertwining law. Consequently the proof establishes both entire
complex-linear-map naturality equations in the published target.

The explicit inverse identities, prescribed equivalence maps, scalar-linear
restricted pullback and naturality are derived formulations of Renard's
splitting argument and the preservation of that splitting by original
intertwiners. The implemented proof uses those canonical formulas directly.
The final examples check the unapplied closed proof at arbitrary independent
universes and at `(0,1,2)` and `(2,1,0)`.

All original hypotheses are retained. There is no finite-dimensionality,
admissibility, nontriviality, faithful action, global algebra unit or added
unit-action law. Zero algebras, zero modules and the zero idempotent are
allowed. The original nonunital actions remain specified when the algebra
has a global unit. This proof addresses the stated complex-linear
fixed-part duality only; right-corner compatibility, comparison with
full-dual fixed parts, exactness, bidual injection, I.4.2/I.4.3 comparisons
and admissible reflexivity remain with their separate owners.
