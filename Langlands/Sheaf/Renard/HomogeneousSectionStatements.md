# Renard III.3.2: the literal alpha and beta section comparisons

These are unproved closed proposition targets for David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.2, printed p.85 / PDF p.91: the compact-section and
smooth-global-section isomorphisms, the displayed alpha and beta formulas,
and their naturality. The transitive-action paragraph and countability
hypothesis are on printed p.84 / PDF p.90. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original pages were read directly.

The declarations are in
`Langlands.Sheaf.Renard.HomogeneousSectionStatements`. They assert no proof,
assume no inverse map, and introduce no alternative section space or action.

## Hypotheses and exact existing endpoints

Both targets quantify over every actual topological group `G : Type` with
`SigmaCompactSpace G` and the explicit predicate `IsLocallyProfinite G`.
The latter retains Hausdorffness and the compact-open neighbourhood basis.
The subgroup `H` is the actual closed subgroup of `G`. Base spaces,
coefficients, original section carriers, stalks and induction carriers are
universe zero, as in the published `HomogeneousSections` interfaces.
The sigma-compactness premise retains Renard's countability at infinity;
it is not replaced by second countability or silently omitted because the
literal quotient is already available.

The base is the original `Langlands.Induction.LeftQuotient H`, with exactly
`HomogeneousSections.homogeneousAction`: `g₀ • Hg = H(g g₀⁻¹)`.
`F` ranges over every existing `SectionActions.SmoothActionSheaf` on this
base. Its compact-section representation is the entire existing
`compactRepresentation F.obj`. Its coefficient representation is the
existing `stalkRepresentation H F.obj`, on the literal ordinary stalk at
`origin H = H1`. Its smoothness is supplied by the existing original-stalk
restriction result on the locally profinite quotient; no substitute stalk
or supplied coefficient isomorphism is used.

## Compact sections

`CompactAlphaBetaStatement` requires a family of actual equivariant
complex-linear maps `beta F` from the original
`compactInduced H (stalkRepresentation H F.obj)` to the original compact
sections. Their domain is the existing `CompactFunctions`; it includes
original covariance, a uniform open right stabilizer and compact quotient
support.

For every `F`, both inverse laws are required against exactly the published
`HomogeneousSections.alphaCompact H F`. That forward map is already defined
by the original global action and original germ at the identity coset:
`alpha(s)(g) = germ_o(g • s)`. Thus the target specifies the actual forward
isomorphism, rather than asking for an arbitrary isomorphism between spaces.

The output beta family must satisfy the source's displayed formula on
original germs at every point `g • o = H g⁻¹`:

```text
germ_(g • o)(beta(f)) = gamma_g(f(g⁻¹)).
```

The right-hand side is literally `Godement.stalkPull` with label `g⁻¹`,
from the original stalk at `o` to the original stalk at `g • o`; its point
equation is `g⁻¹ • (g • o)=o`. The argument is the original induced
function's value at `g⁻¹`. The beta output is an actual original compact
section, so it must meet the sheaf descent, local representability and
compact-support obligations. They are conclusions of the target, not
assumed certificates.

A final quantified equation requires naturality of beta for every original
equivariant sheaf morphism. On compact sections it uses exactly
`CompactSections.map`; on coefficient stalks it uses the existing
`fixedStalkFunctor` map; on induction it uses exactly `compactInducedMap`.
The forward alpha naturality is already published. Together with both
inverse laws this states the natural section isomorphism in the source.

## The smooth part of global sections

`SmoothGlobalAlphaBetaStatement` has the same original group, base, sheaf
and stalk data. Its beta family goes from the original `smoothInduced` to
`Langlands.smoothPart (globalRepresentation F.obj)`, whose carrier is the
existing `smoothVectors` of all original global sections. The inverse laws
are against exactly `alphaSmoothGlobal H F.obj`. The germ formula is the
same displayed formula, using the actual underlying global section of the
smooth-vector output and the original smooth induced function value.

Naturality uses the original global-section intertwiner and its existing
`Langlands.smoothMap`, together with the original induced stalk map and
`smoothInducedMap`. Neither the whole global-section representation nor
its compact-support subspace is substituted for its actual smooth part.

`SectionComparisonStatement` is the conjunction of these two source
assertions. It supplies a single inspected proposition entry while leaving
the two full declaration names available for focused proof tasks. The
induction-sheaf fibre identification, singleton category equivalence,
homogeneous categorical equivalence, arbitrary transitive-space comparison
and the III.3.1 coinvariant assertions are separate targets.
