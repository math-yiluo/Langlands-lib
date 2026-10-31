# Local open-restriction criterion for support of algebraic distributions

`Langlands.HarmonicAnalysis.Distribution.openRestrictionLocality.{u}` proves
the published proposition
`Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement.{u}`
from [OpenRestrictionLocalityStatement](OpenRestrictionLocalityStatement.md).
The theorem has exactly that proposition as its type, at an arbitrary universe
`u`.

## Scope and conventions

The space `X` is Hausdorff, locally compact and totally disconnected. The
subset `Z` is arbitrary: it need not be closed or nonempty. The Library's
`Distribution X` is the entire complex algebraic dual of the actual
Schwartz–Bruhat space `SchwartzBruhat X`; no continuity of `D` is used. The
hypothesis is applied pointwise as published: each point `x ∉ Z` has an open
neighbourhood `U` whose actual open restriction `restrictOpen hU D`, the dual
of extension by zero `SchwartzBruhat.extendZero hU`, is zero. The conclusion
is membership in the existing pointwise-annihilator submodule
`supportedOn Z`: `D f = 0` for every test function `f` with `f z = 0` for all
`z ∈ Z`. No countability, global open cover, compactness of `X`, group action
or measure enters.

## Implemented proof

The private linear map `cutoff hV`, for a clopen set `V`, multiplies a test
function by the characteristic function `LocallyConstant.charFn ℂ hV`. The
product is locally constant and has compact support because the original
function does; `V` itself need not be compact. Its evaluation lemma
`cutoff_apply` gives the original value on `V` and zero elsewhere.

The private lemma `kill_of_restrictOpen_zero` shows that a distribution with
`restrictOpen hU D = 0` kills every test function `f` vanishing outside the
open set `U`. The published `FiniteOrbitVanishingProof.exists_extension_eq`,
applied to `SchwartzBruhat.extendZero hU` with its evaluation laws
`extendZero_apply_subtype` and `extendZero_apply_of_not_mem`, writes `f` as an
actual extension by zero `extendZero hU φ`. Then `D f` is the value of the zero
restriction at `φ`. Consequently (`kill_cutoff`) if a clopen `V` lies inside
such a `U`, then `D` kills `cutoff hV g` for every test function `g`, since
this cutoff vanishes outside `U`.

For the main theorem, fix a test function `f` vanishing on `Z`. Every point
`x` of its support lies outside `Z`, so the hypothesis gives an open
zero-restriction neighbourhood `U` of `x`. Mathlib's
`loc_compact_Haus_tot_disc_of_zero_dim` turns the space's clopen
neighbourhood basis into a clopen `V x` with `x ∈ V x ⊆ U`, and `D` kills
every cutoff by `V x`. The support of a test function is compact
(`Hecke.TestFunction.isCompact_support`), so finitely many of these sets,
indexed by a finset `s` of support points, cover it.

Induction on finsets `t` proves that `D` kills the cutoff of `f` by the clopen
union `⋃ x ∈ t, V x`. The empty union gives the zero function. For an inserted
point `x`, the pointwise identity

```text
cutoff (V x ∪ W) f = cutoff (V x) f + cutoff W f - cutoff (V x) (cutoff W f)
```

holds, where `W` is the previous union. The first and last terms are cutoffs
by `V x` and are killed by `D`; the middle term is killed by induction. Only
finite additivity of `D` is used, and no infinite sum or integral is
exchanged with the distribution. Because the final union covers the support
of `f`, its cutoff of `f` equals `f`, so `D f = 0`. A function with empty
support needs no separate case.

## Provenance

This is an internal deduction from the published Schwartz–Bruhat subspace
maps and the full algebraic dual; the paired statement Markdown explains its
analogy with Shalika's Proposition 1.14 without identifying the two
formulations. Worker 634 prepared this argument as the private
`OpenRestrictionLocalityCore.locality` for the Design form of the same
proposition. Its extension characterization reuses Worker 33's published
`FiniteOrbitVanishingProof.exists_extension_eq`, and its characteristic
cutoff and finite-union compact-cover argument adapt Worker 121's published
`LocalizationProof`. This module ports that proof to the published statement;
it uses neither the finite-orbit theorem itself nor any covariance or
global-invariance result.
