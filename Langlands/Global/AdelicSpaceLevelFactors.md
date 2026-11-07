# The factors of an adelic level

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). For a separated algebraic space `X` of
finite type over a ring `C`, it collects the topological properties of the two kinds of factors
of the adelic-level topology.

## Declarations

Namespace `Langlands.Global.AdelicSpaceLevelFactors`; `K` is a nontrivially normed field with a
`C`-algebra structure.

- `locallyOfFiniteTypeOverBase`, `isQuasiSeparatedLocallyFiniteType`, `t2Space_etale`: the base
  change `X_K` is quasi-separated and locally of finite type. Over a henselian `K`, its rational
  points are Hausdorff for the étale-chart topology (`t2Space_etaleChartTopology`, Proposition
  5.4).

Field factors, along a bijective `φ : R →ₐ[C] K`:

- `t2Space_field`: Hausdorff over a henselian valued field.
- `locallyCompactSpace_field`: locally compact over a locally compact henselian valued field
  (`locallyCompactSpace_etaleChartTopology`).

Integer factors, along the inclusion of a subring `O ⊆ K`:

- `injective_integer`: `X(O) → X_K(K)` is injective for separated `X` (`changeRing_injective`).
- `t2Space_integer`: Hausdorff over a henselian valued field.
- `compactSpace_integer`: compact when `O` is the closed unit ball, `O` is henselian and `K` is
  locally compact (Corollary 5.7, quasi-compactness).
- `locallyCompactSpace_integer`: locally compact, being compact and Hausdorff.
- `isOpen_range_integer`: the image of `X(O)` in `X_K(K)` is open (Corollary 5.7, openness).
