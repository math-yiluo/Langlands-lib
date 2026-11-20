# Rational and adelic points of subgroups in the constant-term formula

Module `Langlands.Global.EisensteinConstantTerm.Points`. It proves facts on points of
subgroups of `G`, as subgroups of `G(𝔸)`. Here `rationalImage F j` is the image of `H(F)`
under `j : H → G` (defined in `AdelicEisensteinConstantTermStatement`). All results are in
namespace `Langlands.Global.AdelicGroupPoints`.

## Functoriality

- `map_rational`, `map_rational_affinePointsTarget`: `j(rational y) = rational(j y)` and
  `j(rational(k y)) = (k ≫ j)(rational y)`. Both come from the Library's `rational_naturality`.
- `rationalImage_le_rationalSubgroup`: `H(F) ⊆ G(F)`.
- `rationalImage_comp_le`: `(k ≫ j)(F) ⊆ j(F)`. The special case
  `rationalImage_comp_le_of_radical` gives `V(F) ⊆ Q(F)`.
- `rationalImage_eq_map`: `rationalImage F j` is the image of the principal subgroup of `H(𝔸)`.
  This is the form used in `parabolicRationalSubgroup`.
- `mem_rationalSubgroup_range_iff`: an adelic point `v` of the subgroup functor `range j` lies
  in its principal subgroup `AdelicSubgroupPoints.rationalSubgroup` exactly when `v`, as a point
  of `G(𝔸)`, lies in `rationalImage F j`.
- `rationalImage_le_adelicPoints`: `rationalImage F j` lies in the adelic points of `range j`.

## Normality

For `q : Q → G` and `iV : V → Q` with `range iV` normal (a field of `IsUnipotentRadical`):

- `conj_mem_adelicPoints_range`: `q(x) v q(x)⁻¹ ∈ V(𝔸)` for `x ∈ Q(𝔸)` and `v ∈ V(𝔸)`.
- `conj_mem_rationalImage`: `x v x⁻¹ ∈ V(F)` for `x ∈ Q(F)` and `v ∈ V(F)`.

Both evaluate normality of the subgroup functor on the test schemes `Spec 𝔸` and `Spec F`.

## Levi decomposition on rational points

- `rationalImage_le_parabolicQuotientSubgroup`: assume `l : M → P` is a rational Levi subgroup
  (`IsRationalLeviSubgroup`) and `iU` is a geometric unipotent radical of `P`. Then
  `P(F) ⊆ U(𝔸) M(F)`, where the right side is the Library's `parabolicQuotientSubgroup`.
  - `IsRationalLeviSubgroup` supplies a geometric unipotent radical `r₀ : U₀ → P` such that the
    multiplication `M × U₀ → P` is an isomorphism. A rational point `y` of `P` is therefore
    `l(m) r₀(u)` with `m ∈ M(F)` and `u ∈ U₀(F)`.
  - By `IsUnipotentRadical.range_eq` the ranges of `r₀` and `iU` agree, so `r₀(u) = iU(u')`.
  - Mapping to `G(𝔸)` gives an element of `M(F) U(F) ⊆ U(𝔸) M(F)`.

Consequently every function left invariant under `U(𝔸)M(F)`, such as an automorphic form in
the target statement, is left invariant under `P(F)`.

## Provenance

These are standard facts (BL §6.7, journal pp. 206–207 use `P = M_P U_P`). The formalization
is internal.
