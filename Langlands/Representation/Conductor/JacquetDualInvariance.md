# Dual comparison and scaled opposite Jacquet invariance

This internal auxiliary proves the group calculation needed to turn a supplied
global comparison of dual functions into scaled opposite Jacquet invariance.
It works with the existing actual general linear groups, group automorphism,
function transform and level-fixed submodules. The analytic comparison and the
integral Jacquet invariances remain explicit inputs.

## Concrete subgroup transport

Let `d = jacquetRowDilation n q = diag(1,...,1,q)` and
`τ = inverseTranspose (n+1) F`. The first theorem proves `τ(d)=d⁻¹` by
transposing the diagonal inverse. The next theorem specializes the published
ideal-level image identity to the unit ideal: `τ(H(0))` is exactly the integral
opposite mirabolic. This uses actual integral invertibility, including entries
of the inverse, and the actual row and column conditions.

By definition, membership of `h` in the scaled opposite Jacquet group means
`d*h*d⁻¹ ∈ τ(H(0))`. Applying the involutive automorphism `τ` therefore gives

`k = d⁻¹*τ(h)*d ∈ H(0)`.

`scaledOpposite_inverseTranspose_conjugate_mem` implements this calculation.
It assumes only a field and an arbitrary subring, with no local-field,
valuation, topology or positive-rank hypothesis. In particular, the underlying
group calculation also includes `n=0`.

## Supplied global comparison

With a topological ring structure on the field,
`HasJacquetDualComparison q f f' c` is the explicit Prop-valued predicate

`dualFunction n f g = c * f'(g*d)` for every `g` in the whole group.

The dual function is the existing transform
`dualFunction n f g = f(weylLong(n+1)*τ(g))`. The predicate does not assert the
existence of `f'`, a comparison constant, an essential vector or a
contragredient-model identification. Equality merely on a Levi slice does not
satisfy this predicate without a separate extension argument.

`right_invariant_of_dualFunction` uses the published translation identity and
injectivity of the existing linear involution: invariance of the dual function
under right multiplication by `τ(h)` implies right invariance of `f` under `h`.
The argument applies to all complex functions, with no Whittaker, genericity,
smoothness or irreducibility assumption.

Suppose the comparison holds and `f'` is right `H(0)`-invariant. For a scaled
opposite element `h`, the group calculation above gives `k ∈ H(0)` and

`(g*τ(h))*d = (g*d)*k`.

The comparison at `g*τ(h)` and `g`, followed by the supplied invariance of `f'`,
thus proves invariance of the dual function under `τ(h)`. The preceding theorem
then gives the actual scaled opposite right invariance of `f` at every group
element. No cancellation of `c` is needed; `c` may be any complex number.

## Actual level conclusions

`mem_levelFixedVectors_of_dual_comparison` takes an actual representation on
an independent carrier universe, a coefficient-model vector `w` already fixed
by `H(0)`, a supplied global comparison for its function, and right `H(0)`
invariance of `f'`. At scale `q=ϖ^(-a)` for a natural `a`, the preceding argument
supplies the missing scaled opposite fixedness. The published
`mem_levelFixedVectors_of_scaled_jacquet_invariant` then gives membership in
the unchanged `levelFixedVectors` of the same coefficient-model representation.
The group rank is at least two (`0<n`); `a=0` is allowed. The uniformizer is the
existing Iwasawa uniformizing-element predicate, and the valuation integer
subring and its maximal-ideal powers are unchanged.

For an integer `m`, `right_level_toNat_invariant_of_dual_comparison` assumes a
nonzero actual standard-character Whittaker function and its global `H(0)`
invariance, as well as the global dual comparison at `q=ϖ^(-m)` and `H(0)`
invariance of `f'`. The preceding scaled opposite invariance and the published
negative-level Whittaker obstruction give `0≤m`, then right invariance at the
actual level `m.toNat`. The rank-at-most-one valuation and positive-rank
hypotheses required by that obstruction remain explicit.

## Provenance and remaining obligations

The unit has internal provenance. Its new steps use diagonal transposition,
the existing subgroup image identity, the involutive group automorphism, the
existing dual-function translation identity and injectivity, and elementary
associativity and cancellation in a group. Its level conclusions compose those
steps with the previously derived scaled-group and valuation comparisons.

The unit proves neither the global dual comparison nor the two supplied
integral invariances. It does not identify the inverse-transpose pullback with
a contragredient, construct essential vectors, compare Godement–Jacquet and
JPSS factors, identify the scale exponent with an epsilon exponent, or prove
minimality or dimension one. It is a conditional algebraic component of the
conductor argument and does not prove `EssentialConductorStatement`.
