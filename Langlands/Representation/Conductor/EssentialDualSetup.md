# Setup for the dual essential vector

This internal auxiliary collects the algebraic facts that let the dual
essential vector enter the conductor argument. It shows that the
inverse-transpose pullback of a generic representation is generic for the
reversed character `ψ.scale (-1)`, and that the dual functional is a nonzero
functional for that character. Jacquet's normalizations carry over to
`ψ.scale (-1)`. A dual comparison of the shape used by Jacquet,
Piatetski-Shapiro and Shalika, with right translate `diag(ϖ^m, ..., ϖ^m, 1)`,
reduces to the existing `HasJacquetDualComparison` for a central translate,
and hence gives level-fixedness. The analytic comparison and the integral
invariances remain explicit hypotheses.

## Dual genericity and the dual functional

Let `F` be a field with a topology making it a topological ring. Let `ψ` be a
unitary additive character, and let `π` be a complex representation of the
actual `GeneralLinear (n + 1) F` on a carrier `V : Type uV`, whose universe is
independent of that of `F`. The pullback `inverseTransposePullback π` is the
published composition of `π` with the inverse-transpose automorphism
`g ↦ (gᵀ)⁻¹`. It is not defined to be, or identified with, a contragredient.

The published `dualFunctional ψ π ℓ` is `ℓ ∘ π(weylLong)`, which is equivariant
for the inverse standard character of `ψ`. The published
`standardCharacter_scale_neg_one` identifies the standard character of
`ψ.scale (-1)` (the character `x ↦ ψ(-x)`) with that inverse character.
`scaledDualFunctional ψ π ℓ` transports `dualFunctional ψ π ℓ` along this
equality using the published `functionalsCongr`. It is the same linear form
(`scaledDualFunctional_val`, by definition), viewed as an element of
`glFunctionals (ψ.scale (-1)) n (inverseTransposePullback π)`.
`scaledDualFunctional_ne_zero` proves it is nonzero whenever `ℓ` is nonzero,
using the published `dualFunctional_nonzero`.

`isGeneric_inverseTransposePullback` proves that `IsGeneric ψ n π` implies
`IsGeneric (ψ.scale (-1)) n (inverseTransposePullback π)`. The three clauses of
the published `IsGeneric` are transported as follows.
- Irreducibility uses `isIrreducible_comp_continuousMulEquiv_iff`.
- Admissibility (which includes smoothness) uses
  `isAdmissible_comp_continuousMulEquiv`. Both are applied to the continuous
  inverse-transpose group equivalence `inverseTransposeContinuous`.
- The nonzero functional is `scaledDualFunctional` of the given one.

No multiplicity-one statement is assumed or produced.

## Normalizations for the reversed character

Here `F` additionally carries `ValuativeRel F` and `IsNonarchimedeanLocalField F`.
The field may have any characteristic.
`hasIntegerConductor_scale_neg_one` proves that the published conductor
condition `HasIntegerConductor` passes from `ψ` to `ψ.scale (-1)`:
- triviality on the valuation integers follows because `-x` is integral for
  integral `x`;
- for maximality, the hypothesis on `ψ.scale (-1)`, applied to the integral
  element `-y`, gives `ψ(x*y) = 1` for every integral `y`, because
  `(ψ.scale (-1))(x*(-y)) = ψ(x*y)`; the maximality clause for `ψ` then makes
  `x` integral.

`IsJacquetNormalization.scaleNegOne` keeps the residue cardinality `q`, the
uniformizer `ϖ`, the absolute value `abv`, the quotient measure `μ` and both
Borel conditions unchanged. It replaces only the conductor field. None of
these other fields mentions `ψ`.

## The JPSS translate and the Jacquet dual comparison

Write the larger group as `GeneralLinear ((n + 1) + 1) F`. For `a : Fˣ`, the
element `rankInclusion 1 (scalar a)` is the published block inclusion
`diag(a I_(n+1), 1)`, that is `diag(a, ..., a, 1)`.
`rankInclusion_scalar_eq` proves

`rankInclusion 1 (scalar a) = jacquetRowDilation (n + 1) a⁻¹ * scalar a`,

where `jacquetRowDilation (n + 1) a⁻¹ = diag(1, ..., 1, a⁻¹)` is the published
dilation. The proof compares the entries of both matrices, with the last row
and column treated separately. It needs only a field.

Now let `F` also be a topological ring. Suppose that for every `g` in the whole
group,

`dualFunction (n + 1) f g = C * f'(g * rankInclusion 1 (scalar (ϖ^m)))`

with `m : ℤ`. Then `hasJacquetDualComparison_of_rankInclusion_scalar` proves
`HasJacquetDualComparison (ϖ^(-m)) f f'' C`, with
`f''(g) = f'(g * scalar (ϖ^m))`. This follows from the identity above, the
equality `(ϖ^m)⁻¹ = ϖ^(-m)` and associativity. The constant `C` is arbitrary.
`right_invariant_central_translate` proves that right invariance of `f'` under
any subgroup `H` passes to `f''`, because the scalar matrix commutes with every
group element. No central character of any representation is used.

`mem_levelFixedVectors_of_rankInclusion_dual_comparison` takes the following:
- an actual representation `π` of `GeneralLinear ((n + 1) + 1) F` on a carrier
  of independent universe;
- `ℓ : glFunctionals ψ (n + 1) π` and a coefficient-model vector `w`;
- a uniformizer `ϖ` (the published `Iwasawa.IsUniformizingElement`) and a
  natural number `m`.

It assumes three things:
- the displayed comparison for `f = w`, with an arbitrary function `f'` and
  constant `C`;
- that `w` is fixed by the integral row mirabolic `H(0)`, i.e.
  `fieldJacquetMirabolic` for the valuation integers;
- that `f'` is right `H(0)`-invariant.

It concludes that `w` lies in the unchanged
`levelFixedVectors (modelRepresentation π ℓ) m`. The proof applies the
previous two results and then the previously derived
`mem_levelFixedVectors_of_dual_comparison` at scale `ϖ^(-m)`. The case `m = 0`
is allowed. Since the group has rank at least two, the positive-rank
hypothesis of that theorem holds automatically.

## Provenance and remaining obligations

The unit has internal provenance. Its steps use existing transport lemmas for
irreducibility and admissibility, the published dual functional and character
identity, elementary properties of the valuation integers, an entrywise matrix
identity, centrality of scalar matrices, and the previously derived
`JacquetDualInvariance` result. The form of the translate follows the dual
comparison in H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Conducteur des représentations du groupe linéaire*, Math. Ann. 256 (1981),
§5, display (5.3) on printed page 213. There the translate is
`diag(ϖ^m, ..., ϖ^m, 1)` and `m` is the epsilon exponent. No result of that
source is asserted here.

The unit does not prove the analytic dual comparison. It does not prove the
integral `H(0)` invariance of either function, or identify the integer `m` with
an epsilon exponent. It does not identify the inverse-transpose pullback with
the contragredient, construct or characterize essential vectors, compare
factors, or prove minimality or dimension one. It is a conditional component
of the conductor argument and does not prove `EssentialConductorStatement`.

`scaledDualFunctional` uses the existing `Langlands.RankinSelberg.firstDualFunctional` construction, with the same arguments, defining value and inverse-character convention.
