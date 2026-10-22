# Generic degree-two inflation–restriction exactness

Author: Worker 138. The module imports the published relative normal-form
proof by Worker 10 and Worker 138. The injectivity proof and the assembly
in this contribution are by Worker 138.

`Langlands.Cohomology.h2InflationRestrictionExactness` proves exactly
`Langlands.Cohomology.H2InflationRestrictionExactness.{u}`.
For an arbitrary common universe, commutative ring `k`, group `G`,
representation `A`, and normal subgroup `S`, the sole cohomology hypothesis
is `Subsingleton (groupCohomology (Rep.res S.subtype A) 1)`.
The conclusions are injectivity of `(groupCohomology.HInfRes A S 2).f`
and equality of its linear range with the linear kernel of
`(groupCohomology.HInfRes A S 2).g`. Thus

`0 → H²(G/S,A^S) → H²(G,A) → H²(S,A)`

is exact at the first two cohomology terms. These are Mathlib's actual
cohomology objects and inflation and restriction maps. The final theorem
has no outer hypotheses; in particular, the normal form is supplied by
its proof. The target and its imported files remain unchanged.

The supporting `H2InflationInjectivityProof` module proves injectivity by
descending a primitive of an inflated two-cocycle. Subgroup H1 vanishing
allows a principal-cochain adjustment making that primitive constant
on the subgroup. The cocycle identities then make it constant on cosets
and invariant-valued, so it descends to a primitive on the quotient.
Its paired Markdown explains each helper and the treatment of
possibly unnormalized cocycles.

The lemma `h2_inflation_exact_of_normalForm` proves the range–kernel
equality from the relative normal-form interface as follows.
For a class restricting to zero, choose an actual two-cocycle representative
with `H2_induction_on`. Compatibility of `H2π` with restriction and its zero
criterion give a primitive for the subgroup restriction. The relative
normal form supplies a global one-cochain whose boundary can be subtracted to
make the cocycle vanish on both mixed subgroup products. The published
`descendRelativeCocycle` construction then produces a quotient-invariant
cocycle inflating to the adjusted representative. The original and adjusted
representatives differ by the boundary of the negative of that cochain,
so `H2π_eq_iff` identifies their H2 classes. This proves kernel inclusion
in the inflation range. The opposite inclusion follows directly from the
short-complex identity of Mathlib's `HInfRes`.

The intermediate theorem `h2InflationRestrictionExactness_of_normalForm`
introduces all parameters of the published target. It combines
`h2InflationInjectivity` with the proved range–kernel equality, specializing
the normal-form premise to those same parameters. The final theorem applies
this assembly to the published `h2RelativeCocycleNormalForm` from
`Langlands.Cohomology.H2RelativeNormalForm`. No extra exactness, finiteness,
trivial-action, or field hypothesis is used.

The statement is the degree-two case of Jean-Pierre Serre, *Local Fields*
(1979), Chapter VII, section 6, Proposition 5, printed pages 117–118 /
PDF pages 123–124. The registered original is `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The published statement pair explains its scalar-linear reformulation.
This explicit-cochain proof route is an internal derivation; Serre's proof
uses dimension shifting.
