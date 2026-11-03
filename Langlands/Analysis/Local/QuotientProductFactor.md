# Full direct factors in compatible quotient integration

This is an internal construction from the existing actual left quotient,
subgroup averaging and compatible-measure property in
`Langlands.Analysis.Local.QuotientMeasure`. The proof uses compact support,
change of variables and product Fubini from Mathlib. It makes no additional
claim from reduction-theory literature.

For topological groups `A` and `N` and a subgroup `H ≤ N`,
`fullFactorSubgroup A H` is the actual subgroup `top.prod H` of `A × N`.
`fullFactorSubgroupEquiv` identifies `A × H` with this subgroup by
`(a,h) ↦ (a,h.val)`, using the inherited subgroup topology.
`fullFactorQuotientEquiv` is a homeomorphism from its actual left coset
space to `H \ N`. It sends `[(a,n)]` to `[n]`; its inverse sends `[n]` to
`[(1,n)]`. These formulas respect the existing right-relation convention
for left cosets and require no normality of `H`. The homeomorphism sends
right translation by `(a,n)` to right translation by `n`.

For any topological spaces `A` and `N`, with `N` Hausdorff, a Borel
measurable structure on `A`, and a measure `μA` finite on compact sets,
`compactIntegralFullFactor A μA f` is the actual function

```
n ↦ ∫ a, f(a,n) dμA
```

for a continuous compactly supported complex function `f` on `A × N`.
The compact first projection of `tsupport f` provides uniform integration
support for the parameter-integral continuity theorem. The partial integral
vanishes outside the compact second projection, so its topological support
is compact. Thus the result is an actual continuous compactly supported
function on `N`. The continuity argument itself does not need `N`
Hausdorff; Hausdorffness makes the compact second projection closed.

For the measure constructions and their laws, both groups are second
countable, `N` is Hausdorff, and `A`, `N` and `H` carry Borel measurable
structures. The quotient measurable structures in the compatibility result
are also Borel for their quotient topologies. These assumptions identify
the needed product measurable structures and make all displayed
homeomorphisms measurable.

`fullFactorSubgroupMeasure A H μA μH` is exactly

```
map fullFactorSubgroupEquiv (μA.prod μH).
```

No scalar is inserted. If both factor measures are sigma finite and right
invariant, this measure is right invariant. The construction does not
assert that arbitrary supplied factor measures are Haar.

For the analytic results, `H` is closed; `μA` and `μH` are sigma finite,
right invariant and finite on compact sets. For every compact test `f`,
`quotientAverage_fullFactor` proves the pointwise equality

```
quotientAverage (top.prod H) fullFactorSubgroupMeasure f q
  = quotientAverage H μH (compactIntegralFullFactor A μA f)
      (fullFactorQuotientEquiv A H q).
```

On a representative `(a,n)`, change of variables converts the subgroup
average to integration over `A × H`. The map
`(b,h) ↦ (b,h.val) * (a,n)` is a closed embedding because `H` is closed.
The pullback of `f` is therefore continuous with compact support, so it is
integrable for the product measure. Fubini places the `A` integral inside
the `H` integral, and right invariance of `μA` removes the representative
coordinate `a`. This proves the equality using convergent fiber
integrals, rather than exchanging totalized integrals without convergence.

`fullFactorQuotientMeasure A H ν` is exactly the pushforward of the
supplied measure `ν` on `H \ N` along the inverse quotient homeomorphism.
If `μN` is sigma finite and finite on compact sets and
`IsCompatible H μN μH ν` holds, then
`fullFactorQuotientMeasure_isCompatible` proves

```
IsCompatible (top.prod H) (μA.prod μN)
  (fullFactorSubgroupMeasure A H μA μH)
  (fullFactorQuotientMeasure A H ν).
```

All five fields are supplied. Nonzeroness and regularity transfer through
the homeomorphism. Its translation law transfers right invariance.
The pointwise averaging identity and the compact partial integral reduce
averaging integrability to that of the supplied compatible quotient.
Finally its integral formula and convergent product Fubini give the
exact ambient product integral.

This result constructs compatibility from specified compatible measures
on the second factor. It proves neither general quotient-measure
existence nor finite volume, reductive unimodularity, or any
reduction-theory statement. Actual adelic specialization is a separate
construction.
