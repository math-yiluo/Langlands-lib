# Proofs of naturality of actual closure inflation

This module proves both propositions imported from
`Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityStatement`:

- `closureInflationTowerCompatibility : ClosureInflationTowerCompatibility.{u}`;
- `closureInflationBaseChangeCompatibility : ClosureInflationBaseChangeCompatibility.{u}`.

These are exact, unapplied target types in arbitrary common universe `u`.
Both results hold for every natural cohomological degree, including zero.
They use the existing ordinary relative cohomology, continuous absolute
cohomology, unit representations, and specified algebraic closures. The
published statement and all its dependencies are unchanged.

## Tower proof

For a compatible tower `K → L → M`, with `L/K` normal and `M/K` finite,
`ClosureNaturality.normalRestriction` equips the actual
`AlgEquiv.restrictNormalHom L` with continuity. Its domain has the discrete
Krull topology of a finite extension. The coefficient morphism
`continuousInflationCoefficients` is exactly `unitInclusionLinear L M`,
with continuity from the discrete unit topology and equivariance from
`AlgEquiv.restrictNormal_commutes`. Applying `ContinuousCohomology.map`
defines the auxiliary `continuousInflation`.

`continuousInflation_comparison` is the pointwise form of the published
`Langlands.Continuous.continuousToOrdinary_naturality`. Its ordinary map is
exactly `relativeInflation K L M`, since forgetting the topology of the
coefficient morphism recovers `inflationCoefficients K L M`.

Now let `L` and `M` be normal intermediate fields of the same specified
algebraic closure, with the supplied scalar towers through `M`.
`normalRestriction_closure` proves that restriction through `M` equals
direct restriction to `L`, using
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`. The underlying unit
inclusions agree because

    (M → Kbar)((L → M)(a)) = (L → Kbar)(a).

The proof uses `IsScalarTower.algebraMap_apply` and unit extensionality.
`continuousInflation_closure` combines these two identities with
`ContinuousCohomology.map_comp`, the published cochain-map congruence lemma,
and the homology functor. Thus its equality is an equality of the actual
continuous cohomology morphisms.

For the final theorem, every ordinary class `x` is written as the image of
some continuous class `y` under `continuousToRelativeEquiv K L n`.
The comparison identity and
`closureInflation_continuousToRelative` reduce the desired equality to
`continuousInflation_closure` evaluated at `y`. This proves exactly

    closureInflation K M n (relativeInflation K L M n x)
      = closureInflation K L n x.

## Mixed base-change proof

For fields and towers `K → E → M` and `K → L → M`, with `L/K` normal
and `M/E` finite, `mixedRestriction` is the continuous homomorphism

    Gal(M/E) → Gal(M/K) → Gal(L/K),

where the first arrow restricts scalars and the second restricts to the
normal field `L`. Its continuity again follows from discreteness of the
finite domain group. The coefficient map `mixedCoefficients` is the actual
unit inclusion `Lˣ → Mˣ`; equivariance follows from normal restriction
commuting with the field inclusion. No normality of `E/K` or `M/K` is used.

`mixedContinuousMap` applies `ContinuousCohomology.map` to these data.
In `mixedContinuousMap_comparison`, the ordinary composite is identified
using `groupCohomology.map_comp` and `groupCohomology.map_congr`:
its group map is definitionally the composite above, and its coefficient
map is the unit inclusion followed by the identity on `Mˣ`.
The continuous-to-ordinary naturality theorem consequently identifies
this continuous map with the specified ordinary inflation followed by
ordinary restriction.

For the closure square, write `i : Kbar → Ebar` for the supplied algebra
map. The explicit hypothesis `hcompat` says

    (M → Ebar)((L → M)(a)) = i((L → Kbar)(a)).

`closure_mixedRestriction` proves equality of the two continuous group
maps `Gal(Ebar/E) → Gal(L/K)`. For an automorphism `σ` and `a : L`,
it applies the injective maps `L → Kbar → Ebar` to the proposed equality.
Twice using `AlgEquiv.restrictNormal_commutes` identifies the source-side
image with `σ(i(a))`. The compatibility hypothesis identifies this with
`σ((M → Ebar)((L → M)(a)))`. Restriction commutation through `M` and
then `L` identifies that expression with the target-side image; one more
application of `hcompat` completes the comparison. This calculation uses
only `L/K` and `M/E` normal, and the algebraic closure's normality over `K`.

The coefficient square is precisely `hcompat` on the underlying value of
each unit. The lemma `closureContinuousInflation_baseChange` therefore
follows from continuous cohomology composition and cochain-map congruence.
Finally, surjectivity of `continuousToRelativeEquiv K L n`, the mixed
comparison identity, and `closureInflation_continuousToRelative` give

    absoluteRestriction K E n (closureInflation K L n x)
      = closureInflation E M n
          (relativeRestriction K E M n (relativeInflation K L M n x)).

The final theorem retains all and only the hypotheses of the published
base-change proposition. There is no characteristic, local-field,
unramifiedness, arithmetic-coordinate, or positive-degree premise.
The auxiliary continuous maps are proved to compare with the existing
ordinary maps; they do not replace any map in the target propositions.

## Provenance and authorship

These are internal functoriality proofs for the published field-induced
constructions, rather than translations of a new literature theorem.
Their inputs are the named published comparison and congruence results,
Mathlib's cohomology functoriality, normal restriction identities, and
scalar-tower identities. The Markdown describes the implemented Lean
proofs. The module establishes no existence of arithmetic stages and no
local invariant theorem.

Worker 104 implemented the proofs and this explanation. Worker 154
formulated the published naturality targets and coordinated their scope
with the absolute-invariant assembly; that contribution is credited in
the submission. Existing published dependencies are imported by Lean name.
