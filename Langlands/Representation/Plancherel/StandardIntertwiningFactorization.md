# Standard-integral composition from literal subgroup factorizations

This is a derived application of `QuotientFactorization` to the actual
standard integrals of `StandardIntertwiningComposition`. Its source motivation
is Waldspurger (2003), IV.1, printed p.279 (PDF p.45), and the composition
assertion IV.1(12), printed p.283 (PDF p.49). It constructs the coordinate and
quotient-normalization inputs from literal product factorizations; it does
not prove those factorizations for general reductive groups.

For actual subgroups `U₀`, `U₁`, `U₂`, `V`, `W` of a topological group,
`OrderedSubgroupFactorization` records inclusions `V ≤ U₁`, `V ≤ U₂`,
`W ≤ U₂` and three homeomorphisms:

- `(U₀ ∩ U₁) × V → U₁`, given by `(h,v) ↦ h*v`;
- `(U₁ ∩ U₂) × W → U₂`, given by `(h,w) ↦ h*w`;
- `(U₀ ∩ U₂) × (V × W) → U₂`, given by `(h,(v,w)) ↦ h*(v*w)`.

Each intersection uses `subgroupOf` in the displayed target, and each product
uses the actual inclusion maps. No homomorphism property of the product
coordinates, normality or commutation is required.

In a topological group with the displayed Borel structures,
`quotientCoordinates` constructs `OrderedQuotientCoordinates` by applying
`factorQuotientHomeomorph` to each product. Thus its maps are the actual
cosets of `v`, `w` and `v*w` in the respective left quotients. It requires
the product measurable structure on `V × W` to be its Borel structure as
well as the individual Borel structures. This condition is explicit; the
construction does not silently infer it for arbitrary spaces.

For the measure comparison the ambient group is locally compact and
Hausdorff and all three `Uᵢ` are closed. Supply measures on `U₁`, `U₂`
finite on compact sets, and regular two-sided Haar measures on the three
intersections. The intersection measures and the measures `μV`, `μW`
are S-finite. The two coordinate measures and their product are regular;
regularity of the product is an explicit premise. Supply compatible Weil
measures `ν₁₀`, `ν₂₁`, `ν₂₀` on the actual quotients.

The additional normalization premises are exact measure preservation of
the three product homeomorphisms with source measures
`μI₁₀.prod μV`, `μI₂₁.prod μW` and
`μI₂₀.prod (μV.prod μW)`. The last two use the same supplied ambient
measure `μU₂`. `measurePreserving_quotientCoordinates` derives the three
exact measure-preserving equations for the constructed quotient charts.
It derives local compactness of the target subgroups from their closedness,
and closedness of each intersection from the continuous subtype inclusion,
then applies `IsCompatible.measurePreserving_factorQuotientHomeomorph`
three times. That comparison uses positive lifting, scalar Fubini and the
real Weil formula, retaining the supplied normalization exactly.

`comp_hasIntegral` applies these derived comparisons to the actual
standard-integral composition theorem. It starts with a vector in the
original normalized induction, an intermediate vector in the actual
intermediate normalized induction, and the two successive integral relations.
Genuine absolute product convergence after every original smooth functional
at every ambient argument remains explicit. The conclusion is the direct
standard-integral relation in the original inducing carrier. The ambient
group is also nonarchimedean for these induction constructions, the
semidirect decompositions share their actual Levi, and the group and carrier
universes remain independent.

The general reductive root-distance condition, existence of the displayed
literal products, their exact normalized Haar product identities, the
regularity and measurable-structure premises in the actual application,
and analytic convergence remain obligations. The product identities are
premises of this intermediate deduction, not permanent structural assumptions
authorized to close the Plancherel program. This unit does not prove rational
continuation, the root-distance composition assertion, or any whole-program
completion condition.
