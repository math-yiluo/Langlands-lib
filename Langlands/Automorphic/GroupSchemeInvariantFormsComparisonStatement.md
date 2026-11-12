# Comparison of automorphic functions on `G(F) \ G(𝔸)` with the existing forms

Module `Langlands.Automorphic.GroupSchemeInvariantFormsComparisonStatement`
states `RationalAutomorphicFunctionComparisonStatement` as a proposition
definition. It supplies no proof.

## Statement

For every number field `F`, every affine group scheme `G` over `F`, every
subgroup `Kinf` of the infinite adelic points `G(𝔸_∞)`, every matrix
representation `rho : G → GL_N`, every proof `hsmooth` that `G` is smooth of
relative dimension `d` (fixing the existing atlas on `G(𝔸_∞)`) with the
existing commutator premise `hcalc`, and every function `φ : G(𝔸) → ℂ`:

`φ` satisfies `IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho` for
`Γ = AdelicGroupPoints.rationalSubgroup F G`, the subgroup of rational points
`G(F)` in `G(𝔸)`, if and only if there is an element `f` of the existing
carrier `FinitePlotSmoothRationalFunctions F G` whose evaluation
`evaluate F G f.val` equals `φ` and which satisfies the existing
`IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f`.

All parameters are those of the existing definition, and both sides use the
same `Kinf`, `rho`, `hsmooth` and `hcalc`. No connected reductivity, closed
embedding or maximal compactness hypothesis is needed for the comparison.

## Purpose and provenance

This is an internal consistency statement, not a theorem of the literature.
`Langlands.Automorphic.GroupSchemeInvariantForms` formulates the conditions of
Mœglin–Waldspurger I.2.17 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, printed p.37)
for functions left invariant under an arbitrary subgroup `Γ`, so that the
space `𝒜_P` of Bernstein–Lapid §2.2 (p.191) is available with
`Γ = U(𝔸)M(F)`. The statement says that for `Γ = G(F)` this formulation
recovers exactly the existing forms of `Langlands.Automorphic.GroupSchemeForms`,
so the two developments describe the same automorphic forms on
`G(F) \ G(𝔸)`.

The expected proof matches the conditions one by one: rational left
invariance is membership in the existing rational-invariant space;
continuity, plot-smooth infinite slices and a common open finite stabilizer
are membership in the finite plot-smooth carrier; finiteness of the
`Kinf`-translates is the same in the carrier and after the injective
evaluation map; for the center, the existing
`isAdelicCenterFinite_iff_exists_ideal` gives the common-ideal form, and the
existing slice intertwining of the center actions together with the
determination of a function by its slices transfers it to slices; moderate
growth is the same inequality.

## Scope

Only `Γ = G(F)` is compared. Nothing is asserted for other subgroups, for the
literal tensor-product spaces of Getz–Hahn (6.1), or about the dependence on
`Kinf` and `rho`.
