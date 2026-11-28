# Enlarging a coarse subspace by central directions

In Arthur's descent the coarse space `b = 𝔞_M` need not contain the central space
`centralSpace R` of the fine roots (the fine centre can be larger than the coarse one). This
module reduces descent for `b` to descent for the enlarged space
`hull R b = b ⊔ (centralSpace R ⊓ bᗮ)`, which contains the central space whenever `b` is
compatible with it. The compatibility is `IsCentreSplit R b`: the orthogonal projection to
`centralSpace R` maps `b` into itself. The added directions `surplus R b = centralSpace R ⊓ bᗮ`
are those central directions that are orthogonal to `b`; they correspond to the surplus central
block of J. Arthur, *An introduction to the trace formula* (2005), (17.13),
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.

## Contents

- **Linear algebra of the hull.** `orthogonal_invariant`, `central_decomp`, `central_le_hull`,
  `central_eq_sup` (under `IsCentreSplit`, the central space is `(centralSpace R ⊓ b) ⊔ surplus R b`),
  `mem_orthogonal_hull`, `orthogonal_hull_of_central`, `mem_of_mem_hull`.
- **Roots and chambers are unchanged.** Roots are orthogonal to the central space
  (`inner_central`), so `coe_restrictedRoot_hull`, `restrictedRoot_hull_eq_zero_iff`,
  `posSet_add_central`, `isRegular_add_central`, `parabolics_hull`, `restrictedRoot_hull`,
  `restrictedRoots_hull`, `simpleRoots_hull` identify the chambers and simple roots of `b` and of
  the hull.
- **Families.** `theta_hull`, `inducedFamily_hull`, `cM_hull` show that the `θ`-functions, induced
  families and the functions `cM` on `b` are those of the hull evaluated at parameters extended
  by `extendParam`; `extendParam_apply_of_mem` and `extendParam_extendParam` compute iterated
  extensions, and `generic_hull` transfers genericity of parameters.
- **Specialness.** `isSpecialSubspace_hull`: if `b` is special in `a₁` for the weights `m`, so is
  the hull.
- **Descent data.** Under `IsCentreSplit R b` and `centralSpace R ≤ a₁`, `surplus_le_fine`,
  `hull_le`, `normal_decomp`, `noncentral_decomp`, `starProjection_normal_eq` and
  `dDescent_hull` show that the descent coefficients for `b` (with coarse centre
  `b ⊓ centralSpace R`) equal those for the hull (with the full central space);
  `central_le_of_mem_leviSpaces`, `offset_hull`, `descentPoint_hull_iff`,
  `isGenericOffset_hull_iff` (for the genericity condition `IsGenericOffset` on displacements) and
  `descentSection_hull` transport the displacements and descent sections.
