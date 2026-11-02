# Convergence, invariance and vanishing of actual subgroup constant terms

This module continues the actual subgroup-quotient construction in
`GroupSchemeConstantTerm`. Its parameters remain a number field `F`, an actual
affine group scheme `G/F`, a subgroup functor `U`, a measurable structure on the
actual quotient `Q = U(F) \ U(A_F)`, and a supplied measure `mu` on `Q`.

For an actual subgroup element `n`, associativity identifies the integrand at
`n*g` with the integrand at `g` composed with positive right translation by `n`
on `Q`. If the measurable structure is Borel and this particular translation
preserves `mu`, `constantTerm_subgroup_mul` proves left invariance of the
totalized integral under `n`. The translation homeomorphism is a measurable
embedding, so the Bochner change-of-variable identity applies without an extra
integrability assumption. A measure-preservation hypothesis is essential and
is explicitly retained.

`HasVanishingConstantTerm` requires both convergence at every ambient adelic
argument and zero integral at every argument. These functions form
`vanishingConstantTermSubrepresentation` inside the original continuous
rational-invariant representation. Its linear closure uses the convergent
operator's additivity and scalar law; its translation stability uses the
positive `g*h` action formula. `constantTermKernelSubrepresentation` is the
kernel of the actual complex-linear operator on its convergence domain, with
the restricted action. Its membership theorem identifies its elements with
the preceding ambient vanishing condition. Thus totalized zero values alone
do not silently substitute for convergence.

Under explicit `CompactSpace Q`, `BorelSpace Q` and `IsFiniteMeasure mu`
hypotheses, every integrand is continuous with compact support and hence
Bochner integrable. `hasConvergentConstantTerm_of_compact` records this
conditional result. `compactConstantTermLinearMap` consequently has the whole
original continuous function space as domain and preserves the positive right
action. Under these same hypotheses, membership in the vanishing space is
equivalent to zero integral at every argument.

For a supplied indexed family of actual subgroup functors, with a measurable
structure and measure on each actual quotient,
`familyVanishingConstantTermSubrepresentation` is the intersection of these
convergent vanishing subspaces. Its membership theorem retains convergence
and vanishing separately for every index. An empty family imposes no
conditions. This construction does not assert that an arbitrary supplied
family enumerates all proper rational parabolics, so it is not by itself a
definition or characterization of the full cuspidal space.

These are derived constructions from the existing actual quotients,
associativity, submodule kernels and intersections, continuous integration on
compact spaces, and Bochner change of variables. No literature theorem is
invoked. Compactness of the actual unipotent rational quotients, their
canonical invariant measures, the parabolic indexing comparison, smooth
output, the original matrix constant-term comparison and the full cuspidal
and L2 constructions remain separate obligations.
