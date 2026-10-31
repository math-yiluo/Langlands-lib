# Integration in a finite-dimensional algebraic span

Author: Worker 94. This is an internal construction from scalar Bochner integration, finite bases and algebraic dual separation in Mathlib. It attributes no additional theorem to the external automorphic literature.

For a topological space `X` and a complex vector space `V`, `HasFiniteContinuousSpan F` means that the complex linear span of the range of `F : X → V` is finitely generated and that `l ∘ F` is continuous for every algebraic linear functional `l : V →ₗ[ℂ] ℂ`. No topology is chosen on `V`. The domain and vector spaces may have independent universes. Constants, sums, complex scalar multiples, images under algebraic linear maps, and continuous changes of the domain preserve this property. The finite-span arguments for sums and changes of domain use that a subspace of a finite-dimensional complex vector space is finite dimensional.

For the integration results, `X` is compact with its Borel measurable structure, and `μ` is any finite measure. Each scalar coefficient is integrable by continuity and compactness. `exists_integral` constructs a vector `v : V` satisfying

`l v = ∫ x, l (F x) ∂μ`

for every algebraic linear functional `l`. Its proof chooses a finite basis of the range span, extends its coordinate functionals to `V`, and takes the finite sum of the scalar coordinate integrals multiplied by the basis vectors. The finite-basis expansion and finite-sum integration prove the displayed identity. The definition `integral μ F hF` chooses one such vector; `dual_integral` records its defining identity.

Algebraic dual separation proves uniqueness, expressed by `integral_eq_iff`. Consequently the vector is independent of all basis and extension choices. `integral_linearMap` proves that integration commutes with every complex linear map, including maps between vector spaces without chosen topologies. The subsequent theorems prove additivity, complex homogeneity, and the constant formula `integral μ (fun _ => v) _ = (μ.real Set.univ : ℂ) • v`. For a probability measure the constant integral equals `v`.

This module supplies a finite-span integration construction. It does not assert that an arbitrary orbit has finite continuous span, construct a group-invariant projection, or prove invariant restriction finiteness, central generation, admissibility, or automorphic differential growth.
