# Levi restrictions of radical averages of adelic test functions

Module `Langlands.Global.AdelicLeviRadicalAverageTestFunctionStatement` states the proposition
`Langlands.Global.LeviRadicalAverageTestFunctionStatement` (universe `u`) and proves nothing.

## Statement

Let `F` be a number field, `G` an affine group scheme over `Spec F`, locally of finite type, with
a compatible standard parabolic family `fam : StandardParabolicFamily F G` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`), and let `J` be a standard index, with
standard parabolic `P_J = M_J U_J`, Levi map `ι = fam.l J ≫ fam.p J : M_J → G` and adelic radical
`N_J = U_J(𝔸) ⊆ G(𝔸)` (`AdelicSubgroupPoints.adelicPoints F G (range (fam.iU J ≫ fam.p J))`), with
the Haar measure `du` normalized by `vol(U_J(F) \ U_J(𝔸)) = 1`
(`AdelicSubgroupPoints.normalizedHaarMeasure`).

For every test function `β` on `G(𝔸)` (`IsAdelicTestFunction F G β`: smooth, compactly
supported, bi-invariant under open subgroups of `G(𝔸_f)`), the function

`m ↦ ∫_{U_J(𝔸)} β(u ι(m)) du`

on `M_J(𝔸)` is a test function on `M_J(𝔸)` (`IsAdelicTestFunction F (fam.M J) _`).

## Provenance

This is a derived statement. In the Iwasawa integration formula
`∫_{G(𝔸)} f = ∫_K ∫_{M(𝔸)} δ_P(m)⁻¹ ∫_{U(𝔸)} f(u m k) du dm dk` of Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series* (1995), I.1.13, printed p. 18 (proved in the Library, with
Mathlib's Haar measures and a positive constant, as `AdelicGroupPoints.adelicIwasawaIntegration`),
the integral over the radical is taken first. For a function `f` on `U(𝔸) M(F) \ G(𝔸)`, left
invariance under `U(𝔸)` and normalization of `U(𝔸)` by `M(𝔸)` turn the right convolution
`∫_{G(𝔸)} β(s) f(ι(m₀) k₀ s) ds` into an integral of the fibres `m ↦ f(ι(m₀ m) k)` against the
weighted Levi kernels `m ↦ δ_P(m)⁻¹ ∫_{U(𝔸)} β(k₀⁻¹ u ι(m) k) du`, followed by integration over
`k ∈ K`. Each such kernel is, up to the continuous factor `δ_P(m)⁻¹`, the function of the
statement for the test function `x ↦ β(k₀⁻¹ x k)`. The proposition is the regularity of these
radical averages, the counterpart for integration over `U(𝔸)` of the constant terms of their
I.2.6, printed p. 27, where the integration runs over `U(F) \ U(𝔸)`.

Each of the four clauses of `IsAdelicTestFunction` follows from the corresponding clause for `β`.
The support is contained in the Levi projection of the compact set `tsupport β ∩ P_J(𝔸)`,
compact because multiplication `U_J(𝔸) × M_J(𝔸) → P_J(𝔸)` is a homeomorphism onto the closed
subgroup `P_J(𝔸)`; the containment can be strict, since the integral may cancel. Right
invariance under an open subgroup of `M_J(𝔸_f)` comes from right invariance of `β`, and left
invariance from left invariance of `β` together with the invariance of `du` under conjugation by
compact subgroups of `M_J(𝔸_f)`. Smoothness of the archimedean slices is differentiation under
the integral sign: at a fixed finite slice, compactness and right finite-level invariance reduce
the integrand to finitely many smooth slices integrated over a fixed compact part of the radical.
