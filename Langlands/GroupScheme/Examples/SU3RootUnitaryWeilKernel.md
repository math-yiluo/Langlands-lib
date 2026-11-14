# Actual restricted unitary depth-transition kernels on field fibres

This derived application proves smoothness, connectedness and unipotence for
the actual field-fibre kernels of integral unitary chart transitions after
restriction of scalars. It includes the published ordered lattice transitions
and compatible alternative model presentations before restriction.

Let `A` be a commutative ring, `O` a domain with fraction field `K`, and
`L/K` a separable quadratic field extension. Assume `O` is a finite projective
`A`-algebra and `k` is an arbitrary `A`-algebra field. All types lie in an
arbitrary common universe `u`. Neither ring is required to be local.

For finite index types `I, J`, take integral charts
`C : IntegralChart O K L I` and `C' : IntegralChart O K L J`. Their models
have the actual generic identification with the unitary parameter group
`unitaryParameterGroup K L`. Let `M : I → J → O` and `t : O` define an
integral chart change: the charts use the same trace-one element, their
bases satisfy `e_i = ∑_j M_ij e'_j` over `K`, and their trace-zero generators
satisfy `f = t f'`. This is the explicit `IsChartChange` hypothesis `h`.
The existing `C.isCompatible_of_isChartChange C' M t h` proves the bilinear
cocycle compatibility over `O`.

For every `φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))`,
`IntegralChart.weilFibreKernelIso` identifies the kernel of
`AffineWeil.BaseChange.sourceMap A O k C.model.group φ.hom` with the
kernel of the actual restricted bilinear homomorphism over `k` obtained
from `M, t` and the chart coefficients in `k ⊗[A] O`. Here `sourceMap`
means: apply actual affine Weil restriction from `O` to `A` to the
original `φ.hom`, then base-change along `A → k`. The comparison concerns
the scheme-theoretic pullback kernels, including their group structures.

The proof uses generic rigidity (`φ.hom_eq`) to identify `φ.hom` with
the original `C.chartHom C' M t h`. It then applies the actual kernel
comparison `AffineWeilBilinear.linearKernelFibreIso`. In particular the
calculation concerns every extension of the generic identity.

`IntegralChart.weilFibre_kernel_properties` uses the same rigidity
identification and `AffineWeilBilinear.linearKernelFibre_properties`.
It proves that this original kernel is smooth over `k`, connected in
its scheme topology, and unipotent in the Library's representation-theoretic
sense. The underlying bilinear result chooses a finite basis only over the
field `k`, for the algebra `k ⊗[A] O`, and describes the kernel by linear
equations in the restricted coordinates. That algebra may be nonreduced.
There is no hypothesis on residue characteristic or on the rank of the
reduced transition matrix.

For models `P, Q` of the same generic unitary group, assume compatible
identifications `e : P.Iso C.model (Iso.refl _)` and
`d : Q.Iso C'.model (Iso.refl _)`. Then
`weilFibrePresentationKernelIso` composes the generic-compatible
restriction/base-change kernel square with the explicit chart comparison
above. `weilFibre_presentation_kernel_properties` transfers the three
properties to every `φ : P.Hom Q (𝟙 _)`. These identifications are explicit
inputs, supplied before restriction.

Under `hω : IsRamifiedQuadraticValuation K L ω` and
`hO : IsValuationIntegers O K ω`, the published `latticeChart` and
`latticeModel` give the unitary models `X_{r,s}` for arbitrary real depths.
For `r₁ ≤ r₂` and `s₁ ≤ s₂`, the published transition matrix and scalar
satisfy `isChartChange_transition`. Applying the chart theorem gives
`lattice_weilFibre_kernel_properties` for every generic-identity extension
from `X_{r₂,s₂}` to `X_{r₁,s₁}`, and
`latticeTransition_weilFibre_kernel_properties` for the explicitly
constructed transition. The lattice charts use the existing normalization
of the central depth by `min s (2*r)`. Equal depths are allowed by both
weak inequalities.

The source motivation is Kaletha–Prasad (2023), Appendix C.4, equations
(C.4.1)–(C.4.2), Corollary C.4.3 and Lemma C.4.4, printed pp. 700–702 /
PDF pp. 731–733, followed by Proposition C.5.1 and Lemma C.5.3, printed
pp. 703–705 / PDF pp. 734–736. The implemented proof uses the published
bilinear models and their explicit transitions, generic rigidity, and a
general restriction/base-change kernel calculation. It does not use the
host Proposition 8.4.15.

This focused prerequisite assumes the quadratic and valuation data and,
for alternative presentations, compatible model identifications. It does
not identify the restricted lattice models with every supplied
`RootFiltrationModelData` or prove the exact
`UnramifiedRootDepthKernelStatement`. Root-case assembly and the remaining
supplied-presentation comparisons remain obligations of Task 6392.
