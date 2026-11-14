# Canonical restrictions of actual unitary integral charts

This derived application uses the fraction-field comparison in
`IntegralModel.AffineWeilGeneric` to construct actual restricted unitary
chart models and their generic-identity transitions. The generic
isomorphism and its commuting square are constructed from the original
integral chart.

Let `A, O` be commutative domains with fraction fields `F, K`, respectively.
Assume the compatible algebra towers `A → O → K` and `A → F → K`, and
that `O` is finite projective over `A`. Let `L/K` be a separable quadratic
field extension. All these types lie in an arbitrary common universe `u`.

In the namespace `SU3Root.IntegralChart`,
`canonicalWeilGroup A F O K L` is the actual affine restriction
`R_{K/F} U_{L/K}`. Finiteness of `K/F` follows from the fraction-field
towers and finiteness of `O/A`. The local geometry instances identify the
underlying scheme of the published unitary parameter group with the
polynomial scheme of its canonical bilinear chart.

For any finite index type `I` and integral chart
`C : IntegralChart O K L I`, `C.canonicalWeilModel A F O K L` is an
integral model over `A` of this fixed generic group. Its integral group
is the actual affine restriction of `C.model.group`. The canonical
generic identification is `AffineWeilGeneric.iso` applied to the original
chart model. `canonicalWeilModel_isSmooth` uses smoothness of affine
restriction. `canonicalWeilModel_hasGeometricallyConnectedFibres` applies
the field-test argument for restrictions of bilinear coordinate groups.
Only finite projectivity, rather than a specified free basis of `O/A`,
is assumed here.

Let `C' : IntegralChart O K L J` be another chart, with integral matrix
`M : I → J → O` and central scalar `t : O`. The `IsChartChange`
hypothesis says that the charts have the same trace-one element and that
their bases and central generators are related by the images of `M, t`
in `K`. The original `C.chartHom C' M t h` is already a homomorphism of
integral models extending the identity of `U_{L/K}`.
`canonicalWeilModelHom` restricts this homomorphism using
`AffineWeilGeneric.modelHom`. Its generic square follows from
`AffineWeilGeneric.iso_naturality`, and restriction of the generic
identity is the identity of `canonicalWeilGroup`.

Assume further that `A` is local. For every model homomorphism `φ`
between these two canonical restricted models extending the generic
identity, `canonicalWeilModel_kernel_properties` proves that the actual
scheme-theoretic kernel of `φ.specialFibreMap` is smooth over the residue
field of `A`, connected in its scheme topology and unipotent in the
Library's representation-theoretic sense. The proof supplies the
derived square to `weilModel_kernel_properties`. That theorem uses
generic rigidity to identify the actual special-fibre map with
restriction and residue-field base change of the explicit chart
transition, then invokes the actual restricted bilinear kernel theorem.
Its coefficient algebra is `(IsLocalRing.ResidueField A) ⊗[A] O`,
which may be nonreduced; no zero-or-unit dichotomy in that algebra is
assumed. `canonicalWeilModel_presentation_kernel_properties` transfers
all three properties to arbitrary models `P, Q` of the same generic
group over `A` when explicit isomorphisms of integral models from
`P, Q` to the two canonical restricted charts are given. These
isomorphisms commute with the identity on the generic group. The proof
uses the actual special-fibre kernel-square isomorphism.

The namespace `SU3Root.IsRamifiedQuadraticValuation` specializes these
constructions to the published lattice charts. Suppose an additive
valuation `ω : L → WithTop ℝ` satisfies
`IsRamifiedQuadraticValuation K L ω` and that
`hO : IsValuationIntegers O K ω`. This is the existing lattice-model
setting, including the normalized base uniformizer and half-valued
quadratic uniformizer.
`canonicalWeilLatticeModel A F O K L hω hO r s` restricts the actual
lattice chart `X_{r,s}` for every pair of real depths. The original chart
uses the central depth `min s (2*r)`. The smoothness and geometrically
connected-fibre theorems apply directly.

For `r₁ ≤ r₂` and `s₁ ≤ s₂`,
`canonicalWeilLatticeTransition` constructs a homomorphism from the
deeper lattice model to the shallower one over the generic identity.
`canonicalWeilLatticeModel_kernel_properties` proves the same three
actual special-fibre kernel properties for every extension of that
identity. It specializes the chart theorem to the existing
`transitionMatrix`, `transitionScalar` and
`isChartChange_transition`. Both depth inequalities are non-strict.
`canonicalWeilLatticeModel_presentation_kernel_properties` gives the
corresponding result for arbitrary explicitly isomorphic presentations
over `A`.

The source motivation is Kaletha–Prasad (2023), Appendix C.4,
equations (C.4.1)–(C.4.2), Corollary C.4.3 and Lemma C.4.4, printed
pp. 700–702 / PDF pp. 731–733, followed by Proposition C.5.1 and
Lemma C.5.3, printed pp. 703–705 / PDF pp. 734–736. The canonical
fraction-field comparison and this application are derived assembly
results, rather than verbatim restatements of those passages. The
implemented proof uses actual restriction, generic naturality and
rigidity, the restricted bilinear kernel calculation and compatible
presentation transport. It does not use the host Proposition 8.4.15.

The canonical generic group here is restriction of the unitary parameter
group. An identification with an ambient relative root group, matching
the lattice depths to a supplied apartment valuation and constructing the
isomorphisms for arbitrary supplied root models remain separate
obligations. This module does not prove
`UnramifiedRootDepthKernelStatement` or address the other root cases.
