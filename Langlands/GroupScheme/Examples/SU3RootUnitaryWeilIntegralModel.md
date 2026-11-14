# Actual restricted integral unitary models and special-fibre kernels

This derived application forms actual integral unitary models over the
restriction base and proves smoothness, connectedness and unipotence of
their special-fibre transition kernels.

Let `A` be a domain with fraction field `F`, and `O` a domain with fraction
field `K`. Let `L/K` be a separable quadratic field extension, and suppose
`O` is a finite projective `A`-algebra. Let
`C : IntegralChart O K L I` and `C' : IntegralChart O K L J` be the
existing integral unitary charts for finite index types `I, J`.
All types lie in an arbitrary common universe `u`.

For a group scheme `G/F` and an explicit isomorphism
`e : AffineWeil.BaseChange.source A O F C.model.group ≅ G`,
`IntegralChart.weilModel` is the integral model over `A` obtained from
`IntegralModel.affineWeil`. Its group scheme is the actual restriction of
the original chart group. `weilModel_isSmooth` proves smoothness.
`weilModel_hasGeometricallyConnectedFibres` applies
`AffineWeilBilinear.restriction_geometricallyConnected` to the original
chart coefficients `C.coeff`. The helper tests every field-valued base
point using the actual restriction/base-change isomorphism, so the latter
conclusion concerns the structure map over `A`, without a freeness
assumption on `O/A`.

Take a second generic identification
`d : AffineWeil.BaseChange.source A O F C'.model.group ≅ H`,
a matrix `M : I → J → O` and scalar `t : O`. The explicit
`IsChartChange` hypothesis `h` says that the two charts have the same
trace-one element and that their bases and central generators are
related by the images of `M, t` over `K`. The existing `chartHom` proves
the corresponding integral cocycle compatibility. For `f : G ⟶ H`,
assume the actual generic square

```text
BaseChange.sourceMap A O F C.model.group (C.chartHom C' M t h).hom
    ≫ d.hom = e.hom ≫ f.
```

Under that hypothesis, `weilModelHom` is the restriction of the original
chart transition, viewed as a homomorphism of the constructed models over
`f`.

Assume now that `A` is local. For every extension
`φ : (C.weilModel A F e).Hom (C'.weilModel A F d) f`,
`weilModel_kernel_properties` proves that the scheme-theoretic kernel
of `φ.specialFibreMap` is smooth over the actual residue field of `A`,
connected in its scheme topology and unipotent in the Library's
representation-theoretic sense. Generic rigidity and
`affineWeil_specialFibreMap_eq` identify the original special-fibre map
with the residue-field base change of the restricted chart transition.
The proof then applies `C.weilFibre_kernel_properties` with the actual
residue field. The coefficient algebra in that calculation is
`(IsLocalRing.ResidueField A) ⊗[A] O`, which is allowed to be nonreduced.
No residue-characteristic or reduced-matrix rank condition is imposed.

Finally, let `P, Q` be any integral models of `G, H` over `A`. Assume
explicit generic-compatible identifications
`ep : P.Iso (C.weilModel A F e) (Iso.refl G)` and
`dq : Q.Iso (C'.weilModel A F d) (Iso.refl H)`.
`weilModel_presentation_kernel_properties` transfers the same three
properties to every `φ : P.Hom Q f`. It applies the existing actual
special-fibre kernel-square isomorphism with the constructed
`weilModelHom`. These alternative presentations and their identifications
are over the restriction base `A`.

The source motivation is Kaletha–Prasad (2023), Appendix C.4,
equations (C.4.1)–(C.4.2), Corollary C.4.3 and Lemma C.4.4, printed
pp. 700–702 / PDF pp. 731–733, and Proposition C.5.1 and Lemma C.5.3,
printed pp. 703–705 / PDF pp. 734–736. The implemented argument is a
derived assembly of actual restriction, generic rigidity, the restricted
bilinear field-fibre theorem and compatible model transport. It does not
use the host Proposition 8.4.15.

The generic isomorphisms and their commuting square remain explicit
inputs. This package does not identify the constructed models with
every supplied root-depth model or prove
`UnramifiedRootDepthKernelStatement`. Those generic and supplied-root
comparisons and the full root-case assembly remain open.
