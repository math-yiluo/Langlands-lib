# Field-fibre kernels after restriction of compatible integral models

This internal comparison extends the compatible-model kernel comparison to
restriction of scalars followed by field base change. Its application to the
unitary lattice models is in
`Langlands.GroupScheme.Examples.SU3RootUnitaryWeilKernel`.

All rings, fields and schemes lie in an arbitrary common universe `u`. Let `A`
be a commutative ring, `O` a finite projective commutative `A`-algebra that is
a domain, `K` its fraction field, and `k` any `A`-algebra field. Let `M, M'`
be integral models over `O` of a `K`-group `G`, and `N, N'` models of a
`K`-group `H`. Integral models are affine, flat and locally of finite type.
The local affine-total-space instance follows from their affine structure
morphisms and the affine base `Spec O`; it adds no hypothesis.

Suppose `e : M.Iso M' (Iso.refl G)` and
`d : N.Iso N' (Iso.refl H)` are compatible model identifications. For
`φ : M.Hom N f` and `ψ : M'.Hom N' f` over the same generic map `f : G ⟶ H`,
the existing generic-rigidity theorem `Iso.hom_square` proves
`e.iso.hom ≫ ψ.hom = φ.hom ≫ d.iso.hom`.

- `Iso.weilFibreIso` restricts `e.iso` from `O` to `A` using
  `AffineWeil.mapIso`, then base-changes to `k`.
- `Iso.weilFibreKernelIso` applies the composition laws of actual restriction
  and base change to that square. `kernelSquareIso` then identifies the
  actual scheme-theoretic kernels of the original restricted maps after
  field base change. The kernels are the Library's pullbacks along the
  target identity sections.
- `Iso.weilFibreKernel_properties` transports smoothness of the kernel
  structure morphism, connectedness of its underlying scheme and the
  Library's representation-theoretic `IsUnipotent` predicate from the
  `ψ` kernel to the `φ` kernel.

This is a derived functorial construction, using
`IntegralModel.SpecialFibreKernelIso`, `AffineWeilBilinearSpecialFibre` and
`KernelSquareTransport`. It is motivated by the restriction-of-scalars
assembly in Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition C.5.1, printed pp. 703–704 / PDF pp. 734–735, and the
special-fibre assertion of Lemma C.5.3, printed p. 705 / PDF p. 736.
It assumes the compatible identifications and the comparison kernel's
geometry explicitly. Constructing those inputs for every supplied root-depth
model remains part of the root-depth proof. No local-ring hypothesis on `A`
or `O`, choice of basis of `O` over `A`, or reducedness assumption on the
fibre algebra `k ⊗[A] O` is used.
