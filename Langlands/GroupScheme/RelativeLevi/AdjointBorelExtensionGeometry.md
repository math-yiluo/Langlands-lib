# Geometry of the actual adjoint Borel extension

This is an internal deduction applying affine fppf torus-image geometry to
`RelativeLevi.AdjointBorelExtensionData`. It retains the actual quotient
objects, their homomorphisms and the original radical from that data.
No replacement of the torus quotient or the radical is made.

Work in every universe over an arbitrary scheme `S`. The inputs are group
schemes `B`, `G`, `A`, maps `i : B ⟶ G` and `q : G ⟶ A`, an automorphic
action `a` of `A` on `G`, a commutative group scheme `T` with
`t : T.toGrp ⟶ B`, and

`d : RelativeLevi.AdjointBorelExtensionData i q a T t`.

In particular, `d` already supplies the actual Borel quotient
`P = d.borel.group`, the actual torus quotient `D = d.torus.group`, the
closed inclusions `P ⟶ A` and `D ⟶ P`, the fppf maps `B ⟶ P` and
`T ⟶ D`, and the original relative unipotent radical `U` with its
inclusion into `B`. It also supplies the sectioned original retraction
`B ⟶ T` and the compatible full-kernel certificates. The imported
extension module constructs the split fppf homomorphism
`d.projection : P ⟶ D` with full kernel represented by the original
`U ⟶ B ⟶ P`. The present module does not assume additional
representability or kernel comparisons.

`AdjointBorelExtensionData.torusCommGroup` gives the same actual `D` its
descended commutative group law. It uses the flat, surjective, locally
finitely presented homomorphism `T ⟶ D` and the source's existing
commutative group law. The generic helper cancels the fppf epimorphism on
products in the multiplication/braiding equality. The underlying group
scheme is definitionally `d.torus.group`; `torusCommGroup_toGrp` records
this equality. This definition requires neither affineness of `A` nor
torus structure on `T`.

The remaining conclusions assume that `A` is affine over `S`:

- `borel_isAffineHom` and `torus_isAffineHom` prove that the actual `P`
  and `D` are affine over `S`. Each closed inclusion is affine, and its
  composite with the affine structure map is the desired structure map.
- `torus_isTorus` additionally assumes
  `RelativeTorus.IsTorus T.toGrp`. Apply the generic relative
  torus-image theorem to the actual fppf map `T ⟶ D`, using the
  established affineness of `D`. Thus the actual quotient, including
  its original group law, is a relative torus.
- `radical_isClosedSubgroup_of_affine` proves that the original composite
  `U ⟶ B ⟶ P` is a closed subgroup. Affineness makes `D` separated,
  supplying the hypothesis of the imported extension's
  `radical_isClosedSubgroup`. No torus hypothesis is needed for this
  conclusion.
- `projection_smooth` proves that the existing `P ⟶ D` is smooth.
  Affineness makes its composite with `D ⟶ S` quasi-compact;
  quasi-separatedness of `D ⟶ S` permits cancellation and gives
  quasi-compactness of `P ⟶ D`. Its full fppf kernel is represented by
  the original `U`, whose structure map is smooth because it is a
  relative unipotent radical. The Library's smooth-kernel quotient
  theorem therefore applies. This argument does not require torus
  structure on `T`.
- `borel_smooth` additionally assumes that `T` is a relative torus.
  The actual `D` is then smooth over `S`, and composition with the
  smooth `P ⟶ D` gives smoothness of `P` over `S`.

The generic helper pair `Torus/RelativeQuotient.lean` and `.md` describes
the arbitrary-base smooth-target, commutativity descent and torus-image
proofs used here. The provenance is entirely internal: compose the
existing actual quotient data and its full kernel with those geometric
results and the represented smooth-kernel theorem.

For application to a reductive group over a ring, the imported
`IsRelativeBorelSubgroup.adjointBorelExtensionData` constructs the
required `d` from a supplied relative maximal torus in a relative Borel,
a supplied full-center ambient fppf quotient and a compatible action.
Affineness of that ambient quotient remains an explicit hypothesis of
the present geometric conclusions. The module does not prove existence
of an affine adjoint quotient, construct an induced finite étale
Weil-restriction presentation for `D`, construct a vector-bundle series
for `U`, prove cohomological vanishing, or prove the exact semilocal
inner-form statement.
