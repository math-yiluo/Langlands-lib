# A common integral split source in recovered models

This internal supporting composition constructs one split torus over the
valuation ring whose generic fibre maps as a maximal split torus to the original
group and whose special fibre maps as a maximal split torus to a supplied
reductive quotient of the recovered lower neutral special fibre.

## Statement and scope

Let `F` be an arbitrary nonarchimedean local field and let `G` be connected
reductive over `F`. Retain the actual descended torus `T`, its embedding `iT`,
the supplied valuation apartment `D` over `inertiaFixedField F`, the actual
centralizer `C`, and full integer-valued V6 compatibility `hDC`. Suppose a
maximal split torus `iS : S.toGrp ⟶ G` factors through `iT` by an actual
commutative-group morphism `f`, with `groupHom f ≫ iT = iS`.

`RecoveredApartmentFixerModels.exists_integralSplitSource` applies to any
recovered bounded-subset models `M` for these data and any supplied valid
reductive quotient `Q` of `M.lower`. It supplies:

- one commutative group scheme `A` over the valuation ring, split as a torus;
- an actual map from the generic fibre of this `A` to `G`, maximal split over
  `F`;
- an actual map from the special fibre of the same `A` to `Q.quotient`,
  maximal split over the residue field of `F`.

`UnramifiedRecoveredSplitSourceStatement` specializes this conclusion to the
actual `recoveredFixedPointModels` of a coefficient-fixed apartment point `x`.
It retains maximal splitness of `iT` after scalar extension to the actual
maximal unramified field, which is needed to construct those models. The point
is fixed as an apartment valuation family by every actual coefficient
automorphism. No additional integral torus, residue-rank, model-existence, or
characteristic hypothesis is added. The universe `u` is arbitrary.

The statement concerns the chosen reference quotient. It makes no assertion
about transfer of maximal splitness between different reductive quotients,
existence of a chamber, absence of proper rational parabolics, or fixation of a
prescribed building point by torus units. These are separate parts of the
fixed-point split-torus problem.

## Implemented proof and provenance

This is derived internal content, with no independent literature claim. Its
actual published inputs are:

- `UnramifiedFixedSubsetModels`, providing `recoveredFixedPointModels`;
- `UnramifiedRecoveredTorusClause`, providing `lowerApartmentTorus` and
  `lowerApartmentTorus_satisfiesTorusClause`;
- `UnipotentQuotientMaximalSplit`, providing source-isomorphism invariance and
  maximal splitness through a smooth connected unipotent quotient over a
  perfect field.

The integral source is exactly
`A := M.lowerApartmentTorus C hDC hiS hf`. The full torus clause says that its
integral torus is split and closed in the recovered neutral model and that its
actual special-fibre inclusion is maximal split before taking the quotient.
Its actual generic-fibre isomorphism identifies the generic source with the
prescribed `S`. Composing that isomorphism with `iS` gives the generic map;
`IsMaximalSplitTorus.iso_comp` proves maximal splitness.

The residue map is the actual base change of the same integral inclusion,
followed by `Q.projection`. The validity of `Q` supplies its represented smooth
connected unipotent radical, the fppf quotient property, and connected
reductivity of its target. The residue field of the nonarchimedean local field
is perfect. The theorem
`IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel` therefore
preserves the known maximal splitness of the actual special-fibre inclusion.
This uses the same quotient argument as
`lowerApartmentTorus_quotient_isMaximalSplitTorus`, while importing only the
smaller torus-clause and unipotent-quotient modules.

Finally, `unramifiedRecoveredSplitSource` constructs the singleton-point models
and applies the general lemma. The entire construction uses actual fibres and
maps of one integral torus.
