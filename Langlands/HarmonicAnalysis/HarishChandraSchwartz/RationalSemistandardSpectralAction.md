# Actual product action on full semistandard spectral families

Worker 268. This internal assembly uses the actual full semistandard family
of `RationalSemistandardSpectralFamily` and the published action in
`ProductInducedOrbitFullAction`. It is a supporting construction for the
invariant-subspace unit of Task 7258. It constructs the action before imposing
the inter-parabolic invariant condition.

The source is Waldspurger (2003), *La formule de Plancherel pour les groupes
p-adiques*, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The coefficient sections come from VI.1, printed pages 295–296 (PDF pages
61–62), their direct sum from VI.3, printed page 305 (PDF page 71), and the
product action is the one used in the proof of VI.4.1, printed page 306
(PDF page 72). The pointwise assembly, exact support equality and finite
intersection argument below are derived interfaces for these source objects.

The field has an independent universe `u` and is any nonarchimedean local
field with finite residue field. The ambient group scheme is affine and
locally of finite type; the construction uses this weaker setting and each
intrinsic semistandard index's closed connected reductive Levi. Its intended
source setting is connected reductive ambient group and maximal split torus.
No ambient splitness, characteristic-zero assumption or representation-carrier
topology is imposed. Representation carriers have the independent universe
`uV`.

The full family retains exactly the published parameters: the intrinsic
all-test semistandard index, `chosenLeviModel p`, a split component `a p` with
proof `ha p`, its normal split-center image, a measurable quotient with Haar
measure `mu p`, and the compact-picture data `d p`. These choices do not become
new coordinates of the intrinsic index. The projection continuity and actual
Iwasawa factorization in `CompactData` remain visible inputs, with existence
and model/compact-picture independence targets owned by Task 7229. This
construction needs no scalar continuation, density or orbit-measure
normalization input.

`RationalSemistandard.orbitRepresentation` is the existing full coefficient
action at every actual inducing representative in one orbit.
`orbitRepresentation_smooth_mem` specializes
`productInducedOrbitRepresentation_full_smooth_mem` using the model's
`unitaryCoordinates_hasLaurent` theorem, the actual literal subgroup
decomposition, closedness and the supplied compact picture. Thus both
self-twist coherence and finite scalar-smooth compact restriction are
preserved by a proved published theorem. The companion
`smoothOrbitSections_isSmoothVector` specializes the published common-open-
stabilizer result for the entire component.

`rationalSemistandardThetaRepresentation` acts componentwise on the full
dependent product `RationalSemistandardThetaSections`, before finite support
or invariance. Its identity, multiplication and linearity laws follow
pointwise from the actual coefficient representation. Its application
formula is definitional. The theorem
`rationalSemistandardThetaRepresentation_support` proves equality of literal
nonzero-component supports under the action: each component operator is
injective, with inverse given by the inverse group element. This argument
uses no finiteness of geometric indices or Fourier families.

`rationalSemistandardThetaRepresentation_smooth_mem` combines proved component
stability with this exact support equality. It gives
`rationalSemistandardThetaSmoothRepresentation` on precisely the published
smooth finite-support submodule. Its value theorem identifies the restriction
with the raw action.

`rationalSemistandardThetaSmoothRepresentation_isSmooth` proves smoothness
of the entire family. For each component, the preceding published theorem
supplies one open subgroup fixing that entire component at all parameters and
representatives. Intersecting these subgroups over the finite input support
gives one open subgroup fixing the whole family; all other components vanish
and linear operators preserve zero. The proof never takes an infinite
intersection. `rationalSemistandardThetaSmoothObject` bundles this exact
representation in the canonical complex `SmoothRep` category.

The inter-parabolic invariant predicate and its stability under this action
still require Task 7257's specified all-unitary normalized comparison and
intrinsic fiber adapters. They are not asserted here. The construction does
not supply a projector, weighted synthesis, global form or Fourier-support
theorem.
