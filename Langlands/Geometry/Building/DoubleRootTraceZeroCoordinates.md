# Trace-zero coordinates for the actual doubled root group

This is an internal construction from the published root-orbit weight-space,
represented root-group Lie comparison, and separable quadratic field interfaces.
Its primary proposition is
`Langlands.Geometry.Building.HasDoubleRootTraceZeroCoordinates`; the theorem
`hasDoubleRootTraceZeroCoordinates` proves it under the hypotheses below.

For a separable quadratic extension `E/F`, a nonzero trace-zero element `eta0`
defines `SU3Root.traceZeroScalarEquiv`, the additive equivalence

`F ≃+ Parameters.traceZero (fieldInvolution F E)`

sending `c` to `algebraMap F E c * eta0`. Injectivity follows from the nonzero
scalar and injectivity of the field map. Surjectivity is the published
`SU3Root.exists_algebraMap_mul_eq_of_traceZero`. The two inverse-scaling lemmas
show that a proportionality relation in `E` becomes the corresponding relation
in `F`, first for `F`-multiplication and then for scalars from any compatible
lower field `k`. They do not install a module instance on the trace-zero
additive subgroup. These lemmas allow independent universes for `k`, `F`, `E`.

For the actual group construction let `k` and `L` be fields in the same arbitrary
universe, with `L/k` finite Galois. Let `f : S ⟶ T` be a homomorphism of
commutative group schemes over `k`, and `j : T.toGrp ⟶ G`. The ambient `G` is
affine, smooth and locally of finite type, connected reductive; `j` is a maximal
torus, `S` is split, and the base change `T_L` is split. Put
`i = CommGroupScheme.groupHom f ≫ j`. Let `a` be a nonzero character of `S`,
with no `n • a` among the relative roots of `i` for any `n ≥ 3`. An affine group
scheme `U₂`, with homomorphism `j₂ : U₂ ⟶ G`, represents the actual subgroup
`RelativeRoot.subgroup i (2 • a)`.

Choose an actual absolute root `mu0` of the base-changed homomorphism `j_L`
whose Galois orbit equals `rootRestrictionFiber k L j f (2 • a)`. Write
`F = rootOrbitField k L j mu0`. The construction
`doubleRootFieldEquiv : Multiplicative F ≃* rationalPoints U₂` composes the
published `rootOrbitFieldWeightSpaceLinearEquiv` for `2 • a` with the inverse
of `RelativeRoot.doubleRootPointLieEquiv`. The split-torus character lattice
makes `2 • a` nonzero. The comparison lemma identifies this composition in
the Lie space, and `doubleRootFieldEquiv_smul` proves its `k`-linearity through
that comparison.

`RelativeRoot.doubleRootPointLieEquiv_act` treats any group-scheme action that
fixes the image of `S` pointwise on every test scheme. It compares the action
on represented doubled-root rational points with its differential. Its proof
identifies the represented point action with the induced root-point action,
then applies the published `representedRootPointLieEquiv_aut_apply` to the
evaluated ambient automorphism. The action differential is the differential of
that automorphism by `AutomorphicAction.targetMapLinear_basePointIso`.

Specializing to conjugation by `j`, `doubleRootFieldEquiv_act` shows that a
rational point `z` of `T` acts in the `F` coordinate by multiplication by the
actual root-orbit character value of `mu0`. This uses the published differential
action on the weight-space equivalence and injectivity of the doubled-root
comparison. It assumes that `T.toGrp` is affine over `k` and a supplied
all-test-scheme proof `hfix` that this conjugation fixes `i(S)`.
`doubleRootFieldEquiv_act_character` also assumes the underlying scheme of `T`
is affine and writes this value using the actual descended
`rootOrbitCharacter k L j mu0` evaluated after `rationalExtend`.

Now let `E/F` be any supplied separable quadratic extension.
`doubleRootTraceZeroEquiv` composes the inverse of `traceZeroScalarEquiv` with
`doubleRootFieldEquiv`, giving a multiplicative equivalence from the
multiplicative type tag of the trace-zero subgroup to `U₂(k)`. Its scalar lemma
assumes compatible `k`-algebra structures on `E` and `F`, and carries any relation
`w' = c • w` in `E` to the corresponding relation in `Lie(G)(k)`. Its action
lemma says: if the actual descended `mu0`-character value, mapped from `F` into
`E`, equals `value * conjugation F E value`, then conjugation on `U₂(k)` carries
the coordinate of `w` to that of any trace-zero `w'` satisfying
`w' = value * conjugation F E value * w`.

`HasDoubleRootTraceZeroCoordinates` records existence of one such equivalence
`second`, together with these two laws: `k`-linearity through the represented
Lie comparison, and norm-action equivariance for a supplied function
`value : T(k) → E`. Its second law quantifies all original rational points and
all trace-zero `w,w'` with the stated norm-proportionality relation. The theorem
`hasDoubleRootTraceZeroCoordinates` assumes the structural and orbit hypotheses
above, the compatible `k`-algebra tower, affineness of `T`, `hfix`, and the norm
identity between the actual descended doubled-root character and `value z`
for every `z`. It chooses a nonzero trace-zero scalar using the published
`SU3Root.exists_ne_zero_add_conjugation_eq_zero`, constructs `second`, and
applies the two composition lemmas. No scalar choice or equivalence is assumed
by this existence theorem.

The construction is valid in every characteristic, including characteristic
two, without an infinite-field or residue-field hypothesis. The quadratic
extension, the doubled-root orbit description, and the norm identity remain
explicit inputs. This module does not construct those inputs, a nonsymmetric
Heisenberg cocycle, coherent opposite coordinates, a unitary group homomorphism,
or an affine lift. In particular, it does not prove the unconditional
`QuasiSplitIndivisibleDerivativeLiftsStatement`.
