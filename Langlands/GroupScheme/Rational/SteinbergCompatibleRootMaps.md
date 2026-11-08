# Whole root-map compatibility from compatible root vectors

This is an internal consequence of the actual semilinear root-homomorphism
construction, its subgroup, torus, coefficient and differential laws, and
fixed-pinning uniqueness of normalized parametrizations. It makes no new
existence claim from Steinberg or Borel–Springer. The fields `k` and `K` are
arbitrary in universe `u`, with an algebra structure of `K` over `k`.

`SplitPinning.RootVectorsGaloisCompatible k K p ρ` is a Prop-valued
condition on a supplied split pinning `p` of the actual base change of an
affine `k`-group `G` and a supplied permutation action `ρ` on its simple
roots. For every `k`-algebra automorphism `σ` of `K` and simple root `a`,
it requires the actual semilinear map
`Lie.baseChangeGaloisEquiv k K G σ` to carry the pinning vector at `a`
to the pinning vector at `ρ σ a`. This condition concerns actual Lie
vectors, rather than only their weights or their one-dimensional spans.

For one supplied normalized root map `x` at `a`, the construction
`NormalizedRootParametrization.galoisNormalized` additionally requires:

* an actual commutative group `T` over `k` with a homomorphism `j` into `G`,
  an isomorphism from `p.torus` to the base change of `T`, and the commuting
  inclusion square;
* the equality carrying the character at `a` to the character at a specified
  simple root `c` under the actual character Galois representation, after that
  torus comparison;
* equality of the semilinear transport of the pinning vector at `a` with
  the pinning vector at `c`.

The constructed normalized parametrization at `c` has underlying
homomorphism exactly `x.galoisHom`. Its representation of the whole root
subgroup follows from `galoisHom_represents_root`.
Closedness is `galoisHom_isClosedSubgroup`. Its epsilon derivative is
`galoisHom_derivative` followed by the supplied pinning-vector equality.
Thus no derivative or torus law for the transported map is supplied as a
new premise. Internally, a private constructor keeps an arbitrary
homomorphism opaque. It takes its all-test scalar-descent law,
representation, closedness and transported derivative; the generic
`VectorGroup.torus_equivariant_of_scalar_descent` proves its torus law
from that scalar law, the original `x.torus_equivariant` and the supplied
torus and character comparisons. Specialization uses the already proved
`x.galoisHom_point` scalar law. A private uniqueness lemma likewise
keeps the homomorphism opaque until that specialization.

`galoisHom_eq` applies the published fixed-pinning `hom_eq` theorem to
this constructed parametrization and any supplied normalized
parametrization `y` at `c`. Consequently the entire transported
homomorphism equals `y.hom`. The lemma `point_descent_eq` rewrites the
proved all-test `galoisHom_point` identity through that equality, so it
retains every scheme test and every global scalar, including nonreduced
tests. The lemma `coefficientCurve_conjugate` rewrites the proved
`galoisHom_coefficientCurve` identity through the same equality. Its
conclusion is coefficient conjugation of the complete polynomial-valued
root map, with the additive-line variable held fixed.

Finally, `SplitPinning.rootMapsGaloisCompatible_of_rootVectors` applies
this coefficient identity to each simple root and automorphism. It
proves `RootMapsGaloisCompatible` for any supplied normalized family
under the commuting torus square, the root-character transport law and
`RootVectorsGaloisCompatible`. Compatibility of the whole family is
therefore a consequence of the actual vector and character laws and
normalization.

This unit neither constructs a compatible pinning or its vectors nor
proves the existence of normalized root maps. These existence obligations
remain, along with orbit orthogonality, cross-section geometry and the
parent quotient theorem. Finite and imperfect fields are retained, and
no global section in exceptional even type A is asserted.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
