# Prescribed split-torus lifts through homomorphisms preserving maximal tori

Worker 184. This is an internal field-group deduction from the published
maximal-torus extension and no-proper-parabolic containment results. Its
purpose is to supply the algebraic residue-torus step once the actual
comparison homomorphism, its preservation of maximal tori and the target's
rational parabolic property have been established.

For any field `k : Type u`, let `H` be an affine group scheme locally of
finite type over `k`, let `Q` be connected reductive, and let
`q : H → Q` be a homomorphism. Assume:

* Every maximal torus `i : T.toGrp → H` has `i ≫ q` maximal in `Q`,
  with exactly the same source.
* Every rational parabolic subgroup embedding `p : P → Q` is an
  isomorphism.

For every prescribed maximal split torus `s : S.toGrp → Q` and every
maximal torus `i : T.toGrp → H`, the proposition
`MaximalTorusImageSplitLiftStatement.{u}` gives a commutative-group-scheme
homomorphism `f : S → T` such that:

* `(groupHom f ≫ i) ≫ q = s` as actual morphisms.
* `groupHom f` is a maximal split torus in `T`.
* `groupHom f ≫ i` is a maximal split torus in `H`.

The statement also supplies an original-field `T`, `i` and `f` with these
properties. There is no perfectness, characteristic, cardinality or
local-field assumption. The source group `H` need not be smooth or
connected. No quotient or unipotent-kernel property of `q` is assumed.
The source of the lifted split torus is precisely the supplied `S`.

The helper `IsClosedSubgroup.comp_of_maximalTorus_images` uses only the
affine, locally finite type hypotheses on `H` and the maximal-torus image
premise; the target is an arbitrary group scheme. It proves that every
closed torus has a closed composite. The published
`exists_maximalTorus_extension_of_finiteType` factors the closed torus
`i` as `a ≫ j` for a maximal torus `j`. The factor `a` is closed by
`IsClosedSubgroup.of_comp`, since `j` and `i` are closed. Composing `a`
with the closed maximal torus `j ≫ q` proves the required closedness.

The helper `IsMaximalSplitTorus.of_comp_of_maximalTorus_images` assumes
the original torus map is closed and its composite is maximal split.
For each proposed closed split overtorus in `H`, the preceding helper
makes its composite closed in the target. Target maximality then makes
the original factor map an isomorphism, proving source maximality. It
does not infer closedness of the original map from its composite.

For `IsMaximalSplitTorus.exists_commFactor_of_maximalTorus_images`, the
preservation premise makes `i ≫ q` maximal in `Q`. The published
`IsMaximalSplitTorus.exists_commFactor_of_noProperParabolic` factors the
prescribed `s` through this torus, and gives maximal splitness of the
factor in `T`. Composing its closed inclusion with `i` gives a closed
map into `H`. The preceding reflection helper proves this composite is
maximal split in `H`, since its further composite is exactly `s`.

The existential helper
`IsMaximalSplitTorus.exists_maximalTorus_commFactor_of_maximalTorus_images`
uses `TorusExistence.exists_closedTorus` to obtain the trivial closed
torus, then `exists_maximalTorus_extension_of_finiteType` to extend it
to a maximal torus. Affineness supplies the separatedness needed for
the trivial closed torus. This avoids imposing smoothness or connectedness
on `H`. The theorem `maximalTorusImageSplitLift` assembles the two clauses.

The direct published inputs are `Torus.ExistenceProof`,
`Rational.MaximalTorusFiniteType` and
`Rational.NoProperParabolicSplitTorusContainment`. Their cited helpers
provide the existence, extension, central split-torus factorization and
closed-subgroup composition steps used above.

The preservation and rational parabolic premises remain explicit.
This result constructs no building or integral model comparison,
valuation-ring torus lift or special apartment. Applying it to the
prescribed-point problem still requires the actual special-fibre
homomorphism and verification of these premises. In particular, it
does not prove `UnramifiedFixedPointSplitTorusStatement`.
