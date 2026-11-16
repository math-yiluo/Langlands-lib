# Affine fppf images of relative tori

This is an internal deduction from the Library's group-scheme descent,
field-torus image and commutative reductivity results. It introduces no new
source-transcribed statement or assumed quotient.

All declarations work in every universe. Write `q : G ⟶ Q` for an actual
homomorphism of group schemes over a scheme `S`. Throughout, its underlying
scheme map is flat, surjective and locally of finite presentation. These are
the fppf hypotheses; quasi-compactness of `q` is not required.

`smooth_target_of_surjective_flat_hom_overBase` proves that if `G` is smooth
over `S`, then `Q` is smooth over `S`, without a field or affineness assumption.
The proof first descends local finite presentation and flatness of the
structure map from the composite with `q`. For every point of `S`, it then
base changes `q` to the actual residue field. The Library's
`smooth_target_of_surjective_flat_hom` proves smoothness of that fibre
target, and Mathlib's smooth-fibre criterion proves smoothness over `S`.

`isCommMonObj_target_of_fppfHom` proves that `Q` is commutative if `G` is
commutative. The fppf homomorphism induces an epimorphism on the product of
two copies of its underlying object over `S`. Cancel that epimorphism in
the desired multiplication/braiding equality; naturality, homomorphic
compatibility with multiplication, and commutativity of `G` give the
equality. This is an equality of morphisms over `S`, so the resulting
commutativity applies on all test schemes.

`commGroupSchemeTargetOfFppfHom q` packages the same actual target `Q` with
this descended commutative group law. Its underlying group scheme is
definitionally `Q`, as recorded by
`commGroupSchemeTargetOfFppfHom_toGrp`.

For a field `k`, `Langlands.GroupScheme.IsTorus.of_fppfHom` additionally
assumes that `Q` is affine over `Spec k` and that `G` is a torus in the
field-splitting sense. It proves that `Q` is a torus. Choose a splitting
field for `G` and base change the actual homomorphism. The smooth-target
theorem makes the target smooth and hence reduced over that field.
Surjectivity makes the map dominant, and reducedness upgrades dominance to
scheme-theoretic dominance. The Library's
`IsSplitTorus.of_schematicallyDominant_hom` makes the target a split torus.
That same field therefore supplies the required torus witness for `Q`.

`Langlands.GroupScheme.RelativeTorus.IsTorus.of_fppfHom` works over an
arbitrary scheme `S`. It assumes that `G` is a relative torus and that `Q`
is affine over `S`, and proves that `Q` is a relative torus. First give the
actual target its descended commutative law. It is smooth by the new
arbitrary-base smooth-target result and affine by the displayed
hypothesis. On each geometric fibre, apply the field torus-image result
to the actual base-changed map. A torus over that field is connected
reductive and in particular pseudo-reductive. These fibre conclusions give
relative reductivity of the commutative target. The Library's
`relativeTorus_of_commutative_reductive` then gives the claimed relative
torus structure.

The affine-target assumption is explicit in both torus-image results.
These results do not construct a quotient, assert that arbitrary target
groups are affine, or give an induced-torus presentation. In particular,
being a relative torus alone does not identify the target with a finite
étale Weil restriction of the multiplicative group.
