# Removing a prescribed residue-field conjugator

Worker 648.

These are internal transport consequences of the pointed smooth-group lift,
the published `Descent.pullbackComparison` and its projection and naturality
laws, and the published `baseChange_innerIso_hom` and `innerIso_hom_comp`.
No external mathematical assertion is introduced.

Let `G` be a group scheme over an arbitrary scheme `S`, let `s` be a point
of `S`, and let `g₀` be a specified point of the actual residue fibre
`G_κ(s)`. Suppose `d : PointedEtaleGroupPointData G s g₀` supplies a pointed
étale neighbourhood `p : U → S`, a residue point `b : Spec κ(s) → U`, and
a section `g` of `G_U` recovering `g₀`.

`PointedEtaleGroupPointData.point_pullbackComparison` proves that pulling `g`
back along `b` and applying the canonical comparison from the iterated
pullback to `G_κ(s)` gives exactly `g₀`. Its proof projects to the original
group and applies the recovery equation in `d`.

`PointedEtaleGroupPointData.innerIso_pullbackComparison` proves that inner
conjugation by `g`, pulled back along `b`, agrees under that comparison with
inner conjugation by `g₀`. It uses preservation of inner automorphisms by
base change and by group-scheme homomorphisms.

For arbitrary group-scheme homomorphisms `i : P → G` and `j : Q → G`,
`PointedEtaleGroupPointData.range_baseChange_conjugated_eq` shows that if
conjugation by `g₀` identifies their residue-fibre ranges on every test
scheme, then the conjugate of `i_U` by `g` and `j_U` have equal ranges after
pullback along `b`. The proof transports both ranges through the ambient
pullback comparison, uses its naturality and the inner-automorphism
equation, and removes the isomorphic source presentations.

`PointedEtaleConjugatorData i j g₀` extends the pointed group-point data
with that specialized equality in its field `ranges_eq`. The constructor
`pointedEtaleConjugator i j g₀ h` assumes that the structure morphism of
`G` is smooth and that `h` is the residue-fibre conjugacy equality. It
constructs the pointed lift using `pointedEtaleGroupPoint`, then fills
`ranges_eq` with `range_baseChange_conjugated_eq`. Thus it supplies actual
neighbourhood and group-point data together with the reduction to equality
over `b`.

The equality is stated over the supplied field-valued point `b`; it makes
no claim identifying its field with the intrinsic residue field of its
image point in `U`. Neither parabolicity nor reductivity is required for
these transport lemmas or for the constructor; the constructor requires
only smoothness of `G`.
