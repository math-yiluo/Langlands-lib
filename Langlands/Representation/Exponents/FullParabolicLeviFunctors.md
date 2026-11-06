# Levi functors of a full represented parabolic

This internal supporting construction supplies the endpoint comparisons used
when an intersection parabolic in the uniqueness argument of Renard 2026,
VII.2.6 has been shown to be full. It derives these comparisons from the
published actual rational-Levi isomorphism, literal point-image semidirect
decomposition, normalized induction and Jacquet constructions, and the
trivial-subgroup coinvariant and full-subgroup induction equivalences. It
does not prove that an intersection parabolic is full.

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition, VII.2.6 theorem, uniqueness proof,
printed p.231 / PDF p.237. There the unitary Jacquet part of discrete
series forces intersection parabolics to be full, after which Jacquet
restriction and induction are replaced by the original Levi
representations. This module isolates only those endpoint replacements.

For an arbitrary field `k : Type u`, an isomorphism of group schemes has the
entire literal rational-point image. If `p : P ⟶ G` is an isomorphism and
`G` is connected reductive, every supplied matching geometric unipotent
radical `r : U ⟶ P` has trivial point image in `G`. The proof transports
reductivity to `P`, uses its trivial unipotent radical on all test schemes,
and maps this equality to rational points. No canonical choice of radical
or identity presentation is required.

The point comparison uses a field endowed with a topology and the
canonical rational-point topology on the affine ambient group. The
functor comparisons additionally assume that the field topology is
Hausdorff and use supplied locally compact and nonarchimedean group
instances on the ambient rational points.
`fullParabolicLeviPointsEquiv` identifies the points of the actual Levi,
with `leviPointTopology`, with the ambient point group. Its map is exactly
`rationalPoints.map (l ≫ p)`. The published rational-Levi theorem proves
that `l` is an isomorphism; the published `leviPointsEquiv` and the equality
of its image with the whole point group give the topological equivalence.

`fullParabolicLeviJacquetEquiv` identifies the actual normalized Jacquet
module on the Levi's own point group with the original representation
restricted along that exact point map. Its linear map sends a coinvariant
class to its original vector. Triviality of the radical identifies the
coinvariant quotient with the original carrier. Conjugation on a trivial
group is the identity, so its Haar modulus and inverse half character are
one. The actual normalized action therefore becomes the original action
of the Levi image. The companion formula computes the equivalence on
every canonical coinvariant class.

`fullParabolicLeviInductionEquiv` identifies the actual normalized
induction from the Levi with the inducing representation transported by
the inverse of `fullParabolicLeviPointsEquiv`. Its map is evaluation at
the identity. The semidirect projection of a point is the point itself
because the Levi image is the whole group. The radical is trivial, hence
the positive half character is one. The published full-subgroup induction
equivalence then applies to this precise inducing action. Smoothness of
the transported action follows from continuity of the inverse point
isomorphism.

The computation lemmas identify the forward map with evaluation at the
identity and the inverse map with the transported orbit function
`g ↦ σ(e.symm g) x`, where `e` is `fullParabolicLeviPointsEquiv`.
These are the literal maps in the equivalence, not only abstract
isomorphism-existence assertions.

The field universe `u` and coefficient-carrier universe `v` are independent.
The Jacquet carrier remains in universe `v`; normalized induction has
the published carrier universe `max u v`.
No local-field, temperedness, irreducibility, admissibility, central
character, quotient compactness, standard-parabolic, Iwahori, or ambient
unimodularity hypothesis is needed. Fullness of `p` is an explicit
hypothesis of these endpoint comparisons. This construction proves none
of the three final VII.2.6 statements and supplies no proper-intersection,
geometric-filtration, nested-Jacquet, or cone-comparison argument.

The point-image equality reuses `pointImage_eq_top_of_isIso` from
`Langlands.Representation.Exponents.IsoParabolicInduction`.
