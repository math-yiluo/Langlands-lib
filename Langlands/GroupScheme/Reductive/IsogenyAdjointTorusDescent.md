# Descent of torus conjugators to an actual adjoint torus

This module is an internal consequence of the published full-centre quotient
and its descended inner action, together with representable fppf descent. It
provides the existence step for split-isogeny uniqueness. It does not assert
the general rigidity theorem or the final existence of local conjugators.

For homomorphisms `f F : G ⟶ H` and a torus inclusion `i : T.toGrp ⟶ H`,
`TorusConjugates i f F t` means that `f(g) = t F(g) t⁻¹` on every test scheme
over the scheme supporting `t`. Every refinement of that scheme is included.
`TorusConjugates.comp` proves preservation under restriction.

For supplied actual adjoint-torus data `h : IsAdjointSplitTorusImage q i j π`,
`point_comp_eq_of_difference_central` says that torus points whose difference
lies in the full scheme-theoretic centre have equal images in the supplied
adjoint torus. The proof applies the published kernel comparison
`h.comp_eq_one_iff_mem_center` to the difference of the points, then cancels
in the group of points. The centre is never replaced by its reduced subgroup.

The main theorem `IsAdjointSplitTorusImage.exists_basePoint_of_local_conjugates`
assumes an fppf cover of the field base, a torus conjugator over each component,
and that any two conjugators over the same test scheme have central difference.
It constructs a rational point `x` of the supplied actual torus `T_ad` such that
`F` followed by the descended inner automorphism of `x ≫ j.hom.hom` equals `f`
as a group-scheme map. It makes no assertion that `x` lifts to a rational point
of `T` and imposes no smoothness condition on a centre or kernel.

The implemented proof restricts local conjugators to common test schemes and
uses the central-difference lemma to make their images compatible. A private
helper uses the subcanonical fppf topology to regard the cover as an effective
epimorphic family. Its descent map glues the underlying scheme morphisms;
joint epimorphy verifies the equation with the base structure map, producing
an actual point in the slice category. To prove the claimed group-map equality,
the proof tests every point of `G`, pulls the cover back to that test scheme,
and compares the two morphisms on this effective epimorphic family. On each
piece, the quotient square and `innerAction_act_lift` identify the descended
action with the given local conjugation. The result therefore holds on every
test scheme, including nonreduced ones.
