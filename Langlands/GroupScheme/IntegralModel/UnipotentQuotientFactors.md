# Integral opposite-cell factors in a unipotent quotient kernel

This internal supporting result is derived from the published integral
quotient-cell lifting theorem and the trivial intersection of opposite dynamic
unipotent and parabolic functors. It is a step toward the full upstairs radical
preimage formula, and asserts no building or root-generation theorem.

`quotientReductionKernelPoints M q` is the image under the actual generic
integral-point map of the inverse image of the rational-point kernel of `q`
under actual reduction. Its membership lemma retains an integral section,
its quotient reduction being one, and its specified generic image. This
definition and membership lemma need only a local-domain integral model;
they have no smoothness or connectedness hypotheses.

Let M be a smooth integral model over a local domain with connected special
fibre. Given an integral cocharacter and representatives of its opposite
unipotent and parabolic functors, suppose a smooth surjective special-fibre
quotient has connected unipotent kernel. Representatives of the corresponding
quotient dynamic functors are explicit inputs. Every integral section killed
by the quotient after reduction is the product of actual integral sections
of the two original factor schemes. Both ambient factor sections are killed
by the quotient after reduction.

The proof lifts the unit coordinates in the quotient cell using
`oppositeCell_section_lifts_iff_quotient_reduction`. Base change and functoriality
place the reductions of the two factors in the opposite dynamic unipotent and
parabolic of the quotient. Their product is the identity. The opposite
intersection is trivial, so both quotient images are the identity individually.
The proof retains the original section and its actual reduction throughout.

`quotientReductionKernelPoints_eq_sup_dynamic` then identifies the full
generic subgroup with the supremum of its intersections with the generic
opposite dynamic unipotent and parabolic subgroups. Base change of the integral
representatives, followed by the model's generic identification, places each
integral factor in the corresponding generic dynamic subgroup. The reverse
inclusion is immediate since both intersections are subgroups of the original
kernel image. This equality has the same smoothness, connectedness,
representability and quotient hypotheses as the factorization lemma; it adds
no assumption that a prescribed generic factorization is already integral.
