# Induction stages on exact finite-length K0

This internal construction descends an actual normalized induction stages
isomorphism to the existing exact finite-length Grothendieck groups. It adds
no literature assertion. The ambient group is locally compact and
nonarchimedean, the coarse Levi is closed, and the fine Levi is a subgroup
of it. The two ambient semidirect decompositions and the literal inside-Levi
decomposition are supplied, as are closedness of the two ambient radicals.
The coefficient universe is `max uG uV`, with independent `uG` and `uV`.

`leviInductionK0` pulls a representation of the ambient fine Levi back to its
literal subgroup copy in the coarse Levi and then applies normalized induction
inside the coarse Levi. Its hypotheses are finite-length preservation and
preservation of short exact sequences for that literal inner induction.

`inductionK0_comp_leviInductionK0` assumes the actual stages natural isomorphism
from fine-to-coarse induction followed by coarse-to-ambient induction to direct
fine induction. It also assumes the two preservation properties for the two
ambient inductions. It composes the preservation proofs, applies
`FiniteLengthGrothendieckGroup.map_eq_of_iso`, and expands the functor
composition using `map_comp` twice. Thus the result is equality of full
integer-linear maps on the quotient by all actual finite-length short exact
sequences, including virtual classes.

`inductionK0_comp_restrictedInductionK0` places the domain at the literal inner
fine subgroup. It composes the first equality with the inverse canonical
pullback and cancels the two pullbacks using `pullback_symm_comp`. This form
can be composed directly with literal restricted Jacquet restriction.

The stages isomorphism is an explicit input to this generic descent. No
Jacquet preservation, geometric expansion, Weyl conjugacy, sign identity or
Aubert compatibility equation is assumed or proved here. Rational
specialization must supply the actual stages isomorphism separately.
