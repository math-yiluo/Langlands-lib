# Nonzero Laurent residues and descent to bilinear forms

This derived internal module supplies the algebraic residue argument needed
for the equal-rank supercuspidal L-factor proof. Its hypotheses explicitly
retain the analytic inputs.

For a normalized generator `P` of a Laurent span and each nonzero complex
point `x`, there exists a generating rational function, possibly depending on
`x`, whose denominator-cleared Laurent lift has nonzero evaluation at `x`.
The proof is by Laurent-span induction: if all
such evaluations vanished on the generating set, they would vanish on the
reciprocal generator `1/P`, whose cleared lift is `1`.

`clearedLaurentForm` evaluates the unique Laurent lift of a trilinear rational
family after multiplication by `P`. If that family includes all the generating
values, the preceding argument makes the form nonzero. If the unnormalized
family is Laurent on a test submodule, then at a root of `P` the cleared form
vanishes on that submodule: its lift is `P` times an unnormalized Laurent lift.

Apply this to the kernel of a test functional `e`. A test with `e`-value one
identifies the resulting nonzero form with `e` times a nonzero bilinear form.
If the original cleared form has simultaneous covariance and `e` is invariant
under the test action, the descended bilinear form has the same covariance.
This uses the Library's `TrilinearReduction.factor_evaluation` and `evaluate`.

The construction is general linear algebra over the published rational and
Laurent-function interfaces. It does not assert that the equal-rank zeta
family is Laurent on tests vanishing at zero, does not prove simple poles,
and does not construct a pole from a contragredient-twist equivalence.
