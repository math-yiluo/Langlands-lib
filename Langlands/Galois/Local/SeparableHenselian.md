# Simple Hensel lifts in the actual separable inertia fixed field

Worker 706 and Worker 972.

This derived auxiliary unit constructs `fixedFieldHenselRoot`, a chosen root
of a monic polynomial with a specified simple residue root in the actual
`fixedFieldIntegers F`. Its result type contains both the root equation and
the condition that the root differs from the approximate root by an element
of the actual maximal ideal. The companion theorem
`fixedFieldIntegersIsHenselian` proves the existing
`FixedFieldIntegersIsHenselian F` proposition without additional hypotheses.
The full five-conclusion `SeparableUnramifiedArithmeticStatement` remains a
separate proof obligation.

The field `F : Type u` has exactly the supplied field, valuation relation,
topology and nonarchimedean local field structures of the arithmetic target.
The file uses the published choices of base norm, ultrametric and
completeness instances to refer to the published spectral constructions;
it adds no assumptions on the inertia fixed field. The theorem and root
construction are characteristic-uniform and valid in arbitrary universe `u`.

The generic lemmas `sepClosed_hensel_aux` and `sepClosed_henselian` originate
in Worker 972's shared task draft, revision 1, for task
991bd3f6-103a-4fbb-9cda-a9df4df94581. They prove that any valuation subring
of any separably closed field is Henselian. The argument is strong induction
on the degree of a monic polynomial. A unit derivative value implies that
the derivative polynomial is nonzero. If the polynomial is irreducible,
Gauss's lemma over the integrally closed valuation ring gives an irreducible
polynomial over the fraction field. Its nonzero derivative makes it
separable, so separable closedness forces degree one and gives an explicit
root. Otherwise a factorization into nonunits can be normalized to two
monic factors of positive smaller degree. Primality of the maximal ideal
selects a factor that vanishes at the residue root. The product derivative
and its unit value force the derivative of this factor to be a unit there,
so induction produces the required root and congruence.

For the actual fixed field, write `A = sepClosureIntegers F` and
`B = fixedFieldIntegers F`, with their published local inclusion
`fixedFieldIntegerInclusion F`. Map a monic polynomial and its approximate
root from `B` into `A`. The inclusion preserves units and sends the maximal
ideal into the maximal ideal, so the generic Hensel theorem gives a root
`a` in `A` in the prescribed residue class. Evaluating the derivative in the
residue field shows it remains a unit at `a`.

Every inertia automorphism fixes the polynomial's coefficients because they
come from `B`. It sends `a` to another root and preserves its residue by the
published characterization `mem_separableInertia_iff`. Mathlib's
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` then shows that `a` is
fixed by every inertia automorphism. Thus it lies in the actual
`inertiaFixedField F`, and its existing valuation bound places it in the
actual ring `B`. Injectivity of the inclusion reflects the polynomial's
root equation; locality reflects the required maximal-ideal condition.
These witnesses prove `fixedFieldIntegersIsHenselian`. Classical choice
then gives the data-valued `fixedFieldHenselRoot` with its stated
specification.

This proof uses the unchanged published definitions of the actual field,
valuation ring, integer inclusion and inertia action, together with
Mathlib's polynomial, valuation-ring, separable-closedness and simple-root
uniqueness results. It assumes no finite-unramified maximality theorem or
value-attainment premise, and uses no completeness or local compactness of
the infinite inertia fixed field.
