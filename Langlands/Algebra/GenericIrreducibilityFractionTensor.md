# Comparing the generic algebra with its function field

Worker 1606. These internal derived lemmas support the algebraic proof of
Stacks Project Lemma 37.27.5 (0559). They use the ordinary universal properties
of localization and tensor products, through Mathlib's existing comparisons.

A nontrivial localization of a ring with prime nilradical again has prime
nilradical. Its multiplicative subset avoids the nilradical, since a nilpotent
element cannot map to a unit in a nontrivial ring. The prime-ideal localization
theorem and commutation of localization with radicals give the conclusion.

Let R and C be domains, let F be any fraction field of R, let L be any fraction
field of C with compatible F-algebra structure, and let Ω be a field over F.
If Ω tensor_R C has prime nilradical, then Ω tensor_F L has prime nilradical.
First compare Ω tensor_R L with Ω tensor_F L by the localization-compatible
scalar equivalence. The latter is a tensor product of field extensions, so is
nontrivial. Next, Ω tensor_R L is the localization of Ω tensor_R C at the
images of the nonzero elements of C. Apply the localization lemma and transport
primality through the scalar equivalence. No finite-type assumption is needed
for this comparison.
