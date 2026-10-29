# Scalar extension preserves polarization Weil alternation

`rationalPolarizationWeilAlternation` proves the exact conditional
`RationalPolarizationWeilAlternationStatement`.

The private scalar-extension helper works over a commutative ring R
and a commutative R-algebra K. Its integral function has zero diagonal
and satisfies the skew identity. The extended K-bilinear map has the
specified pure-tensor formula, with the product of the two K
coefficients. Tensor induction in both arguments extends the skew
identity to arbitrary tensors; commutativity of K exchanges the two
coefficients. A further tensor induction proves alternation: the
pure-tensor diagonal vanishes by the integral identity, and the sum
case expands into two zero diagonal terms and two mixed terms that
cancel by skew symmetry. No division by two or choice of a twist basis
is involved.

`rationalWeilAlongPolarization_isAlt` applies this helper with R equal
to Z and K equal to Q. The integral function is exactly the existing
selected integral Weil pullback. The imported
`integralWeilAlongPolarization_isAlt` supplies its alternation from
the actual `IsPolarization` hypothesis and the explicit relative finite
alternation theorem. Mathlib's `LinearMap.IsAlt.neg` supplies the
integral skew identity. The existing rational pullback pure-tensor
formula is the helper's remaining hypothesis.

`primeRationalWeilAlongPolarization_isAlt` repeats the argument with
the p-adic integers and p-adic rationals, using the imported actual
integral prime-adic alternation result and the existing prime-adic
rational pullback pure-tensor formula. The input prime has
`Fact p.Prime`.

The final theorem proves the four conclusions. The selected rational
and prime-adic branches are the two lemmas above. In the full adelic
branch, the explicit full scalar comparison supplies the finite-adele
module instances on both inputs and on the actual roots-of-unity twist;
after unfolding `LinearMap.IsAlt` to its diagonal form, the existing
identity `adelicWeilAlongHomBilinearMap_apply` rewrites each adelic
diagonal value as the selected rational diagonal value for the same
order predicate, which vanishes by the first lemma. The away branch is
the same argument with the coupled away comparison, the prime-to-m
adele module instances and `awayAdelicWeilAlongHomBilinearMap_apply`,
reducing to the selected rational pairing for orders coprime to m.

The proof is an internal scalar-extension deduction from the imported
finite-to-integral polarization alternation proof and existing
pairing formulas. It retains every hypothesis of the exact statement,
including relative finite transition and finite alternation, and works
on every test scheme over the quasi-separated base. It proves neither
of those deep relative finite theorems and asserts no nondegeneracy,
perfectness, continuity, or monodromy result.
