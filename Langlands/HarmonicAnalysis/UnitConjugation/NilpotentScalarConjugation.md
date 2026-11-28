# Scalar conjugation of nilpotent elements

`NilpotentScalarConjugationStatement` says that for a field `F`, a semisimple
`F`-algebra `A`, a nilpotent `N ∈ A` and a nonzero scalar `t ∈ F`, there is a
unit `u ∈ Aˣ` such that `u N u⁻¹ = t • N`. The field and algebra can belong to
independent universes. `nilpotentScalarConjugation` proves this statement.

The scalar conjugacy is the algebraic step used with `t²` in Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups* (1999), §3.1,
Lemma 3.2, printed p. 18. Harish-Chandra obtains a conjugator from a
Jacobson–Morozov triple. For the unit group of a semisimple associative algebra,
the proof here constructs one using complements of submodules.

## Proof

Let `T` be a nilpotent endomorphism of a semisimple left module and let `a` be a
central unit of its coefficient ring. Induct on a nilpotence exponent to find
a linear equivalence `e` with `e(T x) = a • T(e x)`, together with a complement
of `range T` on which `e` is the identity.

For the induction step, use the restriction of `T` to `P = range T`.
Induction gives `eP` on `P` fixing a complement `W` of `T(P)` in `P`.
Let `S` be the preimage of `W` under `T` viewed as a map to `P`. Decomposing
`T x` into its components in `W` and `T(P)` shows that `S + P` is the whole
module. Choose a complement `U` of `S ∩ P` in `S`. Then `U` and `P` are
complementary in the original module. Define `e` as the identity on `U` and
as `a • eP` on `P`. The desired relation on `U` follows because `T(U) ⊆ W`.
On `P` it follows from the induction hypothesis and linearity of `T`.

Apply this construction to right multiplication by `N` on the regular left
`A`-module with `a = algebraMap F A t`. Every endomorphism of that module
is right multiplication by its value at `1`. Since `e` and `e⁻¹` are
inverse, their values at `1` are inverse units. Taking `u = e⁻¹(1)`, the
relation at `1` gives `N u⁻¹ = a u⁻¹ N` and hence `u N u⁻¹ = t • N`.
