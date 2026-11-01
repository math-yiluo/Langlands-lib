# Whole-Levi conjugacy on exact finite-length Grothendieck groups

Author: Worker 320.

`Langlands.Parabolic.normalizedConjugateInductionK0` composes the actual
inverse-conjugation transport from the product Levi of `B` to that of `C`
with actual normalized parabolic induction from `C` to `GL_n`. The input
includes a permutation `w` with the published whole-Levi conjugacy predicate
`ConjugatesLevi B C w`. Transport is the literal existing `transportFunctor`,
whose action pulls back through inverse conjugation, and induction uses
upper block parabolics, positive half-modulus covariance and right translation.

The map's domain is `B.FiniteLengthGrothendieckGroup.{uV,uF} F.Carrier` and
its codomain is `GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier`.
Both are full exact quotients of actual smooth complex representations of
finite group-algebra length; all actual short exact relations, including
nonsplit ones, are retained. The supplied prime, p-adic field and topology
are arbitrary. Field and carrier universes are independent, with carriers
in `Type (max uF uV)`, and every rank, including zero, is covered.

`normalizedInductionK0_comp_leviTransport` proves that this map equals
`normalizedInductionK0 F T B` on every virtual class. The proof reduces to
actual finite-length object generators. It takes the literal transported
object and both actual induced objects, supplies their finite-length
witnesses from the published preservation theorems, and applies the
published all-rank `wholeLeviInductionConjugacy` with the identity
representation equivalence to the transported object. The supporting
`Smooth/JordanHolderGrothendieck` helper turns that actual composition-factor
matching into equality of exact classes. Explicitly instantiated transport
and induction generator formulas then identify the two maps.

This is an internal derivation from those existing actual constructions and
proofs. It adds no preservation, admissibility, irreducibility, tensor
factorization or theorem-valued hypothesis. The theorem asserts equality of
induced classes; it does not construct an equivalence of the induced
representations or a splitting. It supplies an algebraic prerequisite for
coefficient regrouping and proves no Aubert identity or analytic segment
classification.
