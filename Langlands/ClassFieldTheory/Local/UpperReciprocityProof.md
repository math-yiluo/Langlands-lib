# Finite upper ramification compatibility of local reciprocity

The theorem `Langlands.LocalClassField.finiteUpperReciprocityTheorems` proves
exactly the published proposition
`Langlands.LocalClassField.FiniteUpperReciprocityTheorems.{u}`. It has no
hypotheses and retains its unrestricted universe `u`.

The implemented proof applies the published reduction
`finiteUpperReciprocityTheorems_of_normCardinality` to the published arithmetic
theorem `NormUnitImage.finiteAbelianNormUnitImageCardinality`, specializing its
independent field universes to `u, u`. This specialization covers the actual
finite abelian intermediate extensions in the chosen algebraic closure of a
base field in universe `u`.

The arithmetic theorem computes the order of the image of every unit level
`U_F^{⌈a⌉₊}` in the determinant-norm quotient for every real `a ≥ 0`, including
zero, using the actual upper ramification subgroup. Its independent proof uses
prime-degree norm computations, Galois towers, induction on the extension
degree and the finite norm index. It transports both filtrations to arbitrary
supplied topological data.

The reduction first obtains literal real unit-image equalities. For the upper
subgroup `H` at a fixed level, Herbrand restriction compatibility makes the upper
group of its fixed subextension trivial. The arithmetic theorem then puts the
corresponding units in that subextension's norm subgroup. Exact reciprocity
kernels and restriction compatibility put their images in `H`. Applying the
arithmetic theorem to the original extension and using the finite norm-residue
equivalence gives equal orders, hence equality of these finite subgroups.

The elementary reduction in `UpperReciprocityReduction` then supplies all five
clauses of the target:

- Integer unit-image equality follows by specialization of the real level.
- Real unit-image equality holds at every nonnegative real level.
- The norm/upper-level criterion uses unconditional reciprocity existence and
  the exact norm kernel, so its conclusion has no supplied reciprocity map.
- The finite-character conductor bound is equivalent to triviality on the
  upper group by the least-unit-level conductor criterion.
- A successor conductor is characterized by nontriviality at the integer
  level and triviality at every later real level, using the natural ceiling.

The target still quantifies every prime, base field, supplied base and extension
topological datum, compatible extension realization and geometric profinite
reciprocity candidate. Its subgroup equalities are literal images. The last
break criterion includes the tame endpoint at zero.

This module is an internal composition of the two published theorems named
above. The source interpretation of the target and arithmetic input is recorded
in `UpperReciprocityStatement.md` and `NormUnitImageCardinality.md`; the
implemented fixed-field and conductor arguments are recorded in
`UpperReciprocityNormReduction.md` and `UpperReciprocityReduction.md`. This proof
adds no further arithmetic premise or source assertion.
