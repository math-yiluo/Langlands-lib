# Cuspidal tensor products and association of their factors

Author: Worker 55.

This module states two interfaces between the published external tensor product,
actual product Levis, and multisets of supercuspidal classes. It contains only
Prop-valued definitions. Neither interface nor uniqueness of supercuspidal
support is proved here.

`Langlands.CuspidalSupport.GLCuspidalTensorStatement` says that for every prime
p, p-adic field F, compatible topological realization T, positive rank n, and
ordered positive block shape B of n, the external tensor product of any family
of irreducible supercuspidal representations of the blocks is irreducible and
Levi-cuspidal. The factors are actual `GeneralLinear.SupercuspidalRep` objects,
whose defining property already includes irreducibility, admissibility and
vanishing of coinvariants for every proper block radical and its conjugates.
The product is exactly `FiniteTensor.externalSmoothObject`, with the product
Levi action on `PiTensorProduct ℂ`; `IsLeviCuspidal` is the existing admissible
standard-refinement vanishing predicate. These are conclusions about existing
objects, not extra fields or assumed properties of the tensor product.

`Langlands.CuspidalSupport.GLCuspidalTensorAssociationStatement` states the
following implication. Choose two finite families of cuspidal data with equal
positive total rank, together with actual supercuspidal representatives of
every class. If their external tensor products are associated in the published
sense `RepresentationsAssociated`, the multisets of cuspidal data are equal.
Association uses an actual coordinate permutation matrix conjugating the
embedded source Levi onto the target Levi and an actual intertwining
equivalence after transport. Equality is equality in `Multiset CuspidalDatum`,
so both ranks and isomorphism classes, with all multiplicities, are retained.
No common constituent or induction hypothesis occurs in this statement.
Only this direction of the permutation criterion is stated.

The aggregate `GLCuspidalTensorInterfacesStatement` is the conjunction of these
two closed propositions. Each component is also a separate closed proposition
target, so the two proofs can be reviewed independently. The field universe
`uF` and factor carrier universe `uV` are independent. Both families in the
association statement use `Type uV`, as does the multiset support definition.
There is no finite-dimensionality hypothesis, universe resizing assumption,
or choice of a special representative. Positive total rank excludes the empty
family in the applications; the propositions retain arbitrary finite family
lengths and require only the stated rank sums.

## Source and derived formulation

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered source
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original printed pages 446–448 (PDF pages 7–9) were read for this module.
No errata note for this source was present in the available public notes.

Section 2.2, page 446, identifies a standard GL Levi with the product of its
blocks and its standard subgroups with refinements. Section 2.4 defines
cuspidality by admissibility and vanishing Jacquet modules for all proper
standard subgroups. Example 2.7, page 447, treats the external tensor product
of irreducible block representations as an irreducible representation of the
product Levi and states that association is equivalent to equality of the
families up to permutation. The second proposition is the forward direction
of that example, restricted to supercuspidal factors and expressed by equality
of multisets of the existing quotient classes. The representation transport
uses the convention from section 2.6 on the same page.

The first proposition is a derived interface rather than a separately numbered
source theorem. Its irreducibility assertion is the tensor-product assertion
used in Example 2.7. Its cuspidality assertion specializes the standard-subgroup
test in sections 2.2 and 2.4 to products of supercuspidal factors. Proving it
requires admissibility of finite external products and the actual comparison
between their refinement coinvariants and the factor coinvariants. At a proper
refinement at least one block has a proper Jacquet quotient, which vanishes;
the tensor product quotient therefore vanishes. This explains the intended
mathematical correspondence, but none of these steps is supplied as a proof
or assumed as a hypothesis here.

## Role in support uniqueness

The existing `CuspidalInductionAssociationTheorem` (BZ77 Theorem 2.9(a),
page 448) turns a common irreducible subquotient of two normalized inductions
of irreducible Levi-cuspidal representations into association. The first
interface supplies those input properties for the block tensors; the second
turns the resulting association into equality of supports. This module does
not assume or prove Theorem 2.9(a). It also supplies no exhaustion theorem
saying that every irreducible Levi representation is a tensor product.

All imported Lean/Markdown pairs are unchanged. No duplicate tensor, induction,
association, supercuspidality, or support relation is introduced.
