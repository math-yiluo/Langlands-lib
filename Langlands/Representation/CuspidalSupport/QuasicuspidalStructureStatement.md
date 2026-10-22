# Quasicuspidal structure on actual product Levis

Author: Worker 14. These proposition definitions state the subquotient
observation and parts (a)-(c) of Bernstein–Zelevinsky 1977, section 2.4,
specialized to standard product Levis of general linear groups. They assert
no proof of that theorem and assume no theorem truth as data.

The aggregate `PadicLeviQuasicuspidalStructureTheorems` quantifies over every
prime p, every actual finite extension F of the p-adic field, every compatible
topological realization T, every positive total rank n, and every ordered
positive block shape B. The group is the actual product `B.Levi F.Carrier`.
Representations are complex smooth representations with arbitrary carrier
in the specified universe; there is no finite-dimensionality or unitarity
assumption. The product topology comes from T. A standard subgroup of this
product Levi is described by refining each block, as in BZ77 section 2.2.

`IsLeviQuasicuspidal` tests vanishing of the actual Jacquet quotient for every
proper standard refinement. `IsLeviCuspidal` adds admissibility, including
smoothness. The vanishing predicate is independent of the normalized action
on the quotient because normalization changes only the action.

- `LeviQuasicuspidalSubquotientTheorem` says that every actual smooth
  subquotient of a quasicuspidal representation is quasicuspidal. No
  admissibility or finite length is imposed.
- `LeviQuasicuspidalDecompositionTheorem` chooses two invariant subspaces
  S and Q of A. Their underlying submodules have zero intersection and sum
  equal to A, through Mathlib's `IsCompl`. The restriction to S is
  quasicuspidal, and every quasicuspidal subquotient of the restriction to Q
  has a subsingleton carrier. This expresses the source's internal direct
  sum and its full subquotient condition. It does not require a chosen
  direct-sum isomorphism or assume semisimplicity.
- `LeviCuspidalConstituentTheorem` requires A to be admissible and D to be
  an irreducible cuspidal subquotient. It concludes the existence of an
  injective equivariant map from D to A and a surjective equivariant map
  from A to D. D is an actual representation, not a label for an
  isomorphism class.
- `LeviCuspidalContragredientTheorem` states that the smooth contragredient
  of a cuspidal representation is cuspidal. The contragredient is the
  smooth subspace of the full algebraic dual, with inverse action.
  Irreducibility is not assumed.

`SmoothRep.IsSubquotient` uses an invariant submodule followed by a quotient
by one of its invariant submodules, and an actual isomorphism to D.
Thus the occurrence conditions refer to the published representation
category and its actual module constructions.

## Original source and specialization

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), section 2.4, printed pages 446-447 / PDF pages 7-8.
Source ID: `bernstein-zelevinsky-1977-induced-i`; original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original section was read directly, including its retained page text
on 2026-10-20.

The observation preceding the theorem gives stability under subquotients
from exactness of the Jacquet functors. Parts (a), (b), and (c) give the
other three assertions. Section 2.1 sets the smooth complex representation
context over a locally compact nonarchimedean field. Section 2.2 identifies
standard subgroups of GL_n and of its product Levis with ordered partitions
and their refinements. The specialization therefore applies the general
reductive theorem to these actual product groups. It restricts the fields
to finite extensions of p-adic fields; it does not claim the full
nonarchimedean generality.

BZ77 cites its reference [1], chapter II, for the GL_n proofs of parts
(a)-(c), and says the general proofs are similar. That cited proof route
remains a future proof-source obligation. No proof is imported from a
paraphrase of BZ77.

## Scope and dependencies

The pair uses `CuspidalSupport.LeviDefinitions`, the canonical smooth
category with its actual subquotients, the smooth contragredient, and the
published p-adic block topologies.

Section 2.4(d), which rules out a quasicuspidal summand of induction from a
proper standard subgroup, will be stated with the normalized induction
family. The present aggregate deliberately names the structure subfamily;
it does not claim to cover that remaining induction assertion. All four
theorem proofs remain separate obligations.
