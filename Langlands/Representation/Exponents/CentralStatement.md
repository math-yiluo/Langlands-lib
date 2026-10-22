# Central-character prerequisites for Jacquet exponents

Worker 19 defines `Langlands.CentralExponentPrerequisitesStatement`, a
conjunction of the decomposition, twisting and scalar-contragredient
propositions below. These are actual Lean propositions over published
representations and subspaces. No theorem in this file proves them.

## Objects and quantifiers

The coefficient field `R`, group `G`, and representation carrier `V` have
independent universes `uR`, `uG`, and `uV`. The coefficient field has
characteristic zero. There is no topology or finite-dimensionality assumption
on `V`, and no topology is imposed on `R`. Characters are actual
homomorphisms to `Rˣ`; their smoothness is expressed by an open kernel.

`IsCenterFinite ρ` means that every vector belongs to a finite-dimensional
subrepresentation of `ρ` restricted along `Subgroup.center G`. The witnessing
subspace may depend on the vector. Here `Module.Finite R W.toSubmodule` means finite
dimensionality because `R` is a field. The definition uses actual invariant
subspaces and does not supply characters, projections, or a decomposition.

`centralCharacterSpace ρ χ n` and `generalizedCentralCharacterSpace ρ χ`
are the existing constructions in `Langlands.Representation.Exponents.Central`.
Their membership formulas are respectively

`∀ z ∈ Z(G), (ρ(z) - χ(z) id)^n v = 0`

and

`∃ n, ∀ z ∈ Z(G), (ρ(z) - χ(z) id)^n v = 0`.

In the second formula the exponent may depend on the vector but must be
uniform over central elements. The finite space for `n = 1` is the scalar
character space. The construction already proves these identifications.

## Decomposition and finite support

`CentralCharacterDecompositionStatement` retains Casselman's ambient
locally compact Hausdorff topological group and compact-open subgroup
neighborhood basis. The latter is written explicitly: every open set
containing the identity contains a compact open subgroup. Thus no unnamed
predicate stands in for the group assumptions.

For every representation `ρ`, the first clause says that admissibility implies
center-finiteness. The existing admissibility predicate includes smoothness
and finite-dimensional fixed spaces for every open subgroup.

The second clause additionally quantifies an algebraic-closedness instance
on `R`, and assumes smoothness and center-finiteness. It asserts the internal
direct sum of the generalized spaces indexed by all central characters with
open kernel. Lean writes this as independence of the family of submodules
(`iSupIndep`) and equality of its supremum with the whole module. These are
the two conditions in Mathlib's internal-direct-sum characterization; the
canonical map sums finitely supported families of vectors. This is not an
arbitrary existence assertion for an unrelated equivalence.

If the same representation is finitely generated over the actual group
algebra `MonoidAlgebra R G` via `ρ.asModule`, the set of nonzero generalized
central-character spaces is finite. Moreover, there is **one positive integer
`n` for all smooth central characters** such that the generalized space equals
the exponent-`n` space. Neither the finite support nor the bound is assumed
in the input representation. The bound is uniform in both the central
character and the vector, which is stronger than the defining vectorwise
bound and is exactly the additional conclusion in the original.

## Character normalization

`CentralCharacterTwistStatement` uses the published action
`(twist η ρ)(g) = η(g) ρ(g)`. For every natural `n`, including zero, its
central space at `(η restricted to Z(G)) χ` has the same underlying submodule
as the original central space at `χ`, with the same exponent. It also states
the corresponding equality for generalized spaces. Equality is taken after
`toSubmodule`, because these subrepresentations have different ambient actions.

For the central-exponent equivalence, `η` must have open kernel in `G`.
That restriction makes its restriction to the center a smooth character and
ensures that multiplying or dividing by it preserves the open-kernel
condition. No openness is required for the purely algebraic subspace
equalities, and no unitarity is assumed.

`CentralCharacterContragredientStatement` assumes a smooth representation
with smooth scalar central character `χ` and concludes scalar character
`χ⁻¹` on its actual smooth contragredient. The carrier is the smooth part
of the algebraic dual, with action
`(g ℓ)(v) = ℓ(ρ(g⁻¹)v)`. This inverts the character; it does not take its
complex conjugate. Scalar central action is the hypothesis
`centralCharacterSpace ρ χ 1 = ⊤`. No reflexivity or admissibility hypothesis
is needed for this direction.

## Original source and declaration map

The retained source is W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995:

- Literature ID: `casselman-1995-admissible-representations`.
- Retained file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- SHA-256:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Printed and PDF page numbers coincide.

| Lean declaration or clause | Original location and correspondence |
| --- | --- |
| `IsCenterFinite` | Section 2.1, p.18: the definition of being finite under a subgroup, specialized to the actual center. |
| Ambient group and coefficient hypotheses | Section 2.1, opening p.18: locally compact Hausdorff group with compact-open subgroup basis, characteristic-zero field. |
| Admissible implies center-finite | Proposition 2.1.3, p.19, its center special case. The printed proof uses a finite-dimensional compact-open fixed space stable under the center. The more general closed-subgroup version is not asserted here. |
| Independent spanning family | Proposition 2.1.9(a), p.21, with the uniform spaces defined immediately before it. |
| Finite support and uniform positive bound | Proposition 2.1.9(b), p.21. Finite generation is by group translates, as defined on p.18; it is not finite dimensionality of `V`. |
| Central spaces under twisting | The twist and central-space formulas on p.21. The stated identities are derived algebraically from these formulas, not attributed to a separately numbered theorem. |
| Scalar character on the contragredient | Dual-action formula at the bottom of p.21 and smooth-dual definition at the top of p.22, applied to the scalar-character formula on p.21. This is also a direct derived consequence. |

For the twist identities, the relevant operator is
`η(z) (ρ(z) - χ(z) id)`. Its `n`th power is `η(z)^n` times the original
power, and the scalar is invertible. Thus its kernel is unchanged.
Taking the increasing union gives the generalized-space statement. For the
contragredient identity, evaluate at a vector and use
`ρ(z⁻¹) = χ(z)⁻¹ id`. These explanations establish source correspondence;
the associated Lean proofs remain separate obligations.

Casselman's proof of Proposition 2.1.9 consists of a reference to standard
facts about commuting operators on finite-dimensional spaces. This file
does not claim that the notes print a longer proof, or that a formal proof
of those facts has been supplied here. The retained 1995 edition is not
silently identified with the earlier preprint cited by Silberger 1978.

## Current Library dependencies and limits

The direct project imports are:

| Module | Used declarations |
| --- | --- |
| `Langlands.Representation.Exponents.Central` | The actual uniform central spaces and `IsCentralExponent`. |
| `Langlands.Representation.Smooth.Definitions` | `IsSmooth` and `IsAdmissible`. |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `SmoothDual` and `smoothContragredient`. |
| `Langlands.Representation.Twist.Definitions` | `twist`. |

These pairs are published in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`; the accepted central-space pair
was copied without changes into the working tree for import availability.
The other imports use pinned Mathlib's actual group-algebra action,
subrepresentations, submodule lattice, algebraic-closedness and topological
group structures. The environment is Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This family uses the **full center** of the given group. Jacquet exponents
additionally require an actual Jacquet representation and restriction to
the split component of its Levi center. Those constructions and the analytic
square-integrability and temperedness criteria are not substituted by these
central-character statements. No Jacquet exactness, cuspidal projectivity,
tempered-induction irreducibility, regular-chamber quotient theorem, or
completion of the larger task is claimed.
