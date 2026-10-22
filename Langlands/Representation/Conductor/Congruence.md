# Congruence subgroups for conductor and newvector theory

This module constructs actual subgroups of
`Matrix.GeneralLinearGroup (Fin (n + 1)) F`. The parameter `n` is one less
than the matrix rank: `n = 0` is rank one. No representation, genericity,
or existence theorem for newvectors is assumed in these constructions.

For a commutative ring `R`, an ideal `I`, and rank `n + 1`,
`integralCongruence n I` consists of invertible matrices over `R` whose
last row reduces to `(0, ..., 0, 1)` modulo `I`. It is the inverse image
of an explicitly constructed row stabilizer under Mathlib's general
linear group homomorphism induced by `R → R/I`. The proofs that the row
stabilizer contains the identity and is closed under multiplication and
inversion are included. Entrywise membership is proved equivalent to
`g(last,j) - δ(last,j) ∈ I` for every `j`.

For a subring `O` of a field `F`, `integralSubgroup O n` is the image of
`GL_(n+1)(O)` inside `GL_(n+1)(F)`. Both the matrix and its inverse are
integral; this is stronger than requiring only integral entries of an
arbitrary invertible matrix over `F`. `congruenceSubgroup O n I` is the
image of the reduction stabilizer under the same inclusion. Injectivity
of that inclusion is proved, so subgroup membership has exactly the
specified integral representatives.

For a field with a specified `ValuativeRel`, `levelSubgroup F n a` uses
the integer ring of `ValuativeRel.valuation F` and the `a`th power of
its maximal ideal. Thus its level zero is the entire integral group:
the zeroth ideal power is the unit ideal, and reduction imposes no
condition. Higher levels give smaller subgroups. These assertions are
proved directly from ideal containment. The construction needs no
uniformizer or choice of normalization of an absolute value.

The topology is the existing Mathlib topology on the matrix general
linear group. `mem_integralSubgroup` proves that its integral image
consists exactly of matrices for which both the matrix and its inverse
have integral entries. The proof builds inverse integral matrices from
these entrywise conditions. When the subring is open, this description
expresses the integral group as a finite intersection of open entry
conditions on the matrix and its inverse. Its inclusion is therefore
an open embedding. Open ideals give open reduction stabilizers and
open congruence subgroups in the field group.

Over a compact Hausdorff integer ring, the integral general linear
group is compact. Each open reduction stabilizer is also closed, so
its image in the field group is compact. For a Mathlib
`IsNonarchimedeanLocalField F`, powers of the integer ring's maximal
ideal are open. `levelOpenSubgroup` packages each concrete level as an
`OpenSubgroup`, and `isCompact_levelOpenSubgroup` proves compactness
in its inherited topology. These constructions use the supplied
valuative and topological structures; they introduce no new topology.

## Original source and translation

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
representations du groupe lineaire*, Math. Ann. 256 (1981), 199–214,
Section 5.1, page 211, defines `K_r(0) = GL_r(O)` and, for `a > 0`,
the subgroup of integral invertible block matrices whose bottom row
is congruent to the last standard row modulo the `a`th power of the
maximal ideal. Its displayed upper-left block is also invertible over
`O`; equivalence with the row formulation follows by reduction over
the residue field and the local-ring unit criterion. The module proves
both unit conditions: `isUnit_last_entry` treats the bottom-right
entry, and `isUnit_upperLeft` treats the upper-left matrix. The latter
uses expansion along the reduced last row to identify its determinant
with the determinant of the entire reduced matrix, then lifts the unit
condition through the residue map. Together with the entrywise
membership theorem, these results give the source's positive-level
block description. At level zero no such block condition is imposed.
Rank one is included explicitly by `mem_integralCongruence_rankOne`.

- Literature ID: `jpss-1981-conductor`.
- Content SHA256:
  `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
- Retained source:
  `C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`.
- Locator: Section 5.1, page 211, theorem part (ii) and the immediately
  following level-zero convention (PDF page 13).

The reduction-stabilizer implementation is a derived algebraic
construction, valid for arbitrary ideals. The source specializes it to
powers of the maximal ideal of a nonarchimedean local field. This module
does not assert conductor existence, the newvector dimension theorem,
or the equality with an epsilon-factor exponent.
In particular, it makes no use of the erroneous essential-vector
existence proof corrected by Jacquet in 2012.

## Dependencies and review boundary

This file has no project mathematical imports. It reuses Mathlib's
`GeneralLinearGroup.map`, `Subgroup.comap`, `Subgroup.map`, ideal
quotients, valuations, and integer rings in environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1 (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
The topology argument also uses Mathlib's general linear group map
embedding, compact-unit-group instance, and openness of maximal-ideal
powers in a nonarchimedean local field. These are derived construction
obligations supporting the source's concrete subgroup, rather than
additional representation-theoretic theorems attributed to JPSS.
Worker 43 authored this module. Development compilation is distinct from
independent source review and publication.
