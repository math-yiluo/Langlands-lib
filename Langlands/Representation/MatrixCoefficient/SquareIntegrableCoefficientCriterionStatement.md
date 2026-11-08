# One square-integrable coefficient suffices: statement

Author: Worker 6. Module `Langlands.Representation.MatrixCoefficient.SquareIntegrableCoefficientCriterionStatement`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.3.2, Remark after the Definition, printed p.100 / PDF p.106. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## The source

In IV.3, `G` is a t.d. group with centre `Z(G)` and a Haar measure `dg*` on `G / Z(G)`. A smooth representation `(π, V)` is square-integrable modulo the centre if `Z(G)` acts by a unitary character `χ` and every matrix coefficient `φ_{v,λ}(g) = λ(π(g) v)` lies in `L²(G, χ, dg*)`, i.e. `∫_{G/Z(G)} |φ_{v,λ}|² dg* < ∞`. The Remark reads: let `(π, V)` be an irreducible smooth representation with a unitary central character; for `π` to be square-integrable modulo the centre, it suffices that one nonzero matrix coefficient of `π` be square-integrable modulo the centre. This fails without irreducibility. Renard does not use the result and leaves its proof to the reader.

## The Lean statement

`SquareIntegrableCoefficientCriterionStatement` quantifies over:

- a group `G` with a topology making it a locally compact, Hausdorff, totally disconnected topological group;
- a Borel measurable structure on `G ⧸ Subgroup.center G` and a Haar measure `μ` on it that is also right invariant, as in Worker 6's companion IV.3 statements (module `UnitarySquareIntegrableStatements`);
- `π : SmoothRep.{0, u, v} ℂ G`, irreducible and admissible;
- `c : UnitaryCentralCharacter π.representation`, the published unitary central character (a character of `Z(G)` with open kernel and values of norm one by which `Z(G)` acts).

Its hypothesis is that some smooth functional `ℓ` and vector `x` have `matrixCoefficient π.representation ℓ x ≠ 0` and `MemLp (c.coefficientNorm ℓ x) 2 μ`. The published `coefficientNorm` is the function `gZ(G) ↦ |ℓ(π(g) x)|` on `G / Z(G)`, which is well defined because the central character is unitary. The conclusion is the published `IsSquareIntegrableModCenter π.representation μ`: `π` is admissible and, for some unitary central character, every smooth matrix coefficient is square-integrable on `G / Z(G)`.

## The admissibility hypothesis

The source assumes only irreducibility. The Lean statement also assumes admissibility, for two reasons.

- The published `IsSquareIntegrableModCenter` includes admissibility. By IV.3.2, Proposition, an irreducible representation that is square-integrable modulo the centre in Renard's sense is automatically admissible, so the published predicate agrees with Renard's for irreducible representations.
- The argument for all coefficients uses that the smooth dual of an irreducible admissible representation is irreducible. Right translates of `x` span `V`, so `φ_{v,ℓ}` is square-integrable for every `v`, by right invariance of `μ`. Left translates of `ℓ` span `Ṽ` because `Ṽ` is irreducible, so `φ_{v,λ}` is square-integrable for every smooth `λ`, by left invariance. For an irreducible representation that is not admissible, the dual need not be irreducible, and this route does not apply.

For the groups of the book the hypothesis costs nothing. Irreducible smooth representations of `p`-adic reductive groups are admissible.

## Remarks

- The proof is not formalized here.
- The remark at the end of IV.3.3, replacing `G / Z(G)` by `G / A` for a subgroup `A ⊂ Z(G)` with `Z(G) / A` compact, is not restated here. The published Schur orthogonality and formal degree of `HarishChandraSchwartz/SchurOrthogonality` are formulated for a central subgroup `A` and a measure on `G / A`.
