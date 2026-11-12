# Integrals over `G/A` for a cocompact central subgroup (Renard IV.3.3, Remark)

Author: Worker 1222. Module
`Langlands.Representation.Compact.CocompactCentralSquareIntegrableStatements`, namespace
`Langlands.Renard.CompactRepresentation`. Statement
`CocompactCentralSquareIntegrableStatements : Prop` (universe parameters `u`, `v`); nothing is
proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, IV.3.3, the Remark after the Corollary, printed p.102 / PDF p.108. The registered
source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation:

> More generally, if `A` is a subgroup of `Z(G)` such that `Z(G)/A` is compact, one can replace
> the integrals over `G/Z(G)` by integrals over `G/A` without affecting their convergence, and
> the results obtained above are still valid.

"The results obtained above" are those of IV.3.2–IV.3.3: the Proposition and Lemma of IV.3.2
and the Lemma and Corollary of IV.3.3. For `A = Z(G)` they are the published statements
`EssentiallySquareIntegrableAdmissibleStatement`, `SquareIntegrableUnitarySemisimpleStatement`,
`SchurOrthogonalityStatement` and `CoefficientLinearIndependenceStatement` (module
`Langlands.Representation.Compact.UnitarySquareIntegrableStatements`). This module states the
Remark: the convergence claim and the four results with integrals over `G/A`.

## Reading of the Remark

The Remark replaces integrals and nothing else. The Definition of IV.3.2 is kept: the centre
`Z(G)` acts by a unitary character (condition a), and only the integral of condition b), and
the integrals of the orthogonality relations of IV.3.3, are taken over `G/A` with a Haar
measure of `G/A`. When the centre acts by a unitary character, the functions `|ℓ(π(g) x)|` and
`ℓ₁(π(g) x₁) ℓ₂(π(g⁻¹) x₂)` are invariant under `Z(G)`, so they descend to `G/A`.

## Statement

The statement quantifies over a t.d. group `G : Type u`
(`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
[TotallyDisconnectedSpace G]`, as in the published IV.3 statements), a subgroup `A` with
`[A.Normal]`, `IsClosed (A : Set G)`, `A ≤ Subgroup.center G` and
`CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))` (Renard's `Z(G)/A`
compact). It takes Borel structures and Haar measures `μZ` on `G ⧸ Subgroup.center G` and `μ`
on `G ⧸ A`, both also right invariant. This is how the published IV.3 statements express
Renard's standing assumption that `G` is unimodular with a bi-invariant Haar measure `dg*`.

It introduces three local predicates on `π : SmoothRep.{0, u, v} ℂ G`:

- `ActsBy π χ`: every `z ∈ Z(G)` acts on `π` by the scalar `χ(z)`;
- `SqIntModA π`: `ActsBy π χ` for some `χ : Z(G) →* ℂˣ` with `|χ(z)| = 1`, and for every
  smooth functional `ℓ`, every vector `x` and every `F : G ⧸ A → ℝ` with
  `F(gA) = |ℓ(π(g) x)|`, `MemLp F 2 μ`. The function `F` is characterized by its values, as
  in the published `SchurOrthogonalityStatement`; when the centre acts by a unitary character
  exactly one such `F` exists;
- `EssSqIntModA π`: `SqIntModA (π.twist ω hω)` for some smooth character `ω` of `G` (the
  published `SmoothRep.twist`).

It asserts the conjunction of:

1. (convergence) for every `π` on which `Z(G)` acts by a unitary character, every `ℓ`, `x`,
   and all `FZ : G ⧸ Z(G) → ℝ`, `FA : G ⧸ A → ℝ` with values `|ℓ(π(g) x)|`:
   `MemLp FZ 2 μZ ↔ MemLp FA 2 μ`;
2. (IV.3.2, Proposition) every irreducible `π` with `EssSqIntModA π` is admissible;
3. (IV.3.2, Lemma) every admissible `π` with `SqIntModA π` is unitarizable and semisimple;
4. (IV.3.3, Lemma) (i) for every irreducible `π` with `EssSqIntModA π` there is a real
   `d > 0` such that, for all `x₁`, `x₂`, `ℓ₁`, `ℓ₂` and every `F : G ⧸ A → ℂ` with
   `F(gA) = ℓ₁(π(g) x₁) ℓ₂(π(g⁻¹) x₂)`, `F` is `μ`-integrable and
   `∫ F dμ = ℓ₁(x₂) ℓ₂(x₁) / d`; (ii) for irreducible `π₁`, `π₂` with `EssSqIntModA`, not
   isomorphic, and on which the centre acts by the same character, every `F : G ⧸ A → ℂ` with
   `F(gA) = ℓ₁(π₁(g) x₁) ℓ₂(π₂(g⁻¹) x₂)` is integrable with integral `0`;
5. (IV.3.3, Corollary) for `π : Fin r → SmoothRep`, all irreducible with `EssSqIntModA`,
   pairwise non-isomorphic, with a common central character, and nonzero `x i`, `ℓ i`, the
   matrix coefficients `matrixCoefficient (π i).representation (ℓ i) (x i)` are linearly
   independent over `ℂ`.

Items 2–5 are the published IV.3 statements with `G/Z(G)`, `μZ` replaced by `G/A`, `μ`. The
formal degree `d` in item 4 is the one for the measure `μ` on `G/A`; it differs from the one
for `μZ` by a positive factor, which the source does not discuss.

## Faithfulness notes

- `A` is assumed closed and normal. Closedness is needed for `G/A` to be a Hausdorff locally
  compact group with a Haar measure, as the source's integrals require; a central subgroup is
  normal, and `[A.Normal]` only supplies the group structure on `G ⧸ A`.
- Irreducibility, admissibility and the remaining hypotheses of each item are exactly those of
  the corresponding published statement.
- The convergence claim of the Remark is stated for coefficient norms, which are the integrals
  whose convergence the Definition of IV.3.2 involves. The integrals of item 4 are asserted
  to converge directly.

## Remaining obligations

The proof is a separate obligation. Item 1 follows from Weil's integration formula for
`A ≤ Z(G) ≤ G`, with `Z(G)/A` compact of finite measure and the integrands invariant under
`Z(G)`. Items 2–5 then follow from the published IV.3 statements (themselves with separate
proof tasks), the integral over `G/A` being a positive multiple of the integral over `G/Z(G)`.
None of this is asserted here.

## Provenance

Source assertion: Renard 2026, IV.3.3, Remark (printed p.102 / PDF p.108), read as the
replacement of the integrals of IV.3.2–IV.3.3 by integrals over `G/A`, with the Definition of
IV.3.2 otherwise unchanged. Formal choices follow the published IV.3 statement module: Borel
Haar measures that are also right invariant on the two quotients, integrands characterized by
their values on the quotient, integrability asserted rather than assumed.
