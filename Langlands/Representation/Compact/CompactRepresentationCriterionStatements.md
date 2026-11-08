# Compact representations: statements

Author: Worker 6. Module `Langlands.Representation.Compact.CompactRepresentationCriterionStatements`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.3, printed pp.89–90 / PDF pp.95–96: Definition, Theorem, Proposition and Lemma. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Throughout IV.1.3 `G` is a unimodular t.d. group.

- **Definition.** A smooth representation `(π, V)` is compact if, for every `v ∈ V` and every compact open subgroup `K`, the function `f_{K,v} : G → V, g ↦ π(e_K) π(g⁻¹) v` has compact support.
- **Theorem.** A smooth representation is compact if and only if all its matrix coefficients `φ_{v,λ}(g) = λ(π(g) v)`, `v ∈ V`, `λ ∈ Ṽ`, have compact support.
- **Proposition.** Every compact representation of finite type is admissible.
- **Lemma.** If `G` is countable at infinity and has a compact representation, then the centre of `G` is compact. In the proof the representation is nonzero; it is replaced by an irreducible subquotient, whose central character then forces the centre into the support of some `f_{K,v}`.

## The Lean statements

The module is a statement unit: nothing is proved. In all three statements `G : Type u` has `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`, i.e. `G` is a t.d. group. Smooth representations are the published `SmoothRep.{0, u, v} ℂ G`. "All smooth matrix coefficients have compact support" is the published predicate `HasCompactSmoothDualCoefficients π.representation`: for every vector `v` and every linear functional `ℓ` that is smooth for the dual action (Renard's `Ṽ`), `g ↦ ℓ(π(g) v)` has compact support.

- `CompactRepresentationCoefficientCriterionStatement` (Theorem): with a Borel structure and a Haar measure `μ` on `G`, for every smooth `π`,
  `(∀ K hK x, HasCompactSupport (fun g => Hecke.fixedProjection μ π.representation π.isSmooth K hK (π.representation g⁻¹ x))) ↔ HasCompactSmoothDualCoefficients π.representation`.
  Here `K` ranges over open subgroups with `hK : IsCompact (K : Set G)`. The published `Hecke.fixedProjection` is the action of the normalized indicator `e_K` of `K`, with values in the `K`-fixed vectors. So the left side is Renard's definition of a compact representation, written out. The normalized indicator function `μ(K)⁻¹ 1_K` itself depends on `μ`: replacing `μ` by `2μ` halves it. Its integrated action on smooth vectors does not, since it is the average of `π(k)` over `K` for the normalized Haar measure of `K` (Renard II.3.11–II.3.12, III.1.3–III.1.5). Hence the left side does not depend on `μ`.
- `CompactFiniteTypeAdmissibleStatement` (Proposition): if `HasCompactSmoothDualCoefficients π.representation` and `Module.Finite (MonoidAlgebra ℂ G) π.representation.asModule`, then `π.IsAdmissible`. Compactness is used here in its coefficient form, which the Theorem identifies with the definition.
- `CompactRepresentationCompactCenterStatement` (Lemma): if moreover `[SigmaCompactSpace G]` (countable at infinity), then `Nontrivial π` and `HasCompactSmoothDualCoefficients π.representation` imply `IsCompact (Subgroup.center G : Set G)`. The nontriviality hypothesis makes explicit the nonzero representation of the source's proof. The zero representation is compact for every `G`.
- `CompactRepresentationCriterionStatements` is the conjunction.

## Departures and relations to published work

- Renard assumes `G` unimodular in IV.1.3. None of these three assertions uses unimodularity, so the statements omit it; they are therefore at least as strong as the source.
- The published `CompactCoefficientIrreducibleAdmissibilityStatement` (module `CompactCoefficient.AdmissibilityStatement`) is the irreducible case of the Proposition; finite type is weaker than irreducibility, so the statement here is more general.
- The decomposition theory of IV.1.4–IV.1.7 corresponds to the published `CompactCoefficient` statements (splitting, projectors, semisimplicity, uniform support), which follow Bernstein–Zelevinsky; that correspondence is not asserted here.
- The proofs are not formalized here.
