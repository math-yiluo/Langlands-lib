# Algebraization of formally versal Picard families: proof

Module `Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationProof`, namespace
`Langlands.AlgebraicGeometry.Picard`.

The theorem

```text
versalAlgebraization : VersalAlgebraizationStatement.{u}
```

proves the Library statement
`Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement` (module
`Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement`) for every
universe `u`. The statement pair is unchanged. The theorem has no hypotheses.

## Statement (recalled)

Let `R` be a commutative ring of finite type over `ℤ` and `X` a proper flat scheme
over `Spec R`. Let `K` be a field of finite type over `R`, `A` a complete Noetherian
local `R`-algebra, `ε : A →ₐ[R] K` surjective, and `L` a line bundle on
`Spec A ×_R X` that is formally versal (`IsFormallyVersalAt`) at the closed point
`p = Spec ε`. Then there are a scheme `U` locally of finite type over `Spec R`, a
line bundle `L'` on `U ×_R X`, a point `u₀` of `U` with an identification
`e : κ(u₀) ≅ K` and the resulting `K`-point `p'` of `U`, such that `L'` is formally
versal at `p'` and `residueBundle L' p' ≅ residueBundle L p`. The statement's own
Markdown gives the full quantifier list and the meaning of every predicate.

## Proof (as implemented)

The proof is one term: the published reduction applied to the published etale
approximation theorem.

```text
versalAlgebraization_of_etaleApproximation
  CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation
```

It adds no hypothesis and introduces no other declaration.

## Published inputs

| Library theorem | Module | Content |
| --- | --- | --- |
| `versalAlgebraization_of_etaleApproximation` | `Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction` | `FiniteTypeIntEtaleCompletionApproximationStatement.{u} → VersalAlgebraizationStatement.{u}`. |
| `CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation` | `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof` | Proves `FiniteTypeIntEtaleCompletionApproximationStatement.{u}`: every maximal localization of a finite-type `ℤ`-algebra has finite-order approximation in etale neighbourhoods for maps into its completion. |

The reduction's Markdown
(`Langlands/AlgebraicGeometry/Picard/VersalAlgebraizationReduction.md`) describes its
proof in seven steps. The family is spread to a finitely generated subalgebra of `A`.
The approximation hypothesis enters only through
`CompleteLocalAlgebraicChart.exists_algebraicChart`, which gives an algebraic chart
`U = Spec T`. Truncation tests are built, the initial fibre point is lifted along the
tower, versality is checked level by level, and the point `u₀`, the identification
`e` and the residue-bundle isomorphism are packaged.

The approximation proof
(`Langlands/CommutativeAlgebra/FiniteTypeIntEtaleCompletionApproximationProof.md`)
uses Popescu factorization (`Popescu.popescuFactorization`), the G-ring property of
finite-type `ℤ`-algebras (`finiteTypeIntGRing`), etale approximation from a smooth
source (`smoothEtaleCompletionApproximation`), and Noetherianity of adic completions.
All of these are published proofs, not hypotheses. None of the following
propositions is an input:
`FiniteTypeVersalChartStatement`, `FiniteTypeFormalVersalBundleStatement`,
`VersalSmoothNeighbourhoodStatement`, `PicardOpennessOfVersalityStatement` and any
assumed atlas, approximation or algebraization statement.

## Relation to the source

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, `artin.pdf` (version ed88ff78).

- **Lemma 98.12.7 (Tag 07XH), printed pp. 20–21.** The target specializes this
  lemma to the Picard stack, as the statement's Markdown explains. Its proof applies
  Lemma 98.10.1 with `N = 2` to an object over `Spec R'` and concludes with Lemma
  98.12.3. The reduction follows this route.
- **Lemma 98.10.1 (Tag 07XB).** It needs the G-ring property and Artin approximation
  for the local rings of `S`. The implementation replaces these with the etale
  approximation statement over maximal localizations of finite-type `ℤ`-algebras.
  The published approximation proof derives that statement from the G-ring property
  and Popescu's theorem (Stacks, *Smoothing ring maps*, Theorem 13.2, Tag 07QZ, and
  Theorem 07GC). The present module only composes the two published results.
