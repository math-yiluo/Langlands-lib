# Renard II.3.6: Haar distributions and density embeddings

The theorem `Langlands.HarmonicAnalysis.Distribution.RenardHaar.statements`
proves the exact published proposition
`Langlands.HarmonicAnalysis.Distribution.RenardHaar.Statements` at its full
group universe. All five conjuncts are proved without additional premises.
The finite expansion of right-invariant tests in left cosets `gK` from II.3.5 is supplied by the published theorem
`Hecke.RenardTestDecomposition.rightInvariantExpansion`.

The implementation is split into three supporting paired modules:

- `RenardHaarDensityProof` proves strict positivity and left invariance of
  actual Haar integration, equality of the actual density distribution support
  with the density's nonzero locus, injectivity and compact support for test
  densities.
- `RenardHaarLeftProof` applies finite coset expansions at a common compact-open
  level to classify every invariant algebraic distribution by a single complex
  scalar. It gives left Haar existence and the comparison with actual Mathlib
  Haar integration.
- `RenardHaarConsequencesProof`, contributed by Worker 140, transports the
  original test and distribution spaces through unweighted inversion to prove
  the right Haar assertion. Evaluation on a nonzero nonnegative compact-open
  subgroup indicator forces the scalar relating positive invariant
  distributions to be a unique positive real number.

Each supporting Markdown file describes its implemented proof. Their
composition retains all five original targets, arbitrary Hausdorff locally
compact totally disconnected groups, the full complex algebraic dual and the
single unrestricted group universe. No measurable representation of an arbitrary
algebraic distribution or countability premise is used. The published statement
pair and all its imported pairs are unchanged.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact source passage is II.3.6 Proposition and following density paragraph,
printed pp.46–47 / PDF pp.52–53, both read. The support equality and
positive-real uniqueness are the derived consequences specified by the
published targets. The finite-expansion argument follows the source's full-dual
uniqueness route; existence instead uses Mathlib's actual Haar construction.
