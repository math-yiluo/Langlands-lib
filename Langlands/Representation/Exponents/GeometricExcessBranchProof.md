# Strict Jordan–Hölder excess selects a noncoarse opposite geometric branch

`Langlands.glGeometricExcessBranch.{uF,uV,uW}` proves exactly the published
proposition `Langlands.GLGeometricExcessBranchStatement.{uF,uV,uW}` of
`Langlands.Representation.Exponents.WeylBranchPiecesStatement`. The field
universe `uF`, the cuspidal target universe `uV` and the inducing universe
`uW` stay independent. The theorem has no premise beyond the statement's own
hypotheses.

## What is proved

The statement covers every prime `p`, every finite p-adic extension `F` with
its supplied topological data `T`, every positive rank `n`, every coarse block
shape `B` with refinement `S`, and every smooth representation `V` of the Levi
of `B` in universe `uW`. No irreducibility, admissibility, finite length,
central character or support condition is placed on `V`. Let `ρ` be an
irreducible Levi-cuspidal representation of the Levi of `B.flatten S` in
universe `uV`, and let `τ` be `ρ` pulled back to the refined Levi
`refinedLevi F B S`. Suppose `τ` has Jordan–Hölder multiplicity `m_in` in the
inner opposite Jacquet module `innerJacquet T B S V` and `m_amb` in the
ambient one `ambientJacquet T B S V`. These are multiplicities in finite
composition series (`HasJordanHolderMultiplicity`). If `m_in < m_amb`, the
theorem gives a permutation `x` and a refinement `S'` of `B` such that:

- `x` conjugates the Levi of `B.flatten S'` onto the Levi of `B.flatten S`
  (an actual `ConjugatesLevi` witness);
- `x` is a minimal representative from `B` to `B.flatten S`;
- `x ∉ blockWeyl B`;
- `ρ` is an actual quotient of an actual subrepresentation (`IsSubquotient`)
  of the inner opposite Jacquet module of `V` along `S'`, transported by `x`.

## Proof

The proof is the single term

```
glGeometricExcessBranch_of_upper Geometric.padicGeometricLemma.{uF, uW}
```

- `Langlands.glGeometricExcessBranch_of_upper` (module
  `Langlands.Representation.Exponents.GeometricExcessBranchFromUpper`,
  published earlier for this task) derives
  `GLGeometricExcessBranchStatement.{uF,uV,uW}` from the proposition
  `Geometric.PadicGeometricLemmaTheorem.{uF,uW}`.
- `Langlands.Geometric.padicGeometricLemma.{uF,uW}` (module
  `Langlands.Representation.Geometric.GeometricLemmaProof`, published by
  Workers 164 and 194 for task 67ebcf61) proves that proposition with no
  premise. It is the normalized upper geometric lemma for positive-rank `GL`.

So the geometric lemma enters as a proved Library theorem, not as a premise
of `glGeometricExcessBranch`. The theorem takes no supplied filtration,
branch package or certificate.

`GeometricExcessBranchFromUpper.md` explains the conditional derivation in
full. In outline:

1. The upper geometric lemma at the source `B` and the reversed fine target
   `(B.flatten S).reverse` gives an actual finite filtration of the upper
   Jacquet module of the normalized induction of `V`. Its graded pieces are
   the actual geometric pieces.
2. The piece with the identity label is identified with the inner opposite
   Jacquet module, after block reversal and the flattened-Levi
   identification. The whole upper Jacquet module is identified with the
   ambient opposite Jacquet module. Jordan–Hölder multiplicity transport
   along group and representation equivalences moves `m_in` and `m_amb` to
   these two modules.
3. Multiplicity additivity along the filtration
   (`IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess`) turns
   `m_in < m_amb` into a piece with a label other than the identity that
   contains the reversed `ρ` as an actual subquotient.
4. Cuspidality excludes proper target induction: BZ77 2.4(d), published as
   `CuspidalSupport.padicProperRefinedInduction`, gives this as
   `not_isSubquotient_properInduced`. So that piece has a whole target
   refinement, and its label conjugates a whole flattened Levi of `B` onto
   the fine target.
5. The reversed-piece permutation `x` and `S' = reverseRefinement B (P w)`
   give the minimal representative and the conjugacy, and the transported
   inner opposite Jacquet module along `S'` contains `ρ`. If `x` were in
   `blockWeyl B`, minimality would force `x = 1`, then `S' = S`, and the
   piece would be the identity piece, which step 3 ruled out.

## Provenance

This theorem is an internal derivation, not a numbered result of the
literature. The argument is the standard Bernstein–Zelevinsky one: a cuspidal
constituent of the geometric-lemma filtration occurs only in a piece whose
inducing parabolic is whole. The source is Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977): section 2.12
for the geometric lemma and section 2.4(d) for proper induction. Its use for
branch selection follows Silberger 1978, Lemma 5.6, as recorded in the target
statement's Markdown. Both literature inputs enter only through published
Library theorems.

Lean check: 0 errors, 0 warnings. The axioms used are `propext`,
`Classical.choice` and `Quot.sound` only. The target statement's
Lean/Markdown pair and all imported Library files are unchanged.
