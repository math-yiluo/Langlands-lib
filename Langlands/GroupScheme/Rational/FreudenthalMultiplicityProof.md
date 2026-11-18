# Freudenthal's multiplicity formula for a split reductive group in characteristic zero

Module `Langlands.GroupScheme.Rational.FreudenthalMultiplicityProof`. The main
theorem is `Langlands.GroupScheme.freudenthalMultiplicityStatement`. The helper
lemmas about products of submodules are in namespace
`Langlands.GroupScheme.FreudenthalMultiplicity`.

## Main theorem

`freudenthalMultiplicityStatement : FreudenthalMultiplicityStatement.{u}` proves
the proposition of `Langlands.GroupScheme.Rational.FreudenthalMultiplicityStatement`
for every universe `u`, with no further hypotheses. That proposition is Freudenthal's
multiplicity formula (Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, §22.3) for a highest-weight representation `r : G → GL_n` of a
group scheme `G` over a field `k` of characteristic zero with a split pinning `p`.

The theorem specializes the abstract recursion
`Langlands.LinearAlgebra.freudenthalCasimirCoreStatement` (module
`Langlands.LinearAlgebra.FreudenthalCasimirCore`) as follows:

- `U = kᴺ × kⁿ`, where `σ : G → GL_N` is a closed linear embedding. Its
  existence is the Library theorem `affineLinearEmbeddingStatement`.
- `X` and `Y` are the character and cocharacter lattices of the split maximal
  torus `p.torus`, and `P` is the perfect pairing of the root datum
  `p.rootDatum`. The basis `yb` of `Y` is transported from a coordinate
  isomorphism `Y ≃ ℤ^I` (`p.isSplitTorus.exists_cocharacterCoordinates`).
- `W μ = p.pairWeightSpace σ r μ`, the product of the `μ`-weight spaces of `σ`
  and of `r`.
- `g = pairLieAlgebra σ r`, the image of the Lie algebra of `G` under the pair
  tangent map `X ↦ (dσ(X), dr(X))` acting on `kᴺ × kⁿ`.
- `root = p.rootDatum.root` and `pos j` means that `root j` lies in
  `p.positiveRootMonoid`.
- `V = 0 × kⁿ`, the copy of the representation space of `r`.

The seventeen hypotheses of `FreudenthalCasimirCoreStatement` are supplied as
follows.

1–2. Independence and spanning of the product weight spaces follow from
   `iSupIndep_representationWeightSpace` and
   `iSup_representationWeightSpace_eq_top` for `σ` and for `r`, combined by the
   helpers `iSupIndep_prod` and `iSup_prod_eq_top`.
3–7. These are the first five conjuncts of `pairLieWeightDataStatement`
   (module `Langlands.GroupScheme.Rational.PairLieWeightDataProof`): grading,
   cocharacter elements, the degree-zero piece, vanishing off the roots, and
   one-dimensional root pieces.
8. The sixth conjunct of `pairLieWeightDataStatement` gives a weight `μ` of `σ`
   with `⟨μ, y⟩ ≠ 0` for each nonzero cocharacter `y`. The pair weight space at
   `μ` is then nonzero (`prod_ne_bot_of_left`).
9–11. Roots are nonzero (`RootPairing.ne_zero`), the root map is injective, and
   `root (reflectionPerm j j) = -root j`, because the reflection in a root sends
   that root to its negative.
12. `G` is connected reductive (`p.isConnectedReductive`), so it is smooth and
   connected. In characteristic zero its unipotent radical over the ground field
   is trivial: this is
   `IsConnectedReductive.hasTrivialUnipotentRadical_of_unipotentFieldExtension`
   applied to the Library theorem `unipotentFieldExtensionStatement`. Then
   `pairLieAlgebra_nilpotentIdeal_eq_bot` says that every Lie ideal of
   `pairLieAlgebra σ r` made of nilpotent endomorphisms is zero, using that `σ`
   is a closed embedding.
13. Every element of `g` is a block-diagonal map `(dσ(X), dr(X))`. It
   therefore sends `0 × kⁿ` into itself.
14. Let `K ≤ 0 × kⁿ` be nonzero and `g`-stable, and let `K'` be its projection to
   `kⁿ`. Then `K'` is stable under every tangent matrix `dr(X)`, so it is an
   `r`-stable subspace by `isStableSubspace_iff_tangentMatrix`. This is the
   characteristic-zero equivalence of the Library module
   `Reductive.CharZeroSemisimplicity.TangentStability`. Since `r` is irreducible
   (the first conjunct of `IsHighestWeight`), `K'` is `0` or `kⁿ`. The
   projection is injective on `K`, so `K' = 0` would force `K = 0`. Hence
   `K' = kⁿ`, and `K = 0 × kⁿ`.
15–17. We have `(0 × kⁿ) ⊓ W μ = 0 × r_μ` (`bot_prod_top_inf_prod`), so
   `dim ((0 × kⁿ) ⊓ W μ) = dim r_μ`, and this space is zero exactly when
   `r_μ = 0`. The highest-weight conditions of `IsHighestWeight` say that
   `r_lam` has dimension one and that `lam - μ` is a sum of positive roots
   whenever `r_μ ≠ 0`. So `r_{lam + α} = 0` for a positive root `α`, since
   `-α` is not a sum of positive roots
   (`WeylCharacter.neg_root_notMem_of_mem`). Likewise `r_{lam - α} = 0` for a
   root `α` that is not positive.

## The form

The form in the conclusion is `F = GramDual.form P yb m` (module
`Langlands.LinearAlgebra.GramDualForm`), where `m ν = dim W ν` is the sum of the
weight multiplicities of `σ` and `r` at `ν`. The four required properties are
proved as follows.

- Symmetry is `GramDual.form_comm`.
- Positivity is `GramDual.form_pos`. Its inputs are that `m` has finite
  support, since only finitely many `W ν` are nonzero
  (`WeightGraded.finite_ne_bot`); that every nonzero cocharacter pairs
  nontrivially with some `ν` with `m ν ≠ 0` (hypothesis 8 above); and that
  every nonzero character pairs nontrivially with some cocharacter, since `P`
  is a perfect pairing.
- Weyl invariance is `GramDual.form_apply_apply_eq`, applied to the reflection
  `s_i` and the coreflection `s_i^∨`. Its inputs are the adjointness
  `⟨s_i χ, y⟩ = ⟨χ, s_i^∨ y⟩`, which is a direct computation from
  `RootPairing.reflection_apply` and `RootPairing.coreflection_apply`, and the
  invariance `m (s_i ν) = m ν`, which is
  `finrank_representationWeightSpace_root_reflection` for `σ` and for `r`.
- The recursion is the conclusion of `freudenthalCasimirCoreStatement`, after
  replacing `dim ((0 × kⁿ) ⊓ W μ)` by `dim r_μ` as in items 15–17.

## Provenance

The formula and the Casimir argument behind it are Humphreys, GTM 9, §22.3. The
form `F` is the dual of the trace form of `kᴺ × kⁿ` restricted to the torus part
of `g`, not the dual of the Killing form. Humphreys derives the recursion for any
invariant nondegenerate form (§22.2–22.3), and `FreudenthalMultiplicityStatement`
only asks for some symmetric, Weyl-invariant, positive definite form. Taking the
pair `(σ, r)`, rather than `r` alone, is an internal device of this proof. The
faithful block `σ` makes the tangent Lie algebra isomorphic to the Lie algebra of
`G`, which is what the vanishing of nilpotent ideals (hypothesis 12) and the
weight data of `pairLieWeightDataStatement` need.
