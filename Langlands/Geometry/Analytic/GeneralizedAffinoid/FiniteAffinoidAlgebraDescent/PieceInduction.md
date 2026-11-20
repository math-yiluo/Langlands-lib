# Global generation from piece generation by binary Laurent induction

This module is in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent`.
Its final theorem is

```
globalGeneration_of_prerequisites
  (hG2 : PieceMatchingLocalGenerationStatement.{u})
  (hG3 : PieceMatchingGluingStatement.{u})
  (h3 : FiniteCoverBinaryLaurentInductionStatement.{u})
  (h4 : DomainBinaryLaurentSplitSquareStatement.{u})
  (h5 : BoundedAlgHom.SplitSquareModuleGenerationStatement.{u, u, u}) :
  FiniteAffinoidAlgebraGlobalGenerationStatement.{u}
```

So global generation of the local finite algebras by elements of the matching
algebra follows from five published route statements:

- local-to-global generation of matching families (`hG2`);
- gluing of matching families (`hG3`);
- induction along binary Laurent splits (`h3`);
- binary Laurent splits of full domains are split squares (`h4`);
- generation of modules over split squares (`h5`).

The theorem takes these statements as hypotheses. The module uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

Throughout, `c` is a finite full-domain cover of the whole spectrum of `R`,
`F : LocalAlgebras c`, and `t` is a family of pair transitions. For a full
domain `V`, `t.piece V i = F.baseChange i (V ∩ cᵢ)` and `t.pieceMatching V` is
the algebra of matching families. `PiecesGenerate V s` says that the `i`-th
components of `s` generate every piece over the algebra of `V ∩ cᵢ`.
`Generates V s` says that `s` generates `t.pieceMatching V` over `V.algebra`.
Both are defined in `PieceMatching`.

## Provenance

The proof is an internal derivation. Its structure follows the proof of Kiehl's
theorem, in which finite modules are glued along binary Laurent splits by a
Cartan-type lemma. See Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 /
PDF p.12 (registered source `berkovich-1993-etale-cohomology`). The induction
along binary Laurent splits follows the reduction in the proof of Tate's
acyclicity theorem in Piotr Achinger, *Introduction to non-Archimedean
Geometry*, lecture notes, November 22, 2020, §7.2–§7.3, pp.65–67 (registered
source `achinger-2020-non-archimedean-geometry-nov22`). That reduction is
supplied here by the hypothesis `h3`.

The induction carries generation of pieces (`PiecesGenerate`), not generation
of the matching algebra. Only the former restricts along smaller domains
without a flatness argument.

## Part A: linear algebra and restriction

- `exists_coeff_trans`: linear combinations of linear combinations are linear
  combinations, for coefficients acting through a ring homomorphism.
- `LocalAlgebras.restrict_localMap_apply`, `restrict_baseMap_apply`: elementwise
  forms of the published restriction laws.
- `LocalAlgebras.baseChange_generated`: if `b` generates `F.algebra i` over the
  member algebra with norm control (the field `F.finite i`), then the images
  `F.localMap i E (bₗ)` generate every base change `F.baseChange i E` over
  `E.algebra`. This is `AffinoidPushout.rightMap_coefficientMap_leftMap` from
  `PieceGeneration`.
- `PairTransitions.transition_baseMap_apply`, `matchingRestrict_comp`,
  `matchingRestrict_self`, `matchingRestrict_structure`, `val_sum_mul_apply`:
  elementwise and functoriality laws for restriction of matching families.
- `piecesGenerate_congr`: transport along pointwise equal families.
- `piecesGenerate_restrict`: piece generation passes to restrictions to
  smaller full domains. Every element of a smaller piece is a combination of
  restricted local generators (`baseChange_generated`). Each restricted
  generator is the restriction of a combination of the given families.
- `piecesGenerate_of_span`: if each member of a generating family is a
  combination of the members of a second family, the second family also
  generates the pieces.

## Part B: descent data

In the namespace `DescentData` (pair transitions with identity and cocycle):

- `transition_transition_apply`: restricted transitions in opposite directions
  are mutually inverse, by `transition_cocycle_of_triple` for `(j, i, j)` and
  `transition_self_of_identity`.
- `piecesGenerate_base` (base case): if `U ⊆ cᵢ₀`, the families
  `ofPiece i₀ (F.localMap … (bₗ))` built from the local generators `b` of
  `F.algebra i₀` generate every piece of `U`. To write `p` in the `j`-th piece,
  move it to the `i₀`-th side by the inverse transition, expand it there with
  `baseChange_generated`, and move it back. Transitions preserve the base
  legs.
- `piece_of_generates`: if the restrictions of `s` to `V ∩ cᵢ` generate the
  matching families there, then the `i`-th components of `s` generate
  `t.piece V i`. Apply the hypothesis to the matching family
  `ofPiece i (restriction of p)` over `V ∩ cᵢ`. Its `i`-th component is the
  restriction of `p`, because the self-transition is the identity. Then restrict
  back from `(V ∩ cᵢ) ∩ cᵢ` to `V ∩ cᵢ`; this composite restriction is the
  identity.

## Part C: two-member covers

In the namespace `PairTransitions`:

- `pairCover h₁ h₂ hcov`: the finite cover of `V` by two full subdomains
  `W₁, W₂` whose loci cover the locus of `V`.
- `exists_pair_glue`: matching families over `W₁` and `W₂` that agree on
  `W₁ ∩ W₂` glue to a matching family over `V` (`hG3` applied to `pairCover`;
  the compatibility of the pair `(2, 1)` follows from that of `(1, 2)` by
  restriction along the swap of the intersection).
- `generates_of_piecesGenerate`: piece generation implies generation (`hG2`
  for the singleton cover).
- `generates_of_pair`: if the restrictions of `s` to `W₁` and `W₂` generate all
  pieces, then the restrictions of `s` to every full subdomain `V' ⊆ V`
  generate the matching families over `V'`. Apply `hG2` to the cover of `V'`
  by `W₁ ∩ V'` and `W₂ ∩ V'`, after `piecesGenerate_restrict`.
- `span_eq_top_of_generates`, `exists_coeff_of_span`: translations between
  `Generates` and `Submodule.span … = ⊤` for the module structure through
  `matchingStructure`.
- `locus_subset_of_split`, `locus_subset_union_of_split`: the halves
  `{|a| ≤ ρ}` and `{|a| ≥ ρ}` of a split of `U` lie in `U` and cover it.

## Part D: the induction step

`piecesGenerate_step`: let `U` be a full domain with `a ∈ U.algebra` and
`ρ > 0`. Suppose that every pair of full domains `U₁, U₂` with the loci of the
two halves has piece-generating families. Suppose also that piece generation
glues along two-member covers (hypothesis `hpair`). Then `U` has a
piece-generating family.

1. `h4` provides full domains `U₁, U₂` with the loci of the halves, and a split
   square for the four restrictions between `U`, `U₁`, `U₂` and `U₁ ∩ U₂`.
2. Let `x` and `y` be piece-generating families on `U₁` and `U₂`. By
   `generates_of_piecesGenerate` and `piecesGenerate_restrict`, the families
   `x`, `y` and their restrictions to `U₁ ∩ U₂` generate the matching
   families. View the matching algebras as modules through
   `matchingStructure`. Then the modules over `U₁` and `U₂` are finite, and
   both restricted families span the module over `U₁ ∩ U₂`.
3. `h5` gives a number `m` and families `x'`, `y'` of length `m` that agree on
   `U₁ ∩ U₂` and span the modules over `U₁` and `U₂`. By
   `piecesGenerate_of_span`, `x'` and `y'` still generate all pieces.
4. `exists_pair_glue` glues `x'ₗ` and `y'ₗ` to matching families `zₗ` over
   `U`, and `hpair` gives piece generation for `z`.

`DescentData.piecesGenerate_of_pair` proves `hpair` for descent data. By
`generates_of_pair`, the restrictions of `s` to `V ∩ cᵢ` generate there, and
`piece_of_generates` concludes.

`DescentData.exists_piecesGenerate_whole`: for a nonempty cover, `h3` applied
to the property "some finite family generates all pieces" gives a
piece-generating family over the whole spectrum. The base case is
`piecesGenerate_base`, and the step is `piecesGenerate_step`.

## Part E: from the whole spectrum to the local algebras

- `member_subset_whole_inter`: `cᵢ ⊆ whole ∩ cᵢ`.
- `LocalAlgebras.wholeInverse i`: the inverse of
  `F.localMap i (whole ∩ cᵢ)`. It is the pushout lift of the identity of
  `F.algebra i` and of the member map composed with the restriction from
  `whole ∩ cᵢ` to `cᵢ`. The lemmas `wholeInverse_comp_localMap`,
  `wholeInverse_comp_baseMap` and `localMap_wholeInverse` (with their
  elementwise forms) show that it is a two-sided inverse.
- `PairTransitions.toMatchingAlgebra`: a matching family over the whole
  spectrum gives an element of `t.MatchingAlgebra` with components
  `wholeInverse i (sᵢ)`. The defining matching condition on `cᵢ ∩ cⱼ` is the
  matching condition of `s` on the overlap, rewritten through
  `transition_overlap`.
- `surjective_of_piecesGenerate_whole`: piece generation over the whole
  spectrum shows that the projections of the corresponding matching-algebra
  elements generate `F.algebra i` over the member algebra. Apply
  `wholeInverse i` to an expansion of `F.localMap … y`.

## Final theorem

`globalGeneration_of_prerequisites`: if the cover is empty, the empty family
works vacuously. Otherwise, `exists_piecesGenerate_whole` gives a
piece-generating family over the whole spectrum. `toMatchingAlgebra` and
`surjective_of_piecesGenerate_whole` turn it into the required finite family of
the matching algebra.
