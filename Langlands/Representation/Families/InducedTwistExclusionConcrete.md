# Exclusion for one character from separated geometric-lemma pieces

Author: Worker 5120.

This internal supporting module applies the abstract isolated-grade theorem of
`InducedTwistExclusionAlgebra` to the actual normalized Jacquet module `r_P(i_P(σ))` of an
actual rational parabolic `P = MU`. Its provenance is internal: it combines published
Frobenius reciprocity (`leviFrobeniusReciprocity`, Renard VI.1.2), the represented geometric
lemma's gluing data, the self-intersection piece results and the published admissibility
theorems.

The ambient setting is a nonarchimedean local field `k` (Hausdorff) and a group scheme `G`
with affine structure map. `G(k)` has the canonical topology and is locally compact and a
nonarchimedean group. Levi points carry `leviPointTopology`.

## Declarations

Namespace `Langlands.Aubert.General.RepresentedParabolic`.

- `exists_mem_range_jacquet_subtype_frobenius_ne_zero`: for a nonzero invariant subspace `S`
  of `I = i_P(σ)`, take the Frobenius image `Φ : r_P(I) → σ` of the identity of `I`. It is
  nonzero on the image of `r_P(S) → r_P(I)`. The Frobenius image of the inclusion
  `S → I` is nonzero because the Frobenius map is a linear equivalence. The published
  evaluation formula `e F (mk x) = F x (1)` shows that this image equals `Φ` composed
  with `r_P(S) → r_P(I)` on every Jacquet class `mk x`.
- `range_levi_le_range_comp_innerIso_of_mem`: if `z ∈ P(k)` then `M ⊆ z P z⁻¹`, as subgroup
  functors.
- `mem_pointImage_of_doubleCoset_eq_one`: a representative of the double coset
  `P(k) 1 P(k)` lies in `P(k)`.
- `not_isGeneralizedEigencharacter_jacquet_quotient_of_pieceSeparation`: let `σ` be
  irreducible admissible on `M(k)`, let `a : A → M` be a split component, and let `χ` be a
  generalized eigencharacter of `σ` on `A(k)`. Take the data of a represented geometric
  lemma for `r_P ∘ i_P` (`c`, `z`, `D`, gluing). Assume that no piece outside the identity
  double coset has the generalized `A(k)`-eigencharacter `χ`. Then for every nonzero
  invariant subspace `S` of `i_P(σ)`, the character `χ` is not a generalized `A(k)`-eigencharacter
  of `r_P(i_P(σ)/S)`.

## Proof of the last theorem

The gluing data evaluated at `σ` give a finite filtration of `r_P(i_P(σ))` whose graded
pieces are equivalent to the pieces, each original index occurring once
(`IsGluedFrom.exists_selected_filtration`). The isolated grade `j₀` is the one whose piece is
indexed by `c⁻¹(P 1 P)`.

- Other grades: their pieces lack `χ` by hypothesis, transported along the graded
  equivalences restricted to `A(k)` (`Cohomology.HyperextAbutment.equivComp`).
- Grade `j₀`: its representative lies in `P(k)`, so the source intersection parabolic is
  full (`isIso_p'_of_range_le`), hence so is the target one (`isIso_q'_of_isIso_p'`). The piece
  is then irreducible on the irreducible `σ` (`pieceFunctor_isIrreducible_of_isIso`).
- Points of `A` are central in `M(k)` because a split component is central.
- `r_P(i_P(σ))` is admissible: induction preserves admissibility
  (`leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement` with
  `arbitraryParabolicQuotientCompact`), Jacquet restriction preserves it
  (`arbitraryParabolicJacquetAdmissibility`), and the Levi-point transport preserves it.
- `Φ` and `W` come from the first declaration. The quotient map `r_P(I) → r_P(I/S)` is
  `r_P` of the quotient map. It is surjective on Jacquet classes and kills the image of
  `r_P(S)`, because `I → I/S` kills `S`.

The abstract theorem `not_isGeneralizedEigencharacter_of_isolatedGrade` then concludes.
