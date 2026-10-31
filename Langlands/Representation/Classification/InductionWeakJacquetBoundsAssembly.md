# Weak upper Jacquet bounds of induced representations from the geometric lemma

Author: Worker 828.

This module derives the exact proposition
`Langlands.GLInductionWeakJacquetBoundsStatement.{uF,uV}` from the normalized
geometric lemma `Langlands.Geometric.PadicGeometricLemmaTheorem.{uF,uV}`, in
the final theorem `Langlands.glInductionWeakJacquetBounds_of_geometricLemma`.
In this module the geometric lemma is a hypothesis. The closing theorem
`Langlands.glInductionWeakJacquetBounds`, in
`Langlands.Representation.Classification.InductionWeakJacquetBoundsProof`,
discharges it with the published proof
`Langlands.Geometric.padicGeometricLemma`.

## Declarations

- `Langlands.isGeneralizedEigencharacter_comp_of_iso`: an isomorphism
  `X ≅ Y` of `Rep ℂ G` preserves generalized eigencharacters of the
  restriction along any `ι : M →* G`. Proof: `e.hom` is an intertwiner after
  restriction. It does not kill a nonzero vector, since `e.inv` undoes it.
  Apply `isGeneralizedEigencharacter_of_map_ne_zero`.
- `T.isGeneralizedEigencharacter_jacquetInductionFunctor B C σ hσ χ hχ`: a
  `T.IsJacquetExponent C` of `T.normalizedParabolicInduced B σ` is a
  generalized eigencharacter of `C.blockScalarLevi` on
  `(jacquetInductionFunctor T B C).obj (SmoothRep.of σ hσ)`. This is the
  second component of `IsJacquetExponent`, since the split-centre Jacquet
  action is the normalized Jacquet action composed with `C.blockScalarLevi`.
- `T.isGeneralizedEigencharacter_of_geometricPiece B C w S R hS hR σ' χ`:
  take a generalized eigencharacter `χ` of the block scalars of `C` on the
  geometric piece
  `(geometricPieceFunctor T B C w S R hS hR).obj σ'`. Then `χ` is a
  generalized eigencharacter of
  `((T.normalizedRefinedJacquet B S σ'.representation).comp (flattenedBlockScalar B S _)).comp (chamberRestriction B C w S _)`.
  Proof, through the factors of the piece:
  1. The outer factor is normalized refined induction for `R`, normalized by
     `T.refinedLeviHalfModulus C R`. That half modulus is trivial on the
     block scalars of `C` (`refinedLeviHalfModulus_refinedBlockScalar`). So
     `isGeneralizedEigencharacter_of_normalizedRefinedInductionFunctorOf`
     moves `χ` to the inducing representation, restricted along
     `refinedBlockScalar C R`. This step is the modulus cancellation: the
     positive half-modulus of induction contributes no character.
  2. `isGeneralizedEigencharacter_subgroupEqualityFunctor` removes the
     relabelling along `hR`.
  3. The intersection transport is definitionally restriction along the
     inverse `intersectionLeviConjugation F B C w`, from the inverse
     representative's source Levi `sourceLevi F C B w⁻¹`. The relabelling
     along `hS.symm` is removed as in step 2.
  4. `intersectionLeviConjugation_symm_blockScalar` identifies the composite
     of these subgroup maps on block scalars of `C` with
     `flattenedBlockScalar B S ∘ chamberRestriction B C w S`.
- `T.norm_le_one_of_geometricPiece B C w S hS σ hw`: let `σ` be admissible,
  `w` strictly increasing on every block of `B`, and assume the source
  premise for the single refinement `S`. Then every `χ` as in the previous
  conclusion satisfies `‖χ a‖ ≤ 1` for each globally increasing tuple of
  normalized absolute values `a`. Proof:
  - The normalized refined Jacquet module is admissible
    (`Parabolic.isAdmissible_normalizedRefinedJacquet`).
  - Flattened block scalars are continuous and central.
  - So `exists_eigencharacter_extension` extends `χ` to an open-kernel
    generalized eigencharacter `ψ` of the flattened block scalars, with
    `ψ ∘ chamberRestriction = χ`.
  - The tuple `chamberRestriction a` is monotone within every outer block of
    `B`: `a` is monotone and so is `chamberIndex` on these blocks
    (`monotone_chamberIndex`).
  - The source premise therefore bounds `‖ψ (chamberRestriction a)‖ = ‖χ a‖`
    by one.
- `T.induction_weakJacquetBound_of_geometricLemma B C hgeo σ`: the target
  conclusion for one ambient block shape `C`, assuming
  `GeometricLemmaTheorem T B C`. Proof:
  - Unpack the refinement families `S` and `R`, their intersection
    equalities, the enumeration `e` of minimal representatives, and the
    natural filtration `s` of `jacquetInductionFunctor T B C` with graded
    isomorphisms to the geometric pieces.
  - Worker 573's published
    `RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter` places
    `χ` in some graded piece `i`, with the same uniform power.
  - `isGeneralizedEigencharacter_comp_of_iso` moves it to the geometric piece
    of `w = e (perm i)`.
  - `w` is a minimal representative. Its first property (strict monotonicity
    on blocks of `B`) is the hypothesis of `norm_le_one_of_geometricPiece`.
    That theorem is applied with the source premise for `D = S w`.
- `Langlands.glInductionWeakJacquetBounds_of_geometricLemma hgeo`: introduces
  all binders of the target statement and applies the previous theorem with
  `hgeo p F T n hn B C`.

## Scope

The irreducibility premise of the target statement is not used, and no
hypothesis is added. Every prime, `PadicField`, `TopologicalData`, positive
rank, block shape, representation and universe of the target is kept. The
induced carrier is the actual function space in `max uF uV`, through
`jacquetInductionFunctor`.

## Provenance

The route is the algebraic part of Waldspurger 2003, III.2.3 (registered
`waldspurger-2003-plancherel`, printed pp.266–267): exponents of the Jacquet
modules of an induced representation come from the pieces of the geometric
lemma (Bernstein–Zelevinsky 1977, 2.11–2.12, registered
`bernstein-zelevinsky-1977-induced-i`). There they are transported from source
exponents by the inverse representative, and inverse conjugation maps the
ambient chamber into the source within-block chambers. The Lean proof uses
the Library's normalized pieces, so the induction and Jacquet half-moduli are
already normalized. The only remaining character on block scalars of `C` is
the induction half modulus, which is trivial there.
