# Proof: the Hilbert scheme of a projective flat family on all test schemes

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705),
by agreement with that task's first executor, Worker 5705. It proves the
published proposition
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement` (module of the
same name, by Worker 22). The operator's answer to request
`98389b48910e54088e0e2b2ba6aaad9c` allows such prerequisite proofs to stay
under Task 5705.

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily :
    HilbertSchemeUniversalFamilyStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Modules

- `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.ProjectivePieces`:
  the FLT per-polynomial Hilbert scheme `C θ`, with the extra conclusion that
  `C θ` is H-projective over `Spec A` (an adapted copy of an FLT-ported proof;
  see its Markdown for the source, licence and changes).
- `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.Globalization`:
  the theorem `classification`, which turns a classifier on affine tests and a
  universal closed subscheme into the universal ideal sheaf on all test schemes.
- This module: the assembly.

## Proof of `hilbertSchemeUniversalFamily`

Let `A`, `f : X ⟶ Spec A`, `𝓛X` and the hypotheses of the statement be given.

1. **Pieces.** For every `θ : Polynomial ℚ`,
   `exists_isHProjective_hilbertPolynomial_piece` gives `C θ`, `πC θ` and a
   classifier `ptC θ` on affine tests for closed subschemes with Hilbert
   polynomial `θ`, natural, surjective and injective up to isomorphism, with
   `πC θ` proper, locally of finite presentation and H-projective (`choose`).
2. **The Hilbert scheme.** `H := ∐ C`, `πH := Sigma.desc πC`. The Library
   theorem
   `AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`
   gives a classifier `pt` for all flat, locally finitely presented closed
   subschemes over affine tests, natural for ring maps (`hnat`), with
   `pt = ptC θ ≫ Sigma.ι C θ` on subschemes with Hilbert polynomial `θ`
   (`hconst`). These data form a structure
   `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam`
   of the Library module of that name, exactly as in the Library proof of the
   FLT Hilbert theorem; its lemmas `Fam.surj`, `Fam.inj` and `Fam.pieces`
   give surjectivity of `pt`, injectivity of `pt` up to isomorphism, and the
   piece clause for the opens `(Sigma.ι C θ).opensRange`.
3. **Universal closed subscheme.** The Library theorem
   `AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`
   applied to `pt`, `hnat`, surjectivity and injectivity gives a closed
   immersion `ι : 𝒵 ⟶ X ×_A H`, flat and locally of finite presentation over
   `H`, that pulls back to every classified closed subscheme over an affine
   test (hypothesis `ClassifierUniv` of `Globalization`).
4. **The ideal sheaf.** `W := ι.ker`. Then `classification` (module
   `Globalization`) gives item 2 of the statement for every scheme `T`: the
   map `pullback.map f s f πH (𝟙 X) g (𝟙 _) _ _` of the statement is
   `mapX f g hg` by definition.
5. **`πH`.** It is locally of finite presentation by
   `IsZariskiLocalAtSource.sigmaDesc` (the instance
   `IsZariskiLocalAtSource @LocallyOfFinitePresentation` is supplied
   explicitly, because instance search does not find it here), and separated
   by the Library theorem `AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated`,
   since each `πC θ` is proper.
6. **Pieces of `H`.** `U θ := (Sigma.ι C θ).opensRange`. They are pairwise
   disjoint (`disjoint_opensRange_sigmaι`) and cover `∐ C` (the Library theorem
   `AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`
   for `𝟙 (∐ C)`), as in the Library proof of the FLT Hilbert theorem.
   - *H-projectivity.* `(U θ).ι ≫ πH = (Sigma.ι C θ).isoOpensRange.inv ≫ πC θ`
     (`Scheme.Hom.isoOpensRange_inv_comp`, `Sigma.ι_comp_desc`). If
     `i : C θ ⟶ ProjectiveSpace A n` is the closed immersion of step 1, then
     `isoOpensRange.inv ≫ i` is a closed immersion over `Spec A`.
   - *Piece clause.* Let `g : Spec B ⟶ H` over `s` with
     `W.comap (mapX f g hg) = I`. By the first part of `classification`, the
     closed subscheme of `I` is flat and locally of finite presentation over
     `Spec B`. By `eq_pt` (module `Globalization`), `g` is the value of `pt` on
     `I.subschemeι`. So the clause is the piece clause of `Fam.pieces` for
     `Z = I.subscheme`, `ι = I.subschemeι`.

## Relation to the derivation in the statement Markdown

The statement Markdown outlines a proof in five steps. The implementation
differs in two places. The universal family (step 2 there) is taken from the
ported FLT theorem
`exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`
instead of being glued here. The projectivity of the pieces (step 5 there) uses
the closed immersion into projective space over `ULift ℤ` that the FLT theorem
`HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`
already provides for the graded Hilbert scheme, so no comparison with a second
representing scheme is needed. The extension to all test schemes (step 3 there)
is `classification`.

## Dependencies

The statement module, the two helper modules above, and the Library modules
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated`
and
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj`.
No new definitions and no new axioms.
