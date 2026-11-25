# Base change maps between affine base changes

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `bcMap K ψ : X_K ⟶ X_B` for an `R`-algebra map `ψ : B → K` (`pullback.map`), with `bcMap_fst`,
  `bcMap_snd`.
- `ptMap π p k hk : X_B ⟶ X ×_R G` for a `B`-point `k` of an `R`-scheme `p : G ⟶ Spec R`, with
  `specMap_comp` and `bcMap_ptMap`.
- `affAlg p O`: `Γ(G, O)` as an `R`-algebra through `p`; `affPt O := O.2.fromSpec`, the canonical
  open immersion `Spec Γ(G, O) ⟶ G` of an affine open, with `range_affPt` and `affPt_comp`
  (`affPt O ≫ p = specMap R Γ(G, O)`).
