# Closed loci and maps between fibre powers

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitLoci`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower`. Here `f : h_U ⟶ X` is a map
from a represented presheaf to a presheaf on `Over S`, and `P` is a published
`ChartFibrePower` of `f` indexed by a type `ι`.

## Finiteness

`fin_pr_isFinite hf ha n i`: if `f` is finite, every projection of the standard fibre power
`fin ha n` is finite. The proof is by induction on `n` and cases on `i`.

- Projection `0` of `fin ha (n + 1)` is the base change of the finite map `toBase` (the
  composite of projection `0` of `fin ha n` with `f`, finite by `IsFinite.map_comp`) along
  `f`.
- Projection `i + 1` is the finite `succSnd` followed by projection `i` of `fin ha n`.

## Diagonal and permutations

- `diag P : U ⟶ P.obj` (definition): the diagonal. It is the index map from the one-fold
  fibre power along the constant map to `0`. `diag_pr` says `diag ≫ pr i = 𝟙`, and
  `diag_perm` says `diag ≫ perm σ = diag`.
- `diag_isClosedImmersion P i hi`: if `pr i` is finite, the diagonal is a closed immersion.
  It is a section of the separated morphism `pr i` (`IsClosedImmersion.of_comp`).
- `perm_perm_inv`: `perm σ ≫ perm σ⁻¹ = 𝟙`.
- `pr_perm_apply`: `pr i (perm σ p) = pr (σ i) p` on points.
- `isDistinct_perm_iff`: `perm σ p` has pairwise distinct coordinates iff `p` has. This
  follows from `coord_mapIndex_eq_iff` and injectivity of `σ`.

## Closed and open loci

- `isClosed_coord_eq hf Q a b`: for finite `f`, the set of points of `Q` whose `a`-th and
  `b`-th coordinates agree is closed. Map `Q` to the twofold fibre power `R` by the index map
  `![a, b]`. The locus is the preimage of the set of points of `R` with equal coordinates.
  By `mem_range_mapIndex` that set is the range of the diagonal `U ⟶ R`, which is closed
  since the diagonal is a closed immersion.
- `isOpen_isDistinct hf Q`: for a finite index type, the set of points with pairwise
  distinct coordinates is open. It is a finite intersection of complements of the closed
  loci above.

## Doubled fibre powers

Here `P2` is a fibre power indexed by `ι ⊕ ι`. The index maps `Sum.inl` and `Sum.inr` give
morphisms `P2.obj ⟶ P.obj`.

- `exists_pair P P2 i₀ h`: let `w, w'` be points of `P` with the same image under
  `h_{pr i₀} ≫ f`. Then some point `p` of `P2` maps to `w` under `Sum.inl` and to `w'` under
  `Sum.inr`. A witness `T, g, g', t` of the same image gives the family
  `Sum.elim (g ≫ pr ·) (g' ≫ pr ·)`, which lifts to `l : T ⟶ P2`. Take `p = l t`.
- `inr_eq_perm_inl P P2 σ p h`: suppose the `Sum.inr i` coordinate of `p` equals the
  `Sum.inl (σ i)` coordinate for all `i`. Then the `Sum.inr` image of `p` is `perm σ`
  applied to its `Sum.inl` image. The two composites `Spec κ(p) ⟶ P.obj` agree by
  `hom_ext`. Evaluating them at the closed point of `Spec κ(p)` gives the claim
  (`fromSpecResidueField_apply`).

## Provenance

Internal helpers for the tuple-orbit construction of task 13a3a0fd (see
`TupleOrbitCover`). No source proof is transcribed.
