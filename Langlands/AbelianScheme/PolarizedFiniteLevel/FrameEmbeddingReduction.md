# Frame-normalized cubic embeddings from the field Lefschetz theorem

This module proves the reduction (a proved definition, as for the other published
reductions of this directory)

```
def frameEmbeddingExistence_of_cubicFieldEmbedding
    (HF : CubicFieldEmbeddingStatement.{u}) :
    FrameEmbeddingExistenceStatement.{u}
```

The published statement `FrameEmbeddingExistenceStatement` follows from the
published field Lefschetz statement `CubicFieldEmbeddingStatement`. That
statement is the only premise. It is an explicit hypothesis `HF`, and this
module does not prove it. The theorem is universe-polymorphic in `u` and adds no
other hypothesis: the base `S` is locally noetherian, `0 < d`, and the frame
locus of `ρ` is `⊤`, as in the target statement. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Notation

Fix `P`, a locally noetherian scheme `S`, `g d n` with `0 < d`,
`a : Datum P S g d n`, `m = cubicProjectiveDimension g d` and a frame
`ρ : Fin (m + 2) → Fin (2 * g) → ZMod n` with `a.frameLocus ρ = ⊤`. Write
`π = a.abelian.X.hom`, `L³ = a.cubicBundle`, `M = a.rigidificationModule`
(`= π_* L³`), and `t_r = a.torsionPoint r`.

- `Datum.frameLine a ρ` is the line bundle `Λ = t_last^* L³` on `S`, where
  `last = Fin.last (m + 1)`.
- `Datum.frameTwist a ρ` is the line bundle
  `L³ ⊗ π^* Λ^∨ = LineBundle.tensor P.preservation L³ (π^* Λ.dual)` on the
  abelian scheme.
- `frameCoordinate m i = ⟨i.castSucc, _⟩` indexes the non-last frame entries
  by the projective coordinates `i : Fin (m + 1)`. It is injective.

## Torsion evaluations of twisted sections

- `Datum.torsionPullbackIso a r : 𝟭 ≅ π^* ⋙ t_r^*` is assembled from the
  identity, congruence and composition comparisons of pullback.
  `Datum.torsionEvaluation_eq_torsionPullbackIso` writes the published
  `a.torsionEvaluation r` through it (by `rfl`). It has a distinct name because
  the Library module `FrameLocusBaseChangeProof` already exports
  `Datum.torsionEvaluation_eq`, a different expression of the same morphism.
- `Datum.pullback_map_cubicAdjoint`: for `τ : Λ' ⟶ M`, pulling back the
  adjoint `π^* τ ≫ a.cubicEvaluationAdjoint` along `t_r` gives
  `τ ≫ a.torsionEvaluation r` up to that isomorphism. This is the naturality of
  `Datum.torsionPullbackIso`.
- `Datum.frameSection a ρ τ`, for `τ : Λ ⟶ M`, is the twisted section
  `twistedSection π Λ (π^* τ ≫ a.cubicEvaluationAdjoint)` of the frame twist
  (module `LinearSystem.LineTwistedSections`). Three lemmas follow from that
  module and the previous lemma. For every torsion section `t_r`:
  `Datum.pullbackSection_frameSection_eq_zero` (the pullback along `t_r` is
  zero if `τ ≫ a.torsionEvaluation r = 0`);
  `Datum.pullbackSection_frameSection_congr` (the pullbacks along `t_r` agree
  if the evaluations agree); and
  `Datum.trivializationOpen_pullbackSection_frameSection` (the pullback
  generates everywhere if `τ ≫ a.torsionEvaluation r` is an isomorphism).

## The fibres

In the next three groups, `τ` is a family indexed by the non-last entries with
`hoff` (`τ i ≫ a.torsionEvaluation (ρ j) = 0` for `i ≠ j`) and `hdiag`
(`τ i ≫ a.torsionEvaluation (ρ i)` is an isomorphism).
`Datum.frameSections a ρ τ i = a.frameSection ρ (τ (frameCoordinate m i))`.

- `Datum.torsionPoint_mem_frameSections`: for all `z : S`, the point
  `t_{ρ j}(z)` lies in the trivialization open of `frameSections i` if and only
  if `i = j`.
- `Datum.fibreTorsionPoint a r z : Spec κ(z) ⟶ π.fiber z` is the lift of
  `S.fromSpecResidueField z ≫ t_r` to the residue fibre.
  `Datum.fibreTorsionPoint_mem_frameSections` is the same criterion for the
  pulled back sections on the fibre.
- `Datum.fibreTwistIso a ρ z` is an isomorphism from the pullback of the frame
  twist to the fibre `π.fiber z` onto the cubic bundle of the residue datum
  `a.pullback (S.fromSpecResidueField z)`. It combines four ingredients: the
  canonical tensor comparison; a trivialization of the pulled back dual line,
  obtained from the published `fieldLineBundleTriviality` over `κ(z)`; the
  right unitor; and the published `Datum.cubicBundlePullbackIso`. Which
  trivialization is chosen does not matter, because Lefschetz's theorem is
  applied to an arbitrary basis.
- `Datum.fibreFrameSections a ρ τ z i` is the image of the pulled back section
  under this isomorphism, as a global section of the residue datum's cubic
  bundle.

The next three results also assume `hoff` and `hdiag`.

- `Datum.pullbackSection_fibreFrameSections_eq_zero_iff`: the pullback of
  `fibreFrameSections z i` along `fibreTorsionPoint (ρ j.castSucc) z` vanishes
  if and only if `i ≠ j`. This uses the published `vanishesAlong_field_iff` and
  `trivializationOpen_mapIso`.
- `Datum.linearIndependent_fibreFrameSections`: the `m + 1` sections
  `fibreFrameSections z i` are linearly independent over `κ(z)`. Evaluate a
  vanishing linear combination at the fibre torsion point of index `j`. The
  `κ(z)`-action on relative global sections is the published
  `CechResolution.relativeGlobalSections_smul`. The published
  `pullbackSection_smul` turns this action into multiplication by the image of
  the coefficient in `Γ(Spec κ(z), ⊤)`, because the fibre torsion point is a
  section of the fibre structure map. Only the `j`-th term survives, and its
  evaluation is nonzero. So the coefficient is zero.
- `Datum.frameSections_fibre` (with `HF`, `0 < d` and
  `hM : IsLocallyFreeOfRank M (m + 1)`): for every `z : S`, the sections
  generate on the fibre `π.fiber z`, and the relative linear-system map of the
  pulled back sections on that fibre is a closed immersion. The published
  `Datum.cubicFibreSectionBasis` provides a basis with `m + 1` elements. Its
  hypotheses come from the published `exists_affine_frameOpen` and
  `cubicDirectImage`. So the independent sections form a basis
  (`basisOfLinearIndependentOfCardEqFinrank`). The first clause of `HF` with the
  published `Datum.basis_generates` gives generation. The second clause of `HF`
  for this basis gives the closed immersion. The published
  `relativeLinearSystemMap_mapIso` and `relativeLinearSystemMap_congr` transfer
  it to the pulled back sections.

## Assembly

- `mem_nonvanishingLocus_iff_mem_trivializationOpen` restates the published
  `lineBundleResidueOpenComparison` pointwise. `relativeLinearSystemMap_congr`
  says that the relative linear-system map depends only on its sections.
- `isClosedImmersion_relativeLinearSystemMap_of_fibres`: for a proper
  `p : X ⟶ S'` and generating sections, the relative linear-system map is a
  closed immersion if, on every residue fibre, the linear-system map of the
  pulled back sections is. The proof applies the published
  `isClosedImmersion_iff_relativeFibre_of_isProper`. It identifies the
  published `relativeFibreMap` with the fibre map, using
  `RelativeProjectiveSpace.isPullback_map`, `pullback.congrHom` and the
  published `relativeLinearSystemMap_pullback`.
- `pullbackSection_relativeLinearSystemMap_coordinate`: the pullback of the
  `i`-th coordinate section of `𝒪(1)` along `f ≫ relativeLinearSystemMap p hs`
  is the image of `pullbackSection f _ (s i)` under canonical isomorphisms. This
  uses the published `relativeLinearSystemTwistIso_coordinate`.

**Proof of `frameEmbeddingExistence_of_cubicFieldEmbedding`.**
`Datum.exists_normalizedFrame` (module `FrameNormalization`) gives `e` and the
maps `τ_i = Pi.ι _ i ≫ e.hom` with `hoff`, `hdiag` and the identity evaluation
at the last entry. The rank `hM` comes from the published `cubicDirectImage`
and `Datum.cubicProjectiveRank`. Each point `x` of the abelian scheme lies on
the fibre over `π x` (`Scheme.Hom.asFiber`). So the fibre generation of
`Datum.frameSections_fibre` gives generation `hgen` of the sections `σ_i`.
Set `ψ = relativeLinearSystemMap π hgen`. Then:

- `toBase` is the published `relativeLinearSystemMap_toBase`;
- `isClosedImmersion` follows from
  `isClosedImmersion_relativeLinearSystemMap_of_fibres` and the second clause
  of `Datum.frameSections_fibre`;
- `cubic` holds with `N = Λ.dual`, by the published
  `relativeLinearSystemTwistIso`;
- `basis`: for `k ≠ j`, `σ_k` pulls back to zero along `t_{ρ j.castSucc}`, so
  the `k`-th coordinate vanishes at `t_{ρ j.castSucc} ≫ ψ`;
- `unit`: all `σ_i` have the same pullback along `t_last`, since every
  `τ_i ≫ a.torsionEvaluation (ρ last)` is the identity. So all coordinates
  have the same pullback along `t_last ≫ ψ`.

## Provenance and scope

This proves the implication `CubicFieldEmbeddingStatement →
FrameEmbeddingExistenceStatement`, not `FrameEmbeddingExistenceStatement`
itself. Applying this theorem to a proof of `CubicFieldEmbeddingStatement`
yields the target. The mathematical route is that of
the statement's Markdown and of Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, 3rd ed. (1994), §7.2, printed p.131 (PDF p.144 of registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
There the embedding into `P_m × S` is determined by a linear rigidification of
`π_* L³`, and `𝒪(1)` pulls back to `L³` twisted by a line bundle from the base.
The fibrewise linear-independence argument and the closed-immersion criterion
via residue fibres are this formalization's own route.
