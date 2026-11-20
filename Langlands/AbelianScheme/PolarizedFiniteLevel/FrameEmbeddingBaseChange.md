# Base change of frame-normalized cubic embeddings

All schemes lie in one universe `u`. For a datum `a` over `S`, a morphism `f : S' ⟶ S` and
`ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m`, the total space of
`(a.pullback f).abelian` is the fibre product `A ×_S S'`.

## Declarations

- `Datum.pullback_torsionPoint_fst`: the torsion points of `a.pullback f` lie over those of
  `a` (from `enumerateTuple_pullback`; the same computation is in the frame-locus
  base-change draft of Task 3449's subtask).
- `pullbackSection_comp_congr`, `pullbackSection_pullback_eq_iff`: equality of pullbacks of
  two sections is preserved along composites, and pulled-back sections have equal pullbacks
  along `w` exactly when the original sections have equal pullbacks along the composite
  (from `LinearSystem.pullbackSection_comp`).
- `Datum.pullbackEmbedding a f ψ`: the morphism `A ×_S S' ⟶ ℙ^m_{S'}` with components the
  projection to `S'` and `A ×_S S' → A → ℙ^m_S → ℙ^m_ℤ`.
- `Datum.pullbackEmbedding_map`, `Datum.isPullback_pullbackEmbedding`: when `ψ` lies over
  `S`, the square formed by `pullbackEmbedding`, the projection to `A`, `ψ` and
  `RelativeProjectiveSpace.map m f` is Cartesian (vertical pasting with the Cartesian square
  `isPullback_map`).
- `Datum.Realizes.pullback`: if `ψ` is a frame-normalized embedding realizing `(I, σ)`, then
  `pullbackEmbedding` realizes `(I.comap (map m f), f ≫ σ)` (Mathlib's
  `ker_fst_of_isClosedImmersion`).
- `Datum.IsFrameEmbedding.pullback`: `pullbackEmbedding` is a frame-normalized embedding of
  `a.pullback f`. Closed immersions are stable under base change; the cubic condition uses
  `Datum.cubicBundlePullbackIso` and the line bundle `f^* N`; the frame conditions use
  `vanishesAlong_pullback_iff`, `LinearSystem.vanishesAlong_comp` and the two section lemmas
  above.

## Provenance

Internal base-change lemmas for Task 7811's reduction (`FrameChartRepresentabilityReduction`).
