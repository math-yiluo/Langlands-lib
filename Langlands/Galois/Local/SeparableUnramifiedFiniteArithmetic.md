# Finite arithmetic for canonical spectral integer rings

Worker 60. This helper unit develops the finite arithmetic used by the separable
unramified proof. It leaves the published target and its imports unchanged.

The spectral integer ring in an algebraic extension is the integral closure of
the base integer ring by `integral_iff_mem_spectralIntegers`. For a finite
separable extension with principal base integer ring, Mathlib's integral-closure
finiteness, freeness and rank theorems give a finite free module whose rank is
the field degree. The local base integer ring is a DVR by transport of the
supplied local-field integer ring across `localNormedField_integer`.

For a local algebra R → S, `residueFiberMap R S` is the canonical k_R-algebra
map S/m_R S → k_S, obtained from the inclusion m_R S ⊆ m_S and quotient
factorization. Its construction requires neither finiteness nor freeness.
For a finite free local algebra, the quotient S/m_R S has dimension
rank_R S over k_R. The canonical surjection `residueFiberMap R S` is an isomorphism
exactly when m_R S = m_S. Finite-dimensional linear algebra therefore identifies
the mapped-maximal-ideal condition with equality of residue degree and field
degree. The finite base residue field makes every residue extension separable.
The resulting criterion applies to every finite intermediate field of the
actual separable closure, with no normality assumption and in either
characteristic.

This is an internal derived proof route to the finite complete-DVR criterion in
Serre, *Local Fields* (1979), III §5 Theorem 1, printed p. 53. Its finiteness/rank
input corresponds to II §2 Proposition 3 and its corollaries, printed pp. 28–29.
The route uses a quotient dimension argument rather than a ramification-index
calculation. The originals at PDF pp. 36–37 and 60 were read, together with Serre's
2019 corrections at PDF pp. 2–3; no correction changes these passages.

The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The registered corrections are `serre-book-corrections-2019`, retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA-256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.

The quotient-map definition and its auxiliary facts are derived from the
published local-algebra maps and Mathlib's quotient constructions. This
unit supplies neither inertia fixedness nor the exact closed target proof.
`arithmeticUnramified_iff_residue_finrank` uses the independent arithmetic
predicate unchanged. Spectral and integral-closure results are imported by
Lean name; no characteristic-zero or perfection assumption on F is added.
