# Scheme representability from locally surjective open charts

Worker 336 proves
`Langlands.AlgebraicGeometry.AlgebraicSpace.openChartGluing.{u}` with exactly
the type of the published `OpenChartGluingStatement.{u}`. Worker 133 contributed
to the interface and the parent proof decomposition. The statement and its
entire import closure remain unchanged.

The proof introduces the actual base scheme, fppf sheaf, chart index type,
schemes over the base, actual chart maps, open-immersion proofs and local
surjectivity proof. It installs the latter as a local instance and applies
`SliceOpenGluing.exists_representation`. That construction gives an actual
scheme over the original base and a natural isomorphism of lifted-value
presheaves. The paired `SliceOpenGluing.md` describes the implemented overlap,
scheme gluing, structure-map descent, slice hypercover and sheaf comparison
arguments, including their universe and topology compatibility.

The mathematical provenance is the internal slice-fppf adaptation of Stacks
Project Lemma 26.15.4, Tag 01JJ, from the registered source
`stacks-open-chart-representability-2026-11-01`, directory SHA-256
`51771f7545361ce0b0f4f3ebe79f53f862d299ecc08344f3273aeb9a8dc84201`.
The retained directory is
`/home/taskhub/pilot/literature/Stacks Project - Open chart representability (HTML snapshot 2026-11-01)`;
`01JJ.html` and `01JJ.txt` contain the original and reading aid. The source's
absolute Zariski statement motivates the criterion; the implementation proves
the published slice-fppf statement directly. It does not assume a comparison
with a smaller-value or absolute presheaf.

The lifted-Yoneda helpers and comparison adapt the registered external source
`external-lean-reuse-snapshots-2026-10-21`, directory SHA-256
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
file `n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/LocalGeometry/LocalRepresentabilityULift.lean`,
NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The helper's header preserves the original notices, upstream attribution
links, and Naganori Yamaguchi's local adaptation notice.

The theorem keeps arbitrary universe `u` and base `S`, the original index
type, actual represented charts and the actual fppf sheaf. No affineness,
finiteness, separation or prior scheme representation is assumed. This unit
proves open-chart gluing; the thickening lifting, affine descent and final
schemeness results are separate units.
