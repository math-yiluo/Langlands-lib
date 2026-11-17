# Reductivity and semisimplicity over a direct limit of rings

Worker 606, with the fibre-locus comparisons of Worker 634.

`Langlands.GroupScheme.directLimitReductive.{u}` proves exactly the unchanged
published `Langlands.GroupScheme.DirectLimitReductiveStatement.{u}`. It applies
to every directed preorder, diagram of commutative rings, colimit cocone and
smooth affine group over an initial term. It adds no hypotheses and imposes no
restriction on the transition maps.

The implemented proof applies the published
`directLimitReductive_of_semisimpleLocusOpen` from
[`DirectLimitAssembly`](DirectLimitAssembly.md) to the published theorem
`identityComponentSemisimpleLocusOpen` from
[`IdentityComponentSemisimpleLocusProof`](IdentityComponentSemisimpleLocusProof.md).
The latter discharges the assembly's sole remaining premise in the same
arbitrary universe `u`.

The assembly detects fullness of the reductive and semisimple identity-component
loci using their openness and compatibility with actual base change. It detects
geometric connectedness using its constructible fibre locus. Directedness gives
a common eventual stage for connectedness and locus fullness. The fibre-locus
comparisons then yield all four equivalences of the target: reductivity of all
geometric identity components, whole-group reductivity, semisimplicity of all
geometric identity components, and reductivity with semisimple whole geometric
fibres. Semisimplicity retains the Library's finite scheme-theoretic centre.

This is a derived composition of the two proved Library results. The
[`target's companion`](DirectLimitReductiveStatement.md) records its provenance
in Conrad's Corollary 3.1.11. The target pair and its imported pairs are unchanged.
