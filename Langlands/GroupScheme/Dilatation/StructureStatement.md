# Smoothness and geometric connectedness of group-scheme dilatations

`SmoothDilatationStatement` concerns `M.dilatation hϖ j` along an actual
closed subgroup `j : Y ⟶ M.specialFibre` of a smooth affine integral group
model `M`. The base is a DVR with specified fraction field and uniformizer.
Smoothness of `Y` over the residue field gives smoothness of the dilatation.
Under the same smoothness hypotheses, geometric connectedness of `Y` gives
geometric connectedness of the special fibre. If the supplied generic group
is geometrically connected as well, the dilatation has geometrically
connected fibres.

`SmoothCongruenceModelsStatement` concerns the actual `M.congruenceModel` at
every positive level. For a smooth `M`, these models are smooth and their
special fibres are geometrically connected. If the supplied generic group
is geometrically connected, all their fibres are geometrically connected.
`DilatationStructureStatement` is the conjunction of these two assertions.

## Source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Appendix A.5,
Lemma A.5.10, printed pp. 635–636 (PDF pp. 666–667), states the smoothness
result over a Henselian DVR for a smooth affine scheme and a smooth closed
centre in the special fibre. For connectedness of the fibres it additionally
assumes that the original fibres and the centre are connected and that the
dilatation has an integral point. In the group case the unit supplies the
integral point after any base extension. The proof in A.5.10 uses the
connectedness of the centre for the special fibre and uses the original
model for the generic fibre. The statements express this argument for
geometric connectedness with the two relevant fibres explicit. The
regular-embedding and blow-up argument is local over the DVR, allowing the
statements over a general DVR.

For the positive-level consequences, Definition A.5.12 uses the repeated
identity-centre dilatation, with each identity centre smooth and geometrically
connected over the residue field. Lemma A.5.13(2) and Remark A.5.14
identify that iteration with the single-rescaling model used here, printed
pp. 636–637 (PDF pp. 667–668).

Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
