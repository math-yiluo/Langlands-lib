# Centralizer unipotent subgroups in ambient Borels

`Langlands.GroupScheme.CentralizerUnipotentBorelContainmentStatement.{u}`
is a proposition target, not a proof.

Let `k : Type u` be algebraically closed, `G` a smooth connected affine group
scheme over `Spec k`, and `χ : 𝔾ₘ ⟶ G` any cocharacter, including the
trivial cocharacter. Let `j : M ⟶ G` be a closed representative of the
existing all-test-scheme dynamic centralizer of `χ`, with `M` smooth and
connected. Let `i : U ⟶ M` be a smooth connected unipotent normal closed
subgroup of `M`. For every Borel subgroup `b : B ⟶ G` containing the
range of `χ`, the range of `i ≫ j` is contained in the range of `b`.
All range containments and normality are on every test scheme. In particular,
normality is assumed in `M`, not in `G`. No reductivity assumption is made
on the ambient group.

This is the Borel-containment step in the proof of J. S. Milne,
*Algebraic Groups* (2017), Corollary 17.57, printed p.371 (zero-based PDF
page 386). Its structural input is Theorem 17.46, printed pp.365–366
(zero-based PDF pages 380–381): if a Borel subgroup contains a torus, its
intersection with the centralizer of that torus is a Borel subgroup of
the centralizer. A smooth connected normal unipotent subgroup of a
connected affine group is contained in its unipotent radical, and that
radical is contained in every Borel. Applying these facts inside `M`
places `U` in the intersection with `B`. This particular containment
step precedes the application of Chevalley's intersection theorem in
the source proof.

The target uses a possibly noninjective cocharacter rather than an
embedded torus. The source connection passes through its
scheme-theoretic image, which is a split torus in the affine group.
The cocharacter and this image have the same centralizer. Containment
of the cocharacter in the closed subgroup `B` places that image in `B`.
The trivial image is included. These image and centralizer comparisons
are part of the proof obligation, not hypotheses silently added to
the statement. Smoothness and connectedness of `M` are explicit premises
so this structural target does not duplicate the separate unrestricted
dynamic smoothness and connectedness proof tasks.

Smoothness, connectedness and affineness place `G` in the finite-type
setting of the source: its affine structure morphism is quasi-compact
and its smooth structure morphism is locally of finite presentation.
Closedness gives affineness of `M` and `U`. No choice of a preferred
centralizer representative or maximal torus occurs in the target.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read and has no
correction to Theorem 17.46 or Corollary 17.57. This module neither
proves the stated containment nor proves the unrestricted connected
reductivity of dynamic centralizers.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
