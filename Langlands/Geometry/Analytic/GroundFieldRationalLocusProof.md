# Proof of the closed rational locus under analytic ground field extension

The theorem `groundFieldRationalLocus` in the namespace
`Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension` proves
`GroundFieldRationalLocusStatement` in all four of its universes. Let
\(K \to L\) be an isometric extension of complete ultrametric normed fields
and \(A\) an affinoid atlas presentation over \(K\). Write \(\pi\) for the
projection of the extended atlas `presentation K L A.atlas` to \(A\), \(R\)
for its \(L\)-rational locus and \(S\) for the \(K\)-rational locus of
\(A\). The theorem proves three facts. The preimage of \(S\) in \(R\) is
closed. \(\pi\) is injective on \(R \cap \pi^{-1}(S)\). Every point of \(S\)
is the image of a point of \(R\). The proof uses no hypothesis on the degree
of \(L\) over \(K\) or on the nontriviality of the absolute values, so it
covers infinite extensions and trivially valued fields.

The argument is the one indicated at the end of the proof of Proposition
5.11(3), p. 19, of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
There the closed embedding of rational points is checked on the
constituents of an affinoid covering. The Lean proof first works on one
chart and then glues over the extended atlas.

## One chart

Fix a presented affinoid algebra \(B\) over \(K\). Its scalar extension is
\(B_L\) (`PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L B`). It
comes with the bounded \(K\)-algebra map \(\iota: B \to B_L\) (`iota`) and
the projection of spectra `spectrumProjection K L B`, which pulls a bounded
seminorm on \(B_L\) back along \(\iota\). For a rational point \(s\), write
\(\chi_s\) for its character `BanachSpectrum.rationalCharacter s`; its
absolute values are the seminorm \(s\) (`norm_rationalCharacter`).

* `rationalCharacter_iota`: suppose an \(L\)-rational point \(t\) of
  \(B_L\) projects to a \(K\)-rational point \(s\) of \(B\). Then
  \(\chi_t(\iota b) = \chi_s(b)\) in \(L\) for every \(b \in B\). Put
  \(c = b - \chi_s(b)\cdot 1\). Then \(s(c) = |\chi_s(c)| = 0\), so
  \(|\chi_t(\iota c)| = s(c) = 0\). Expanding \(\chi_t(\iota c) = 0\) gives
  the claim.
* `spectrumProjection_mem_rationalLocus_iff`: the projection of an
  \(L\)-rational point \(t\) is \(K\)-rational exactly when every value
  \(\chi_t(\iota b)\) lies in the image of \(K\). The forward direction is the
  previous item. Conversely, the \(K\)-algebra map
  \(\varphi = \chi_t \circ \iota: B \to L\) then lands in the image of the
  algebra map \(K \to L\). Composing its codomain restriction with the
  inverse of \(K \cong \operatorname{im}(K \to L)\)
  (`AlgEquiv.ofInjectiveField`) gives a \(K\)-algebra map \(\psi: B \to K\)
  whose image in \(L\) is \(\varphi\). Since \(K \to L\) is isometric
  (`norm_algebraMap'`), \(|\psi(b)|\) equals the value at \(b\) of the
  projected seminorm. The seminorm is bounded by the norm, so \(\psi\) is
  bounded with constant \(1\), and it witnesses that the projected point is
  \(K\)-rational.
* `isClosed_spectrumProjection_rationalLocus` (with \(K\) complete): by the
  criterion, the locus is the intersection over \(b \in B\) of the preimages
  of the image of \(K\) under \(t \mapsto \chi_t(\iota b)\). Each of these
  maps is continuous on the \(L\)-rational locus
  (`BanachSpectrum.continuous_rationalCharacter_apply`). The image of \(K\) is
  closed in \(L\), because \(K \to L\) is an isometry from a complete space
  and hence a closed embedding.
* `spectrumProjection_existsUnique_rationalLift` (with \(L\) complete): for
  a \(K\)-rational point \(s\), the universal property of \(B_L\) (`lift`)
  extends the bounded map \(B \to K \to L\) (`coefficientMap` after
  \(\chi_s\)) to a bounded \(L\)-algebra map \(\psi: B_L \to L\). The
  seminorm \(t = |\psi|\) (`BanachSpectrum.comap` of `BanachSpectrum.fieldPoint L`)
  is an \(L\)-rational point, witnessed by \(\psi\). It projects to \(s\) by
  `lift_iota`, `norm_coefficientMap` and `norm_rationalCharacter`. If \(q\) is
  any \(L\)-rational point over \(s\), the first item shows that
  \(\chi_q \circ \iota\) is the map \(B \to L\) that \(\psi\) extends. So
  \(\chi_q = \psi\) by `lift_unique`, and \(q = t\) because
  \(q = |\chi_q|\).

## The atlas

The charts of `presentation K L A.atlas` come from `chartSystem K L A.atlas`.
It has the indices of \(A\) and the scalar-extended chart algebras. The
projection satisfies `projection_chart`: on the extended chart \(i\) it is the
original chart \(i\) after `spectrumProjection`. By `range_chart`, the image
of the extended chart \(i\) is the \(\pi\)-preimage of the image of the
original chart \(i\). On both atlases, a chart point is rational exactly when
its spectrum point is (`AffinoidAtlasPresentation.chart_mem_rationalLocus_iff`).

* `isClosed_projection_rationalLocus`: the extended chart images form a
  quasinet (`isNet_chartFamily`). Their preimages in \(R\) form a quasinet of
  \(R\) (`IsQuasinet.preimage_image`), so closedness may be tested on each
  member (`IsQuasinet.isClosed_iff`). The member \(W_i\) cut out by chart
  \(i\) receives a map from the \(L\)-rational locus of the \(i\)-th extended
  chart algebra. This map is an embedding, since charts are embeddings, and
  surjective by the chart rationality criterion. Hence it is a homeomorphism.
  By `projection_chart` and the chart rationality criterion on \(A\), the
  preimage of \(\pi^{-1}(S)\) under it is the chartwise locus, which is
  closed by `isClosed_spectrumProjection_rationalLocus`.
* `projection_existsUnique_rationalLift`: given \(x \in S\), choose an
  original chart \(i\) and a spectrum point \(s\) with chart image \(x\);
  \(s\) is \(K\)-rational. Its chartwise lift \(t\) gives the point
  \(z = \mathrm{chart}_i(t)\) of \(R\), and \(\pi(z) = x\) by
  `projection_chart`. Any \(y \in R\) over \(x\) lies in the image of the
  extended chart \(i\) by `range_chart`, say \(y = \mathrm{chart}_i(u)\) with
  \(u\) \(L\)-rational. Injectivity of the original chart gives that \(u\)
  projects to \(s\). By chartwise uniqueness \(u = t\), so \(y = z\).

Finally, `groundFieldRationalLocus` combines these results. The first gives
the closedness clause. Uniqueness of lifts gives injectivity of \(\pi\) on
\(R \cap \pi^{-1}(S)\), and existence gives \(S \subseteq \pi(R)\).
