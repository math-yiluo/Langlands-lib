# Étale continuity for the compact-probe quasi-étale topology

`CompactProbeEtaleContinuityStatement` gives continuity of the inclusion of
small étale tests into quasi-étale tests with the compact-probe topology.
The base \(X\) varies over saturated localized analytic spaces over a
complete ultrametric field \(K\), with independent field and atlas
universes. The covering test uses the compact Hausdorff probes of
`compactProbeQuasiEtaleTopology`. On Hausdorff test objects,
`compactProbeQuasiEtaleHausdorffComparison` identifies this test with
the chart-neighbourhood description.

`compactProbeEtaleContinuity_of_comp` reduces the statement to composition
of quasi-étale arrows, the composition clause of the 1994 paper's
Lemma 3.1(i). The proof uses flatness of the étale inclusion and starts
with a jointly surjective family of étale tests. After pulling back along
an arrow from a compact Hausdorff probe, point lifting gives a preimage
of each probe point. Étale openness gives a neighbourhood formed by
finitely many chart images around the preimage. Each chart is compact
Hausdorff, and its map to the base factors through the original covering
arrow. Quasi-étale composition supplies its structure map in the
quasi-étale site. Compactness of the probe gives finitely many such
charts covering it. The argument permits a non-Hausdorff test object as
the target of the probe.

## Sources

- Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
  (1994), §3, printed p. 544 (PDF p. 6). Lemma 3.1(i) gives
  composition, and the following paragraphs describe the covering
  families and the morphism \(X_{\mathrm{q\acute et}}\to X_{\mathrm{\acute et}}\).
  Literature ID `berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
  `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
- Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
  (1996 manuscript), §1.2, printed and PDF p. 3. Taking the trivial
  group in \(\mu_G\) gives the ordinary inclusion. Literature ID
  `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
  PDF SHA-256
  `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
- Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
  Publ. Math. IHÉS 78 (1993), Proposition 1.4.1, printed pp. 29–30
  (PDF pp. 26–27), supplies the analytic fibre-product point geometry.
  Literature ID `berkovich-1993-etale-cohomology`, SHA-256
  `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
