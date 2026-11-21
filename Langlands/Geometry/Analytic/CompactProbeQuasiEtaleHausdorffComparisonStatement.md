# Compact-probe covering sieves on Hausdorff quasi-étale objects

Author: Worker 21. The comparison interface and proof route use Worker 209's draft.

`Langlands.Analytic.SaturatedAtlasPresentation.CompactProbeQuasiEtaleHausdorffComparisonStatement K`
is a proposition, not a proof. For a complete ultrametric normed field `K`,
it quantifies over `X : LocalizedCategory.{u, v, v} (K := K)`, an object
`U` of `QuasiEtaleSite X`, and a sieve `S` on `U`. It has one separation
hypothesis: the underlying space of `U.left` is Hausdorff. The base `X`
and the sources of the arrows in `S` need not be Hausdorff.

Under this hypothesis, it states that `S` is covering in
[`compactProbeQuasiEtaleTopology X`](QuasiEtaleCompactProbeTopology.md) if
and only if `HasQuasiEtaleChartNeighborhoods S.arrows` holds. The latter
predicate on a presieve `R` means: for every point `x` of `U.left`, there is a
finite set of subsets of `U.left` whose union is a neighbourhood of `x`, each
of the form `|f| '' ((presentationOf V.left).chartDomain i).carrier` for an
arrow `f : V ⟶ U` in `R` and a chart index `i` of the presentation of
`V.left`. Here `|f|` is the underlying continuous map of `f.left`. Applying
this condition to all the arrows of `S` is equivalent to asking that there be
some presieve contained in `S` satisfying it: the condition is monotone in
the presieve, and `S.arrows` itself is such a presieve if the condition holds.

## Original sources and correspondence

- Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
  §3, printed p. 544 (PDF p. 6), describes the covering families of `Qét(X)`
  by asking that every target point have a neighbourhood that is a finite
  union of images of affinoid domains of the sources. This is the condition
  on the right-hand side of the comparison, written with the actual chart
  domains of the Library's presentations. Each such chart domain is an
  affinoid domain. Conversely, a compact affinoid domain in a source is
  covered by finitely many chart ranges of that source by the atlas net
  property. Replacing each domain in a neighbourhood witness by these
  charts may enlarge the union of images, which is still a neighbourhood.
- Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, Publ.
  Math. IHÉS 78 (1993), §1.4, Proposition 1.4.1, printed pp. 29–30 (PDF
  pp. 26–27), constructs analytic fibre products and describes their map
  to the topological fibre product. This is the geometric background for
  pulling compact sources back along a compact probe and lifting pairs of
  points with the same image. The statement here assumes neither a general
  fibre-product theorem nor a separate point-lifting hypothesis.

The equivalence is a derived comparison with the source's neighbourhood
condition, not a statement from either paper. It is only about Hausdorff
site objects and the compact-probe topology. It does not compare with the
legacy generated `quasiEtaleTopology` or prove any assertion about coverings
on non-Hausdorff objects.
