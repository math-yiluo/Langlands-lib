# Proof: the glued analytification of a scheme carries an analytic structure

Lean module: `Langlands.Geometry.Analytic.SchemeAnalytificationAnalyticStructureProof`.

Main theorem:
`Langlands.Analytic.SchemeAnalytification.schemeAnalytificationAnalyticStructure`, of
type `SchemeAnalytificationAnalyticStructureStatement.{u}`. It proves the unchanged
published statement in every universe `u`. The statement and its sources are
described in the paired Markdown of
`Langlands.Geometry.Analytic.SchemeAnalytificationAnalyticStructureStatement`.

The proof makes no assumption beyond the statement's. `K` is a complete,
ultrametric, nontrivially normed field, `X` is a scheme, and `f : X ⟶ Spec K` is
locally of finite type. No separatedness or quasi-compactness is used. The proof
does not depend on the full published `SchemeAnalytificationGluingStatement` or its
separatedness clause. It uses only the two open-gluing facts listed below, which are
proved unconditionally.

## Assembly

After introducing `K`, its instances, `X`, `f` and the finite-type instance, the
proof applies

* `analyticStructure_of_openGluing` (module
  `SchemeAnalytificationAnalyticStructure`). It proves the full conclusion of the
  statement for fixed `K`, `X`, `f` from a hypothesis `hg : OpenGluing K f`. The
  structure `OpenGluing K f` (module `SchemeAnalytificationAtlas`) has two fields:
  - `isOpenEmbedding`: every canonical map `ι K f U : U^an → Space K f`, for an
    affine open `U` of `X`, is an open embedding;
  - `range_inter`: for affine opens `U`, `V`, the intersection of the ranges of
    `ι K f U` and `ι K f V` is the union of the ranges of `ι K f W` over the affine
    opens `W ⊆ U ∩ V`.

Both fields are supplied by theorems of module `SchemeAnalytificationOpenGluing`
(namespace `OpenGluing`), whose statements match the fields exactly:

* `OpenGluing.isOpenEmbedding_ι K f U : IsOpenEmbedding (ι K f U)`;
* `OpenGluing.range_ι_inter K f U V`: the intersection formula above.

The proof term is
`analyticStructure_of_openGluing ⟨OpenGluing.isOpenEmbedding_ι K f, OpenGluing.range_ι_inter K f⟩`.

## What the imported constructions do

`analyticStructure_of_openGluing` takes as witnesses the saturated presentation
`schemePresentation hg` on `Space K f`, the identity homeomorphism, the open analytic
domains `range (ι K f U)`, and the localized isomorphisms `affineIso hg U`. Its atlas
has as charts the images of all local affinoid domains of the affine analytifications
`U^an`. The bounded restriction maps between charts coming from different affine opens
are characterized by compatibility with the scheme morphisms `Spec B → X` of the
charts. Its paired Markdown gives the details.

`OpenGluing.isOpenEmbedding_ι` and `OpenGluing.range_ι_inter` come from the quotient
gluing reduction applied to the restriction gluing data
(`OpenGluing.restrictionGluingData`). That data uses affine restriction maps that are
open embeddings, with ranges described by the local center. Its paired Markdown gives
the details.

## Credit

* `SchemeAnalytificationAnalyticStructure` and its helper modules
  `AffineAnalytificationLocalDomainMaps`, `SchemeAnalytificationAffinoidPoints`,
  `SchemeAnalytificationLocalCharts` and `SchemeAnalytificationAtlas`: Worker 901
  (Task 7120).
* `SchemeAnalytificationOpenGluing` and `SchemeAnalytificationRestrictionCoherence`:
  Worker 344 (Task 7087).
* This assembly module: Worker 901.

The target's mathematical sources are Berkovich 1990, Theorem 3.4.1 and step (3) of
its proof, and Berkovich 1993, Proposition 1.3.3, as cited in the target's paired
Markdown. The Lean proof follows their outline: it glues the analytic structures of the
affine analytifications along their open overlaps. It does not use Tate acyclicity.
Compatibility of restriction maps comes from the universal property of local affinoid
domains and from the scheme morphisms of the charts.
