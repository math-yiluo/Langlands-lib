# Rational points over an extension of henselian valued fields

Author: Worker 105.

`HenselianExtensionPointEmbeddingStatement` states part (3) of Proposition 5.11 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.18. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
defines one auxiliary predicate and states the result. It contains no proof.

Conrad's Proposition 5.11 (printed p.18) begins: "Let `k′/k` be an extension of
henselian valued fields, and `X` a (quasi-separated) algebraic space locally of finite
type over `k`." Part (3) reads: "Assume `X` is covered by separated Zariski-open
subsets. The natural map `X(k) → X(k′) = X_{k′}(k′)` is a topological embedding, and it
is a closed embedding when `k` is closed in `k′`." Conrad adds: "We will not use (3)
(whose proof rests on [CT] when `[k′ : k]` is infinite)."

## Objects

`K` and `K'` are fields in one universe `u`. The algebraic spaces are the Library's
actual algebraic spaces over `Spec K` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. Apart from the new predicate
below, the statement uses only published definitions.

- `IsHenselianValuedField K` (from
  `Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointStatement.lean`) says
  that the norm of the nontrivially normed field `K` extends uniquely to an absolute
  value on every algebraic extension field. This is Conrad's definition of a henselian
  valued field (printed p.14).
- `IsQuasiSeparatedLocallyFiniteType K X` (from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianSpacePointTopologyStatement.lean`)
  says that `X` is quasi-separated and locally of finite type over `Spec K`.
- `RingPoints K X A` (from `RingPoints.lean`) is the set `X(A)` of `A`-valued points
  for a `K`-algebra `A`. `RingPoints.map j` is the map on `A`-valued points induced by a
  morphism `j`. `RingPoints.changeRing φ` is the map `X(A) → X(B)` induced by a
  `K`-algebra map `φ : A → B`.
- For a morphism `j` of algebraic spaces, `hom j` is its underlying transformation of
  presheaves. `IsOpenImmersion (hom j)` (from `SchemeLocalGeometry.lean`) says that `j`
  is representable and every base change of it to an actual scheme is an open
  immersion of schemes. `IsSeparated U` (from `RingPoints.lean`) says that the diagonal
  of `U` over `Spec K` is a representable closed immersion.
- `baseChange (Spec.algebraMap K K') X` (from `SpaceBaseChange.lean`) is the base change
  `X_{K'}` along `Spec K' ⟶ Spec K`, and `baseChangeRingPointsEquiv K K' K' X` is the
  identification `X_{K'}(K') ≃ X(K')`.
- `etaleChartTopology F Y` (from `EtaleChartTopology.lean`) is the strongest topology on
  `Y(F)` making every map `U(F) → Y(F)` continuous, for étale maps `U → Y` from actual
  schemes of finite type over `F`, with the scheme point topology on `U(F)`. This is the
  topology Conrad constructs in the proof of Proposition 5.4.

## Definitions and the statement

- `IsCoveredBySeparatedOpenSubspaces K X`, for a field `K` and an algebraic space `X`
  over `Spec K`, says: for every field `L : Type u` that is a `K`-algebra and every
  point `x : RingPoints K X L`, there are an algebraic space `U` over `Spec K` and a
  morphism `j : U ⟶ X` with `IsOpenImmersion (hom j)` and `IsSeparated U` such that `x`
  lies in the image of `RingPoints.map j : U(L) → X(L)`.
- `HenselianExtensionPointEmbeddingStatement` says: let `K` and `K'` be nontrivially
  normed fields with a normed `K`-algebra structure on `K'` (`NormedAlgebra K K'`), both
  satisfying `IsHenselianValuedField`. Let `X` be an algebraic space over `Spec K` with
  `IsQuasiSeparatedLocallyFiniteType K X` and `IsCoveredBySeparatedOpenSubspaces K X`.
  Let `φ` be the map

  `x ↦ (baseChangeRingPointsEquiv K K' K' X).symm (RingPoints.changeRing (Algebra.ofId K K') x)`

  from `RingPoints K X K` to `RingPoints K' X_{K'} K'`. Give the source
  `etaleChartTopology K X` and the target `etaleChartTopology K' X_{K'}`. Then `φ` is a
  topological embedding (`Topology.IsEmbedding`), and if the image of `algebraMap K K'`
  is closed in `K'`, then `φ` is a closed embedding (`Topology.IsClosedEmbedding`).

## Relation to the source and derived content

An extension `k′/k` of valued fields is a field extension whose absolute value
restricts to that of `k`. A normed algebra structure gives exactly this:
`‖algebraMap K K' c‖ = ‖c‖` for all `c` (Mathlib's `norm_algebraMap'`). Conversely, a
norm-preserving embedding `K → K'` makes `K'` a normed `K`-algebra, since then
`‖c • x‖ = ‖c‖ * ‖x‖`. The extension may have infinite degree.

Conrad's "natural map `X(k) → X(k′) = X_{k′}(k′)`" is `φ`: a rational point is viewed
as a `k′`-valued point along `k → k′`, and `X(k′) = X_{k′}(k′)` is the Library's
base change identification of points. Conrad's topologies are those of Proposition 5.4
over `k` and over `k′`. The statement uses the étale-chart topology over both fields.
Conrad's existence proof of Proposition 5.4 (printed p.15) asserts that this topology
has all the properties of Proposition 5.4; that claim is stated separately as
`EtaleChartTopologyAdmissibleStatement`, and with the uniqueness part of Proposition
5.4 it identifies the étale-chart topology with the topology of Proposition 5.4 on
quasi-separated spaces locally of finite type. The base change `X_{K'}` is again
quasi-separated and locally of finite type over `K'` (`IsQuasiSeparated.baseChange` and
`HasAtlasProperty.baseChange` in `SpaceBaseChange.lean`). "`k` is closed in `k′`" is
read as closedness of the image of `K` in `K'` for the norm topology.

`IsCoveredBySeparatedOpenSubspaces` is a derived formulation of "covered by separated
Zariski-open subsets", stated through field-valued points to avoid an index type. It
agrees with the usual notion by the Stacks Project, registered source
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, Properties of Algebraic
Spaces:

- Definition 4.1 (Tag 03BU): the points `|X|` of an algebraic space are equivalence
  classes of morphisms from spectra of fields into `X`. Since `X` lies over `Spec K`,
  such a morphism `Spec L → X` is a point `x : RingPoints K X L` for the induced
  `K`-algebra structure on `L`.
- Lemma 4.8 (Tag 03BZ): a family of open subspaces of `X` is a Zariski covering if and
  only if their underlying sets cover `|X|`.
- Lemma 4.9 (Tag 03IE): a morphism `Y → X` factors through an open subspace `X′` if and
  only if `|Y| → |X|` lands in `|X′|`. For `Y = Spec L` this says that `x` factors
  through `X′` exactly when its point of `|X|` lies in `|X′|`.

The open immersion `j : U ⟶ X` identifies `U` with an open subspace of `X`. So `X` has a
Zariski covering by separated open subspaces exactly when every field-valued point
factors through some separated open subspace, which is the predicate. Separatedness of
`U` is over `Spec K`; since `Spec K` is separated, this agrees with the absolute notion.

Quasi-separatedness is Conrad's standing convention for Section 5 (printed p.13). Also
derived here: the names of the predicate and the statement, and the packaging of the
embedding and closed-embedding conclusions in one conjunction.

## Not stated here

- Part (1) of Proposition 5.11, on Weil restriction along a finite extension, needs the
  Weil restriction of algebraic spaces from Conrad's Lemma 5.10 and is not part of this
  statement. Part (2), the embedding into points over the completion, is stated
  separately as `HenselianCompletionPointEmbeddingStatement`.
- Conrad's proof (printed p.19) reduces to complete fields by (2), treats finite degree
  through the closed immersion `X → Res_{k′/k}(X_{k′})`, and treats infinite degree
  through the rigid-analytic analytification of Conrad–Temkin [CT]. It also records,
  for finite degree, that the embedding holds without completeness whenever the
  diagonal of `X` is a quasi-compact immersion. These are proof material and are not
  stated here.
