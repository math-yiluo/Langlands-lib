# Varying-dimension analytic structures on all smooth-space rational points

This is derived definition content supporting the analytic-manifold clause of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.15, Proposition 5.4, and the final paragraph of its proof on
printed p.16. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
For a complete field and a smooth space, Conrad asserts a unique analytic
structure on the rational points that is functorial, carries étale maps to
local analytic isomorphisms and agrees with the known scheme case. He allows
the dimension to vary between components. The source does not state the
family-level structure or the coordinate predicates below. They are the Library's
packaging of the objects that clause quantifies over, so that the existence and
uniqueness assertions can be stated as separate Prop-valued targets.

All declarations are in `Langlands.AlgebraicGeometry.AlgebraicSpace`. Let
`K : Type u` be a nontrivially normed field. The point set of a space `X` over
`Spec K` is always the original `RingPoints K X K`, with the independently
defined topology `etaleChartTopology K X`. The coordinate space in dimension
`m` is `Fin m → K` with its usual normed-space structure. `ω` is Mathlib's
analytic differentiability class.

This module imports only the published modules `SmoothSourceAnalyticAtlas`
and `AnalyticPointUniqueness`. It uses their `DimensionPointAtlas` predicates
`IsAnalytic`, `AnalyticMap`, `IsLocalAnalyticIso` and `Equivalent` unchanged.

## Affine space lies in the class

The three theorems `affineSpace_smoothOverBase n`,
`affineSpace_isQuasiSeparated n` and `affineSpace_isLocallySeparated n`
concern the actual algebraic space of the polynomial affine `n`-space scheme
`affineSpaceOver K n`. They prove that it is `SmoothOverBase`,
`IsQuasiSeparated` and `IsLocallySeparated`. The first one applies the published
`SmoothOverBase.of_scheme` to the smoothness obtained from
`smoothOfRelativeDimension_affineSpace n`. The other two project the published
`isSmoothPureDimensional_affineSpace n`. These facts let the affine-space
normalization below evaluate a family on `Aⁿ` for every `n`, including `n = 0`.

## Analytic maps to and from coordinate space

Let `A : DimensionPointAtlas hX` for `hX : SmoothOverBase X`.

- `A.AnalyticToModel g`, for `g : RingPoints K X K → (Fin m → K)`, is the
  conjunction of `Continuous g` for the original topology with
  `ContDiffOn K ω (g ∘ e.symm) e.target` for every dimension `n` and every chart
  `e ∈ A.atlas n`.
- `A.AnalyticFromModel h`, for `h : (Fin m → K) → RingPoints K X K`, is the
  conjunction of `Continuous h` with
  `ContDiffOn K ω (e ∘ h) (h ⁻¹' e.source)` for every dimension `n` and every
  chart `e ∈ A.atlas n`.

These are the two halves of analyticity against the identity chart of `Kᵐ`.
The tests use every chart of every dimension, on the chart's whole target or on
the whole preimage of its source. Continuity is stated separately, as in the
published `AnalyticOn`.

## The family structure

`DimensionAnalyticStructure K` is a structure with one field, `atlas`. For every
actual algebraic space `X` over `Spec K`, every `hX : SmoothOverBase X`, and
proofs of `IsQuasiSeparated X` and `IsLocallySeparated X`, it gives a
`DimensionPointAtlas hX` on the original points of `X`. This is the varying-
dimension counterpart of the published pure-dimensional
`AnalyticPointStructure K`. There is no fixed dimension and no finiteness of the
set of dimensions. The class is the corrected Proposition 5.4 class of smooth,
quasi-separated, locally separated spaces. The structure has no analytic,
functoriality or agreement field. Each such law is one of the separate
predicates below.

For `Φ Ψ : DimensionAnalyticStructure K`:

- `Φ.IsAnalytic`: for every space of the class, `(Φ.atlas X hX hqs hls).IsAnalytic`.
  Every same-dimension transition is analytic on its full source.
- `Φ.IsFunctorial`: for all spaces `X` and `Y` of the class and every morphism
  `f : X ⟶ Y`, the actual point map `RingPoints.map (A := K) f` is an
  `AnalyticMap` from the atlas of `X` to that of `Y`. By the published definition
  this includes continuity and tests every source and target dimension pair.
  Different dimensions on the two sides are allowed.
- `Φ.IsEtaleLocalIso`: for all spaces `X` and `Y` of the class and every
  `f : X ⟶ Y` with `IsEtaleMorphism f`, the actual point map is an
  `IsLocalAnalyticIso` between the two atlases. By the published definition this
  includes preservation of intrinsic point dimension, and also local branches
  that are open partial homeomorphisms of the original point spaces, analytic
  with analytic inverses.
- `Φ.AgreesWithAffineSpace`: for every `n`, there is an equivalence
  `c : RingPoints K Aⁿ K ≃ (Fin n → K)` with `c x = affineSpaceCoordinates K n x`
  for all `x`. Moreover `c` is `AnalyticToModel` and `c.symm` is
  `AnalyticFromModel` for `Φ`'s atlas on `Aⁿ`. Here `Aⁿ` is the algebraic space
  of `affineSpaceOver K n`, with the three class proofs above. So the actual
  polynomial coordinate map is a bijection that is analytic in both directions.
- `Φ.IsAdmissible` is the conjunction of these four conditions.
- `Φ.Equivalent Ψ`: for every space of the class, the published
  `DimensionPointAtlas.Equivalent` holds between the atlases of `Φ` and `Ψ`.
  That is, the actual identity of `X(K)` is analytic in both directions.

Scheme agreement is encoded by this affine-space normalization, mirroring the
published pure-dimensional `AnalyticPointStructure.AgreesWithAffineSpace`. That
definition asks for an analytic `Diffeomorph` equal to `affineSpaceCoordinates`.
Here the atlas is not a Mathlib `ChartedSpace`, so the same requirement is
written as an equivalence with the two chart-wise analyticity conditions.
Together with functoriality and étale local analytic isomorphisms, this
normalization is the input of the uniqueness argument used for the published
pure-dimensional `AnalyticPointStructure.equivalent_of_isAdmissible`. Agreement
with a separately defined analytic structure on every smooth scheme is not
encoded here. That would be a separate comparison statement.

## The structure determined by a pure-dimensional family

For `σ : AnalyticPointStructure K` and `hK : IsHenselianValuedField K`,
`σ.dimensionStructure hK` is the `DimensionAnalyticStructure K` whose atlas on
each space of the class is the published concrete lifted atlas
`σ.dimensionAtlas hK hX hqs hls`. The simp lemma
`AnalyticPointStructure.dimensionStructure_atlas` records this by `rfl`. No
analyticity of `σ` is assumed for the construction.

## Scope and related modules

This module contains definitions and three structural lemmas about affine space
only. It does not prove that any family is admissible, or that admissible
families exist or are unique. The later statements, each with its own module
and each proved in the Library, are:

- for an admissible pure-dimensional `σ` over a henselian field,
  `σ.dimensionStructure hK` satisfies `AgreesWithAffineSpace`
  (`SmoothSourceDimensionAffineAgreementStatement`). Together with
  the separate assembly, functoriality and étale statements for
  `σ.dimensionAtlas`, this would make it `IsAdmissible`;
- any two admissible `DimensionAnalyticStructure`s are `Equivalent`
  (`SmoothSourceDimensionAnalyticUniquenessStatement`);
- over complete fields an admissible structure exists, and it is unique up to
  `Equivalent` (`SmoothSourceAnalyticManifoldStatement`). This is the
  varying-dimension source-level clause of Proposition 5.4.

Uniqueness here concerns the whole varying-dimension family. That is a stronger
assertion than the published choice independence for pure-dimensional families,
and the two should be kept distinct. This module does not discharge
Proposition 5.4.
