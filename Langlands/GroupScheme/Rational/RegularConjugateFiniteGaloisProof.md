# Proof: finite Galois conjugacy to a point with toral centralizer

Worker 1296.

`Langlands.GroupScheme.regularConjugateFiniteGalois` proves the Library
statement `Langlands.GroupScheme.RegularConjugateFiniteGaloisStatement.{u}`
(module `Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisStatement`),
for an arbitrary universe `u`. See that statement's Markdown for its meaning
and provenance. The proof follows the argument in that Markdown, with the
transporter shown to be smooth (not only geometrically reduced). No
hypothesis is added: `K` is any field, including imperfect and finite fields,
and `E` is any field extension of `K`.

## Setting

`K`, `L` are fields with `L/K` finite Galois, and `G` is a connected reductive
group over `Spec K`; only its affineness (`IsAffineHom G.X.hom`) is used.
`z : Spec L ⟶ G` is a point whose all-test centralizer in `G_L` is contained
in a closed torus `j : S ⟶ G_L`. `x` is a rational point of `G`, `E` a field
over `K`, `q : Spec E ⟶ Spec L` a morphism over `Spec K`, and
`g : Spec E ⟶ G` satisfies `g * x * g⁻¹ = q ≫ z`.

## Step 1: the centralizer of `x` is a closed torus

`G` is affine over `Spec K`, hence separated, so
`pointCentralizer_isClosedRepresentable` (in
`Langlands/GroupScheme/PointCentralizer.md`) gives a group scheme `T` and a
closed subgroup `i : T ⟶ G` representing the all-test centralizer of `x`.

- `isRepresentedBy_pointCentralizer_of_le` turns the containment hypothesis
  on `z` into the statement that `j` represents the centralizer of `z` in
  `G_L`.
- `isTorus_of_isRepresentedBy_pointCentralizer` (in
  `Langlands/GroupScheme/Rational/RegularConjugateCentralizerTorus.md`) then
  shows that `T` is a torus.
- Every point `c` commuting with `x` lies in the centralizer, which equals the
  range of `i`, so `c` factors through `i`.

This gives the first three conclusions, `IsTorus T`, `IsClosedSubgroup i` and
the containment of the centralizer.

## Step 2: the transporter is smooth over `L`

Let `o = conjugationOrbitMap G x` and let the transporter be
`P = pullback z o` in `Over (Spec K)` (see
`Langlands/GroupScheme/ConjugacyTransporter.md`). Its projection
`p : P ⟶ Spec L` is `pullback.fst z o`.

- The torus `T` is smooth (`IsTorus.smooth`). Over `Spec E`, the transporter
  `pullback (q ≫ z) o` is isomorphic to `Spec E × T` by `transporterIso`, so
  its projection to `Spec E` is smooth (`smooth_transporter_fst_left`, applied
  to `g`).
- `isPullback_pullback_comp` shows that this projection is the base change of
  `p` along `q.left : Spec E ⟶ Spec L`, as a pullback square of schemes after
  forgetting to `Over`.
- `q.left` is `Spec.map` of a field extension `L → E`, hence surjective, flat
  and quasi-compact (`fieldExtension_fpqc`). Mathlib's fpqc descent of
  smoothness, `MorphismProperty.of_isPullback_of_descendsAlong` for
  `Smooth` along `Surjective ⊓ Flat ⊓ QuasiCompact`, shows that `p.left` is
  smooth.

## Step 3: the transporter is smooth, affine and nonempty over `K`

- `L/K` is finite separable, hence étale (`Algebra.FormallyEtale.of_isSeparable`
  and finite presentation), hence smooth, so `Spec L ⟶ Spec K` is smooth. The
  structure morphism of `P` is `p.left` followed by it (`Over.w`), so it is
  smooth.
- `G.X.left` is affine, so `o.left` is an affine morphism between affine
  schemes. `p.left` is its base change, hence affine, and `Spec L` is affine,
  so `P.left` is affine.
- The pair `(q, g)` defines `s = pullback.lift q g : Spec E ⟶ P`, using
  `comp_conjugationOrbitMap` and `hg`. Then `P.left` is nonempty: it contains
  the image of the unique point of `Spec E`.

## Step 4: a point over a finite Galois extension

`exists_finiteGalois_point_of_smooth` (in
`Langlands/AlgebraicGeometry/SmoothFiniteGaloisPoint.md`) gives a finite
Galois extension `L'/K` in universe `u` and `σ : Spec L' ⟶ P.left` over
`Spec K`, packaged as a morphism `σ'` in `Over (Spec K)`. Put
`r = σ' ≫ pullback.fst z o` and `g' = σ' ≫ pullback.snd z o`. Then
`g' * x * g'⁻¹ = g' ≫ o = σ' ≫ pullback.fst ≫ z = r ≫ z`, by
`comp_conjugationOrbitMap` and `pullback.condition`. These are the last
conclusions of the statement.
