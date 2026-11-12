# Smooth atlases of the actual coherent-family stack from charts at finite-type points

Module: `Langlands.AlgebraicGeometry.CoherentSheaves.FieldCoherentStackAtlasAssembly`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

The main theorem `fieldCoherentStackAtlas_of_inputs` derives the published
`FieldCoherentStackAtlasStatement.{u}` from three published propositions. They
remain hypotheses here and are not proved:

- `hI : ProperIsomRepresentabilityStatement.{u}` (affine finitely presented scheme
  representation of actual coherent-family Isom presheaves),
- `hC : FieldCoherentPointSmoothChartStatement.{u}` (smooth charts through
  finite-type field points),
- `hS : Modules.FinitePresentationEssentiallySmallStatement.{u}` (essential
  smallness of locally finitely presented module sheaves).

The argument formalizes the assembly step of Stacks Project Lemma 98.17.1
(Tag 07Y4) over `S = Spec k`. It follows the published line-bundle assembly
`Picard.PicardGroupoid.finiteTypePicardStackAtlas_of_pointSmoothCharts` and
reuses its field points `PointField`, `exists_pointField_base_eq` and
`surjective_of_isOpenMap_of_closedPoints`. All schemes, rings and index types
are in one universe `u`.

## Notation

`liftedStack f` abbreviates
`PseudofunctorHomLift.homLift.{u + 1} (FamilyGroupoid.pseudofunctor f)`, the
published coherent-family pseudofunctor with lifted morphism universe. Its
objects over `T` are the explicit lifts `ULiftHom.objUp N` of actual families
`N : FamilyGroupoid f T`.

## Supporting lemmas

- `exists_family_representatives f hS T`: there are `ι : Type u` and families
  `N : ι → FamilyGroupoid f T` such that every actual family over `T` is
  isomorphic in the family groupoid to some `N i`. Apply `hS` to the relative
  space of `T` to obtain a `u`-small property `Q` whose isomorphism closure
  contains all locally finitely presented module sheaves. Index by the elements
  of `Shrink (Subtype Q)` whose module is flat over the test, and move family
  conditions along module isomorphisms.
- `exists_pointFiber_representation f hI ξ η`, for proper and locally finitely
  presented `f`: every actual point fibre of `liftedStack f` is represented on
  the full slice by some scheme. This is the published
  `FamilyGroupoid.exists_pointFiberIsomScheme_of_properIsom`.
- `smooth_of_coproductFamily f V M hsm η e`: let the component families
  `M i` have smooth point fibres. Then every scheme representing a point fibre
  of the glued family `CoproductChartFamily.family f V M` is smooth over its
  test. This is `Stacks.smooth_of_coproductChart` with the restriction
  isomorphisms `CoproductChartFamily.familyIso`.
- `mem_range_of_familyChartPoint`: `Stacks.mem_range_of_chartPoint` for actual
  families over affine tests `Picard.affineBase k B` and a field point
  `ψ : B →ₐ[k] K`.
- `surjective_of_chartPoints f ξ hpt M₀ e hQ`: let `B` be a `k`-algebra of
  finite type and `Q` a smooth scheme representing the point fibre of `ξ`
  against a family `M₀` over `Spec B`. Assume `hpt`: for every presented field
  point `PointField n m = k[x₁, …, xₙ]/𝔪` and every family `N` over it, some map
  `a` from that point to the chart pulls `ξ` back to `N`. Then `Q → Spec B` is
  surjective. Smoothness makes its image open. `Spec B` is a Jacobson space,
  since `k` is a field and `B` is of finite type. It therefore suffices to hit
  closed points. A closed point `y` is the image of some
  `ψ : B →ₐ[k] PointField n m` (published `exists_pointField_base_eq`). Applying
  `hpt` to the pullback of `M₀` along `ψ` gives a chart point, and
  `mem_range_of_familyChartPoint` puts `y` in the image.
- `surjective_of_finiteTypeTests f ξ hft η e`, for `f` quasi-compact,
  separated and locally of finite type: assume `hft`, that every point fibre
  over every finite-type affine test has a surjective representing scheme.
  Then every representing scheme `P` over an arbitrary test `T` is surjective.
  For `t ∈ T`, let `κ` be the residue field. Give it the `k`-algebra structure
  obtained from `Spec κ → T → Spec k` by full faithfulness of `Spec`. Let
  `g : Spec κ ⟶ T` be the residue-field point as a test map.
  `FamilyDescent.exists_finiteType_model`, applied to the pullback of `η` along
  `g`, gives a finite-type `k`-algebra `B`, a `k`-algebra map `φ : B → κ`, a
  family `M₀` over `Spec B` and an actual isomorphism of pullbacks. Let `Q` be a
  surjective representing scheme for `M₀`. Its pullback along `Spec φ` and the
  pullback of `P` along `g` both represent the point fibre of the pulled-back
  test family (`Stacks.pullbackRepresentationIso`,
  `Stacks.pointFiberPresheafIsoOfTestIso`). Hence they are isomorphic over
  `Spec κ` (`Picard.PicardGroupoid.representingIso`). The former is surjective by base change,
  so the latter has a point over the closed point of `Spec κ`. Its image in `P`
  lies over `t`.

## The main theorem

Let `k` be a field and `X` proper over `Spec k`. Then `X.hom` is locally of
finite presentation (published `locallyOfFinitePresentation_over_field`),
quasi-compact and separated.

1. For each presented field point `j = (n, 𝔪)`, choose representatives
   `Nrep j r` of all families over `PointField n 𝔪`
   (`exists_family_representatives`).
2. For each index `i = (j, r)`, `hC` gives a chart `V i` locally of finite type
   over `k`, a family `M i` with smooth point fibres, a point
   `p i : Spec (PointField n 𝔪) ⟶ V i` and an actual isomorphism from the
   pullback of `M i` along `p i` to `Nrep j r`. The index type lies in `Type u`.
3. The atlas is the published coproduct chart `sigmaOver V`, locally of finite
   type over `k` (published instance), with the object
   `ULiftHom.objUp (CoproductChartFamily.family X.hom V M)`.
4. For a test `T` and object `η`, `exists_pointFiber_representation` gives a
   representing scheme `P`. It is smooth by `smooth_of_coproductFamily`.
5. Surjectivity of `P` uses `surjective_of_finiteTypeTests`. Its hypothesis
   `hft` is supplied by representing schemes over finite-type affine tests,
   smooth by step 4 and surjective by `surjective_of_chartPoints`. The
   hypothesis `hpt` is: for `N` over `PointField n 𝔪`, choose `r` with
   `Nrep (n, 𝔪) r ≅ N` and use the chart point `p i ≫ sigmaOverι V i`. The required
   isomorphism composes the published pullback composition comparison, the
   pulled-back `familyIso`, the chart isomorphism of step 2 and
   `Nrep (n, 𝔪) r ≅ N`.

The theorem keeps the exact published target: every field and universe, every
proper scheme, every test scheme in the full slice, the actual families, their
ordinary pullbacks and actual isomorphisms, and the explicit morphism-universe
lift.

## Source

Registered original `stacks-artin-axioms-approximation-2026-11-06`, file
`artin.pdf`, Lemma 98.17.1 (Tag 07Y4), printed page 27. Its proof chooses a
smooth chart for every finite type field and every isomorphism class of objects
over it (Lemma 98.13.8), forms their disjoint union and checks surjectivity at
finite type points of affine tests, using the Jacobson property. The set
theoretic axiom [-1] bounds the index set (footnote 7). The Lean proof follows
this argument with these formal changes:

- the chart lemma and the bound on isomorphism classes are hypotheses `hC` and
  `hS`, and representability of point fibres by schemes is the hypothesis `hI`;
- charts are indexed by presented fields `k[x₁, …, xₙ]/𝔪` and a `u`-small set of
  representatives of families over them;
- surjectivity over an arbitrary test is reduced to finite-type affine tests by
  descending the family at each residue field (`FiniteTypeFamilyDescent`), in
  place of the source's reduction to affine tests locally of finite
  presentation.
