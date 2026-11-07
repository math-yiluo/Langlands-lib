# Smooth Picard atlases from charts at finite-type field points

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasAssembly`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

The main theorem is `PicardGroupoid.finiteTypePicardStackAtlas_of_pointSmoothCharts`.
It proves the published `FiniteTypePicardStackAtlasStatement.{u}` from the
published `FiniteTypePointSmoothChartStatement.{u}`, which is a hypothesis
here and is not proved. The theorem formalizes the assembly step of Stacks
Lemma 98.17.1 (Tag 07Y4): take one smooth chart for every object over every
finite type field, form their disjoint union, and use the Jacobson property
to show that the union is surjective. The other declarations support this
proof. All schemes, rings and index types are in one universe `u`. All
declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid`.

## Smooth point fibres of a coproduct chart

Fix `f : X ⟶ S`.

- `pointFiberPresheafIsoOfChartIso f eL M`: an isomorphism `eL : L ≅ L'` of
  actual line bundles on `U ×ₛ X` gives an isomorphism of the actual point
  fibre presheaves `pointFiberPresheaf f L M ≅ pointFiberPresheaf f L' M`.
  It is the published `PseudofunctorPointFiberObjectIso.presheafIso`,
  whiskered by the iterated-slice functor and the universe lift.
- `representingIso e e'`: two schemes `P`, `P'` over `T` whose lifted
  Yoneda presheaves are isomorphic to the same presheaf are isomorphic over
  `T` (full faithfulness of the lifted Yoneda embedding).
- `coproductChart_hasSmoothPointFibers f V L hL hrep`: for a family
  `V : ι → Over S` (`ι : Type u`) and actual line bundles `L i` on
  `V i ×ₛ X` with `HasSmoothPointFibers f (L i)` for every `i`, the glued
  bundle `CoproductChartBundle.bundle f V L` on `(∐ᵢ V i) ×ₛ X` has smooth
  point fibres. The hypothesis `hrep` says that its point fibres over every
  test are represented by some scheme. Proof: if `P` represents a point
  fibre of the glued bundle, the published `restrictIso` identifies the part
  of `P` over the component `V i` with a scheme representing the point fibre
  of `L i`, using `bundleIso`. That part is therefore isomorphic over the
  test to a smooth representing scheme for `L i`. These parts form the open
  cover of `P` pulled back from the coproduct cover, and smoothness is local
  on the source.
- `residueBundleCompIso f L j a`: for `a : W ⟶ V` and `j : V ⟶ U` over `S`,
  the pullback of `L` along `(relativeSpace f).map (a ≫ j)` is isomorphic to
  the pullback along `(relativeSpace f).map a` of the restriction
  `restrictBundle f L j`. It uses functoriality of `relativeSpace` and the
  published `LineBundle.pullbackComp`.

## Points of representing schemes

`mem_range_of_chartPoint`: let `R` be a ring, `f : X ⟶ Spec R`, `L` an actual
line bundle on `U ×_R X`, `B` an `R`-algebra, `M` an actual line bundle on
`Spec B ×_R X`, and `P` a scheme over `Spec B` with
`e : schemeYoneda P ≅ pointFiberPresheaf f L M`. Let `K` be a field over
`R`, `φ : B →ₐ[R] K`, `a : Spec K ⟶ U` over `Spec R`, and
`c : residueBundle f L a ≅` the pullback of `M` along `Spec φ`. Then for every
point `x` of `Spec K`, the image of `x` in `Spec B` under `Spec φ` lies in the
image of `P.hom`. Proof: the pair `(a, c)` is a point of the point fibre over
the scheme `Spec K` over `Spec B` (the published `PseudofunctorPointFiber.pullIso`
builds the required identification). Through `e` it gives a morphism
`Spec K ⟶ P` over `Spec B`, so the image point lies in the image of `P`.

`surjective_of_isOpenMap_of_closedPoints`: a morphism of schemes `g : W ⟶ Y`
with `Y` a Jacobson space, an open underlying map, and every closed point of
`Y` in its image, is surjective. The complement of the image is closed. If it
were nonempty it would be locally closed, so it would contain a closed point
of `Y` (Mathlib's `nonempty_inter_closedPoints`), which is impossible.

## Presented field points and the chart index

Fix a commutative ring `R` and a scheme `X` over `Spec R`.

- `PointField n m` (abbreviation): the quotient
  `MvPolynomial (Fin n) R ⧸ m` by a maximal ideal `m`. It has the instances
  `Field` (quotient by a maximal ideal) and `Algebra.FiniteType R`
  (a quotient of a polynomial ring in finitely many variables).
- `pointFiber X n m` (abbreviation): the scheme
  `(relativeSpace X.hom).obj (ArtinianTest.residueBase R (PointField n m))`,
  that is, `Spec (PointField n m) ×_R X`. If `X.hom` is quasi-compact, it is
  a compact space (instance).
- `ChartIndex X`, for `X.hom` quasi-compact: the type of triples
  `⟨n, m, c⟩` with `n : ℕ`, `m` a maximal ideal of
  `MvPolynomial (Fin n) R`, and `c` a class in the published actual unit
  sheaf cohomology `Sheaf.H.{u} (unitSheaf (pointFiber X n m)) 1`. This type
  lies in `Type u`. Every isomorphism class of line bundles on every fibre
  `pointFiber X n m` occurs through its class (published
  `LineBundle.unitCohomologyClass_surjective` and
  `unitCohomologyClass_eq_iff_iso`, which need compactness).
- `ChartIndex.bundle i`: a line bundle on `pointFiber X i.1 i.2.1` whose
  class is `i.2.2`, chosen by `Classical.choose`. The lemma
  `ChartIndex.unitCohomologyClass_bundle` records that its class is `i.2.2`.
- `exists_pointField_base_eq`: for an `R`-algebra `B` of finite type and a
  prime `y` of `B` whose ideal is maximal, there are `n`, a maximal ideal `m`
  of `MvPolynomial (Fin n) R` and `φ : B →ₐ[R] PointField n m` such that
  `Spec φ` maps every point of `Spec (PointField n m)` to `y`. Proof: choose a
  surjection `π : MvPolynomial (Fin n) R → B`, let `m` be the preimage of `y`,
  and let `φ` be induced by the quotient map. Its kernel is `y`, and the
  preimage under `φ` of the prime of the field is a proper ideal containing
  `y`, hence `y`.

## The main theorem

`finiteTypePicardStackAtlas_of_pointSmoothCharts (h : FiniteTypePointSmoothChartStatement.{u}) :
FiniteTypePicardStackAtlasStatement.{u}`.

Let `R` be of finite type over `ℤ` and `X` proper and flat over `Spec R`.
Then `R` is Noetherian, so `X.hom` is locally of finite presentation. `R` is
a Jacobson ring, because `ℤ` is (published
`NoetherianApproximation.isJacobsonRing_int`) and Mathlib's
`isJacobsonRing_of_finiteType`.

1. For every `i : ChartIndex X`, apply `h` to the field `PointField i.1 i.2.1`
   and the line bundle `i.bundle`. This gives a chart `V i` locally of finite
   type over `Spec R`, an actual line bundle `Lc i` with smooth point fibres,
   a point `p i : Spec (PointField i.1 i.2.1) ⟶ V i` over `Spec R`, and an
   isomorphism of `residueBundle X.hom (Lc i) (p i)` with `i.bundle`.
2. The atlas is the coproduct `sigmaOver V`, locally of finite type over
   `Spec R` (published instance), with the glued bundle
   `L = CoproductChartBundle.bundle X.hom V Lc`.
3. Its point fibres are represented by schemes (published
   `hasAffinePointFiberSchemes`), so `coproductChart_hasSmoothPointFibers`
   shows that they are smooth.
4. By the published `isSmoothSurjectivePresentation_of_finiteTypeAffine`, it
   suffices to show smoothness and surjectivity for every test `Spec B` with
   `B` of finite type over `R` and every line bundle `M` on `Spec B ×_R X`.
   Take a representing scheme `P`. It is smooth over `Spec B` by step 3, so
   its structure map is open (flat and locally of finite presentation). `B`
   is a Jacobson ring, so `Spec B` is a Jacobson space. By
   `surjective_of_isOpenMap_of_closedPoints` it remains to show that every
   closed point `y` of `Spec B` lies in the image of `P`.
5. A closed point `y` is a maximal ideal. Take `n`, `m` and `φ` from
   `exists_pointField_base_eq`, and let `N` be the pullback of `M` to
   `pointFiber X n m` along `Spec φ`. Put `i = ⟨n, m, [N]⟩`. Then
   `i.bundle ≅ N`. The pullback of `L` along `p i` followed by the component
   inclusion is isomorphic to `N`: use `residueBundleCompIso`, then
   `bundleIso`, then the isomorphism from step 1, then `i.bundle ≅ N`.
   `mem_range_of_chartPoint` applied at the point of
   `Spec (PointField n m)` shows that `y` lies in the image of `P`.

## Source

The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, `artin.pdf` (Chapter 98
"Artin's Axioms"), Lemma 98.17.1 (Tag 07Y4), printed as Lemma 17.1, p. 27.
Its proof chooses, for every finite type field `k` over `S` and every
isomorphism class of objects `x₀` over `Spec k`, a smooth chart `U_{k,x₀}`
with a point of residue field `k` mapping to `x₀` (Lemma 98.13.8, Tag 07XY),
and takes the disjoint union `U` of these charts (footnote 7 bounds the index
set). Surjectivity is checked on affine tests `V` locally of finite
presentation over `S`: the fibre product `W → V` is smooth, so its image is
open, and it contains every finite type point `v₀` of `V`, because the chart
point of `(κ(v₀), y|_{v₀})` gives a morphism `Spec κ(v₀) → W` over `v₀`.

The Lean proof follows this argument with these formal changes:

- it assumes the chart statement rather than proving it;
- it indexes the charts by presented fields `R[x₁, …, xₙ]/m` and
  unit-cohomology classes of line bundles on the fibre, so the index type
  lies in `Type u`;
- it checks surjectivity on finite-type affine tests `Spec B`, reached
  through the published test reduction, and at closed points, using the
  Jacobson property (in place of finite type points, Morphisms Lemma 16.7);
- it works with the published point-fibre presheaves and their
  representing schemes rather than fibre products over the stack. A chart
  point gives only a `K`-valued point, which is all the image argument uses.
