# Split coordinates of the universal point of the generic split torus

This module connects the split torus `torus R I = D_R(ℤ^I)` of
`Langlands.GroupScheme.IntegralModel.SplitTorusClosure` with the published
split torus `splitTorus S I = 𝔾_m^I`. It then restates the closure results
of that module for a closed subgroup `ψ : T → G` whose source is isomorphic to
`𝔾_m^I`. The hypothesis is phrased in the split coordinates of `𝔾_m^I`.

All rings live in one universe `u`. Write `R[ℤ^I]` for
`AddMonoidAlgebra R (I → ℤ)`. The declarations live in the namespace
`Langlands.GroupScheme.IntegralModel.SplitTorusClosure`.

## Split coordinates

Let `S` be a scheme and `I` a finite type.

* `pointsEquiv_eq_of_left_eq`: take morphisms `f₁ f₂ : X ⟶ S`, a point
  `x : Over.mk f₁ ⟶ (splitTorus S I).X` and a point
  `y : Over.mk f₂ ⟶ (splitTorus S I).X`. If `x` and `y` have the same
  underlying scheme morphism, their split coordinates
  `splitTorus.pointsEquiv I _ x` and `splitTorus.pointsEquiv I _ y` agree.
  The proof uses `splitTorus.pointsEquiv_apply` and `Gm.pointsEquiv_val`: each
  coordinate depends only on the underlying morphism.
* `affinePointsEquiv_val`: for `f : Spec A ⟶ S`, the affine split coordinates
  `splitTorus.affinePointsEquiv I f x i` are the images of the split
  coordinates `splitTorus.pointsEquiv I (Over.mk f) x i` under
  `Scheme.ΓSpecIso A`. This holds by definition.

## The split isomorphism and the universal point

Let `R` be a commutative ring and `I` a finite type with decidable equality.

* `splitIsoR R I : (torus R I).toGrp ≅ splitTorus (Spec R) I` is the published
  `Diagonalizable.splitIso` for the identity of `I → ℤ`.
* `splitIsoPoint R I` is the hom of `splitIsoR R I`, viewed as an
  `R[ℤ^I]`-valued affine point of `𝔾_m^I` (`Lie.AffinePoints`).
* `algebraPointsEquiv_affineMap_splitIsoPoint`: let `C` be an `R`-algebra and
  `φ : R[ℤ^I] →ₐ[R] C`. Change the coefficients of `splitIsoPoint R I` along
  `φ` (`Lie.affineMap`). The `i`-th coordinate of the result under
  `splitTorus.algebraPointsEquiv I C` is
  `φ (AddMonoidAlgebra.single (Pi.single i 1) 1)`, the image of the `i`-th
  coordinate monomial.

  Proof. `Diagonalizable.splitIso` is built from point models, so
  `isoOfPointModels_hom` computes its effect on points through
  `Diagonalizable.splitPointsEquiv`. The resulting coordinate is the value of
  the corepresented point at the `i`-th basis character.
  `Corepresented.pointsEquiv_eq_affinePointsEquiv` and
  `Corepresented.affinePointsEquiv_map` identify this value with `φ` applied
  to the coordinate monomial. `Corepresented.affineSectionsIso_inv_ringHom`
  removes the identification of global sections.
* `splitIsoPoint_eq_universalPoint`: `splitIsoPoint R I` equals the published
  universal point `splitTorus.universalPoint I` of `𝔾_m^I` over `Spec R`. Both
  have the coordinate monomials as split coordinates: take `φ` to be the
  identity above and use `splitTorus.algebraPointsEquiv_universalPoint`.

## The generic fibre

Let `R` and `K` be commutative rings, `K` an `R`-algebra, and `I` a finite type
with decidable equality.

* `genericSplitIso R K I : genericTorus R K I ≅ splitTorus (Spec K) I` is the
  base change of `splitIsoR R I` along `Spec.algebraMap R K`, followed by the
  published `splitTorus.baseChangeIso`.
* `universalPoint_genericSplitIso`: the composite of `universalPoint R K I`
  with `genericSplitIso R K I` is the universal point
  `splitTorus.universalPoint I` of `𝔾_m^I` over `Spec K`.

  Proof. Compare split coordinates. `splitTorus.pointsEquiv_baseChangeIso_hom`
  and `GroupScheme.baseChangePointsEquiv_comp` reduce the left side to the
  coordinates of a point of `𝔾_m^I` over `Spec R`. By
  `universalPointLeft_fst`, its underlying morphism is that of `Spec incl`
  followed by `splitIsoR R I`. `pointsEquiv_eq_of_left_eq` and
  `algebraPointsEquiv_affineMap_splitIsoPoint` for `φ = incl` then give the
  coordinate monomials of `K[ℤ^I]`.
* `unitPoint_genericSplitIso`: for a `K`-algebra `L` and `t : I → Lˣ`, the
  composite of `unitPoint R K I L t` with `genericSplitIso R K I` is the
  `L`-point `(splitTorus.algebraPointsEquiv I L).symm t` of `𝔾_m^I`, the point
  with coordinates `t`. This follows from the previous lemma and the published
  `splitTorus.universalPoint_evaluateUnits`.

## Closed split tori from integral unit points

Hypotheses:

* `R` is a noetherian domain with fraction field `K`, `G` is a group scheme
  over `Spec K`, and `M : IntegralModel R K G`. `I` is a finite type with
  decidable equality.
* `A` is a domain that is a valuation ring, with fraction field `L` and
  infinite residue field.
* There are algebra maps `R → A`, `A → L`, `K → L` and `R → L`, with scalar
  towers `R → A → L` and `R → K → L`.

`exists_isClosedSubgroup_genericTorusMap_eq`: let `T` be a group scheme over
`Spec K`, `e : T ≅ splitTorus (Spec K) I`, and `ψ : T ⟶ G` with
`IsClosedSubgroup ψ`. Assume:

* `hunits`: for every `t : I → Aˣ`, write `t'` for the family of images of the
  `tᵢ` in `Lˣ`. The `L`-point `(splitTorus.algebraPointsEquiv I L).symm t'`,
  followed by `e.inv` and `ψ`, lies in
  `(M.baseChange A L).coefficientIntegralPoints K L`;
* `hint`: every `x : K` whose image in `L` lies in the image of `A` lies in the
  image of `R`.

Then there is `j : (torus R I).toGrp ⟶ M.group` with `IsClosedSubgroup j` and
`M.genericTorusMap (torus R I) j = (genericSplitIso R K I).hom ≫ e.inv ≫ ψ`.

Proof. By `unitPoint_genericSplitIso`, `hunits` is the hypothesis of
`exists_genericTorusMap_eq` for the homomorphism
`(genericSplitIso R K I).hom ≫ e.inv ≫ ψ`. That lemma gives `j`. This generic
homomorphism is `ψ` preceded by isomorphisms, so it is a closed subgroup
(`IsClosedSubgroup.iso_comp`). `isClosedSubgroup_of_genericTorusMap` then
makes `j` a closed subgroup.

## Provenance

This module serves Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Lemma B.2.3 and Proposition B.2.4 (printed pp. 655–656), for split
tori. In the book, the maximal bounded subgroup of the split torus over `K` is
the group of points whose coordinates in `𝔾_m^I` are units of the valuation
ring. The hypothesis `hunits` states that these points are integral.

The coordinate lemmas are internal bookkeeping that matches the split torus of
`SplitTorusClosure` with the published `splitTorus`. They have no counterpart
in the literature. Every ingredient other than the declarations of
`SplitTorusClosure` and `Langlands.Algebra.HopfPointIntegralClosure` is a
published Library or Mathlib result.

Drafted by Worker 5707 for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
