# Lie weights of a split-torus action through a corepresented model

This module connects the weights of a split-torus action on the Lie algebra of an affine group
`G` over a field `k` with the coordinate-algebra weights of the torus action on a corepresented
model of `G`. It supplies the three facts (L0)–(L2) used to identify weight subgroups in the
proof of `Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement`.

## Setting

Throughout, `k` is a field and `G` a group scheme over `Spec k`. The model is a functor
`F : CommAlgCat k ⥤ GrpCat` corepresented by `e` through a `k`-algebra `B`, with an isomorphism
`ψ : groupScheme F e ≅ G`. The torus is a commutative group scheme `S` over `Spec k` with a
splitting `φ : S.toGrp ≅ splitTorus (Spec k) I` for a finite type `I`. Finally,
`b : AutomorphicAction S.toGrp G` is an action of `S` on `G` by group automorphisms.

Through the bridge module `Rational.TorusActionBridge`, `b` gives the torus action
`TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)` of unit families `t : I → Aˣ` on the
groups `F.obj A`. All statements below use this action, written out in full.

## Coordinates of points

- `lieCoords e ψ A : Lie.AffinePoints G A ≃* F.obj A` sends a point `g` of `G` over a
  `k`-algebra `A` to the coordinates of `g ≫ ψ.inv` in the model. It is the composite of the
  existing `isoPointsEquiv ψ.symm` and `affinePointsEquiv F e A`. `lieCoords_apply` states this
  formula.
- `lieCoords_affineMap` says that coordinates commute with change of algebra along a
  `k`-algebra map `f : A →ₐ[k] A'`. `lieCoords_reduction` says the coordinates of a point
  of the dual-number identity kernel `lieKernel G k` reduce to `1`.
- `lieCoords_act` says the action is computed in coordinates. For `s` a point of `S` and `g` a
  point of `G` over `A`, the coordinates of `b.act s g` are obtained by applying the torus
  action, at the unit coordinates of `s ≫ φ.hom`, to the coordinates of `g`.
- `algebraPointsEquiv_constant`: the unit coordinates of the constant dual-number point
  `Lie.constant S.toGrp s` are the images of those of `s` under `A → A[ε]`.
- `characterEquiv_characterExponents` and `characterValue_eq_exponentValue`: for a character
  `χ` of `S`, the value `Lie.characterValue χ s` is the monomial
  `splitTorus.exponentValue I t (characterExponents φ χ)` in the unit coordinates `t` of
  `s ≫ φ.hom`. Here `characterExponents φ` is the exponent-vector equivalence of the bridge
  module, and `PointedCoordinateWeights.characterEquiv φ` from the Library is its inverse.

## (L0) Eigenvectors

`mem_actionEigenvectors_iff e ψ φ b χ X`: a tangent vector `X` in `lieKernel G k` lies in
`actionEigenvectors b χ` exactly when its coordinates are a weight tangent vector
(`IsWeightTangent`) of weight `characterExponents φ χ` for the torus action. Both conditions
compare the action of a torus point on the tangent vector with scaling by the value of the
character. The proof turns each side into the other using `lieCoords_act`, the naturality of
the coordinates and the monomial formula for character values. In the forward direction, a unit
family `t` is realized as the unit coordinates of the point
`(splitTorus.algebraPointsEquiv I A).symm t ≫ φ.inv` of `S`.

## (L1) Tangent weights of transported weight subgroups

- `mem_cutSubgroupFunctor_affine`: on affine tests, a point lies in the subgroup functor cut out
  by an ideal `J` (`cutSubgroupFunctor hJ`) exactly when its coordinates lie in the subgroup
  family `H` that `J` cuts out.
- `sndSupportSubmodule e ψ σ χ` is the `k`-submodule of `Additive (lieKernel G k)` made of the
  tangent vectors `X` whose coordinates satisfy the following: for every `f` in `B` and every
  `m ≠ χ`, the infinitesimal part of the coordinate of `X` at the weight-`m` component
  `comp e σ m f` vanishes.
- `actionWeightSpace_le_sndSupportSubmodule`: the weight space `actionWeightSpace b χ` (the span
  of the eigenvectors) is contained in `sndSupportSubmodule` for the exponent vector of `χ`. This
  follows from (L0) and the Library lemma `snd_comp_eq_zero_of_isWeightTangent`.
- `actionWeightSupport_comap_weightSubgroup_subset e ψ φ b P`: for an additive subsemigroup `P`
  of `I → ℤ`, let `U` be the subgroup functor of `G` obtained by cutting out the model's weight
  subgroup for `P` (`isCutOutBy_weightIdeal`) and pulling it back along `ψ.inv`. Then every
  character in `actionWeightSupport b U` has exponent vector in `P`. Proof: a nonzero vector `X`
  of weight `χ` in the tangent space of `U` has coordinates in the weight subgroup for `P`,
  supported on the single exponent vector of `χ`. If that vector is not in `P`, the Library
  lemma `eq_one_of_mem_weightSubgroup_of_snd_comp` forces the coordinates, hence `X`, to be
  trivial.

## (L2) Tangent rigidity

- `lieCoords_mem_affineSubgroups_iff`: for a subgroup functor `F'` of `G`, the coordinates of
  a dual-number point `g` of `G` lie in `affineSubgroups (F'.comap ψ.hom)` exactly when `g`
  lies in `F'`.
- `tangentRigid_of_actionWeightSupport_subset e ψ φ b P hF' hJ hH`. Assume:
  - `F'` is a subgroup functor of `G` whose tangent weights all have exponent vectors in `P`;
  - `J` is an ideal of `B` cutting out the pulled-back family `affineSubgroups (F'.comap ψ.hom)`;
  - `hH` says this family is stable under the torus action.

  Let `χ` be an exponent vector outside `P`. Then every tangent vector `X` of the cut-out group
  (`cutFunctor hJ` at `k[ε]`, reducing to `1`) is trivial if the following holds: the
  infinitesimal parts of its coordinates vanish at all weight components `m ≠ χ` of the
  restricted torus action `restrict hJ hH`. This is the rigidity hypothesis of the Library
  lemma `Corepresented.le_weightSubgroup`.

  Proof: these vanishing conditions make the coordinates a weight tangent vector of weight `χ`
  (`isWeightTangent_of_snd_comp`). Transported back to `G` through `lieCoords`, it is by (L0)
  an eigenvector of weight `(characterExponents φ).symm χ` that lies in `F'`. If it were
  nonzero, that character would belong to `actionWeightSupport b F'`, so `χ` would lie in `P`.
  The statement does not need `b` to stabilize `F'`; only the stability `hH` of the cut-out
  family is used.

## Provenance

This is an internal supporting module for the explicit coordinate-algebra proof of
`CyclicWeightFiltrationStatement`. The target statements (L0)–(L2) were agreed with the task's
first executor (Worker 1224), whose assembly applies them. The mathematical setting is
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 and its proof (printed
pp. 111–112), where the Lie algebra of the subgroup attached to a set of weights is identified
through the grading of the coordinate algebra. The results here translate between the tangent
weights of the scheme-theoretic action and the coordinate grading. They do not formalize a
particular statement of that source.
