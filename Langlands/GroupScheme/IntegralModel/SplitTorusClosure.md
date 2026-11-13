# Extending a split torus with integral unit points to a closed split torus of a model

This module proves two results about integral models. First, a homomorphism
from a split generic torus into `G` extends to an integral homomorphism from the
split torus over the base into the model, provided it sends integral unit points
to integral points. Second, over a noetherian domain, such an integral
homomorphism is a closed immersion whenever its generic fibre is.

All rings live in one universe `u`. Write `R[ℤ^I]` for
`AddMonoidAlgebra R (I → ℤ)`.

## The split torus and its universal point

Let `R` and `K` be commutative rings, `K` an `R`-algebra, and `I : Type u`.

* `torus R I` is the published diagonalizable group scheme
  `Diagonalizable.groupScheme (CommRingCat.of R) (I → ℤ)`, that is
  `D_R(ℤ^I) = Spec R[ℤ^I]` over `Spec R`. `flat_torus` shows that its structure
  morphism is flat.
* `incl : R[ℤ^I] →ₐ[R] K[ℤ^I]` extends coefficients. `incl_injective` shows it
  is injective when `R → K` is.
* `tensorEquiv : R[ℤ^I] ⊗[R] K ≃+* K[ℤ^I]` swaps the tensor factors and then
  applies Mathlib's `AddMonoidAlgebra.scalarTensorEquiv`. It sends `p ⊗ k` to
  `k • incl p` (`tensorEquiv_tmul`). `tensorEquiv_comp_includeLeft` and
  `tensorEquiv_comp_includeRight` give its composites with the two tensor
  inclusions.
* `genericTorus R K I` is the base change of `torus R I` along
  `Spec.algebraMap R K`, as a group scheme over `Spec K`.
* `universalPointLeft : Spec K[ℤ^I] ⟶ pullback (torus R I).X.hom (Spec.algebraMap R K)`
  is `Spec` of `tensorEquiv` followed by the inverse of Mathlib's
  `pullbackSpecIso`. It is an isomorphism (instance). Its first projection is
  `Spec` of `incl` (`universalPointLeft_fst`). Its second projection is the
  structure map to `Spec K` (`universalPointLeft_snd`). `universalPoint` is the
  resulting `K[ℤ^I]`-valued point of `genericTorus R K I` (`universalPoint_left`).
* For finite `I`, a `K`-algebra `L` and `t : I → Lˣ`, `unitPoint R K I L t` is
  the `L`-point obtained from `universalPoint` by
  `evalUnits K t : K[ℤ^I] →ₐ[K] L`, the evaluation at the units `t` (from
  `Langlands.Algebra.HopfPointIntegralClosure`).

## Lifting points along injective coefficient maps

Let `X` be an object over `Spec R` with affine total space. Let `f : S →ₐ[R] T`
be injective and `p` a `T`-point of `X`. Suppose every affine coordinate of `p`,
under the published `affineSchemePointEquiv`, lies in the range of `f`. Then
`pointLift X f hf p hp` is the `S`-point whose coordinate homomorphism is the
coordinate homomorphism of `p`, restricted to the range of `f` and composed with
the inverse of `AlgEquiv.ofInjective f hf`. `pointLift_changeRing` proves that
changing coefficients along `f` recovers `p`. These are wrappers around the shared lifting
construction in `Langlands.GroupScheme.IntegralModel.IntegralPointDescent`.

## Descent of generic torus homomorphisms

Hypotheses:

* `R` is a domain with fraction field `K`, `G` is a group scheme over `Spec K`,
  and `M : IntegralModel R K G`. `I` is a finite type.
* `A` is a domain that is a valuation ring, with fraction field `L` and
  infinite residue field.
* There are algebra maps `R → A`, `A → L`, `K → L` and `R → L`, with scalar
  towers `R → A → L` and `R → K → L`.

The private instance `modelAffine` records that the model's total space is
affine.

Let `ψ : genericTorus R K I ⟶ G`. Two conditions appear:

* `hψ`: for every `t : I → Aˣ`, `ψ` maps the unit point given by the images of
  the `tᵢ` in `Lˣ` into `(M.baseChange A L).coefficientIntegralPoints K L`.
* `hint`: every `x : K` whose image in `L` lies in the image of `A` lies in the
  image of `R`.

Under these conditions:

* `genericCoordinate_universalPoint_mem_range`: for every affine coordinate `a`
  of the model, `M.genericCoordinate a` evaluated at the `K[ℤ^I]`-point
  `universalPoint ≫ ψ` lies in the range of `incl`.

  Proof. Call this Laurent polynomial `P`. Extend its coefficients to `L`. By
  the published criterion
  `mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates` and
  naturality of evaluation (`affinePointEvaluation_map`), `hψ` says that this
  polynomial takes values in `A` at every family of units of `A`.
  `coeff_mem_range_of_forall_evalUnits_mem` makes each coefficient integral
  over `A`. `hint` puts it in `R`, and `mem_range_mapAlgHom_of_coeff`
  concludes.
* `exists_genericTorusMap_eq`: there is a group-scheme homomorphism
  `j : (torus R I).toGrp ⟶ M.group` with `M.genericTorusMap (torus R I) j = ψ`.

  Proof. Move the point `universalPoint ≫ ψ` to a `K[ℤ^I]`-point of the model
  with `M.genericModelPointEquiv`. By the previous lemma and
  `genericModelPointEquiv_evaluation`, its coordinates lie in the range of
  `incl`. `pointLift` lifts it to an `R[ℤ^I]`-point `q` of the model, that is,
  a morphism `φ : torus R I ⟶ M.group.X` over `Spec R`.

  The base change of `φ` along `Spec K → Spec R` equals
  `ψ.hom.hom ≫ M.genericIso.inv.hom.hom`. Both sides agree after the two
  pullback projections. For the first projection, cancel the isomorphism
  `universalPointLeft` and use `universalPointLeft_fst`, `pointLift_changeRing`
  and `genericModelPointEquiv_left`. For the second, use the structure-map
  triangles.

  So the base change of `φ` is a monoid morphism. The source is flat
  (`flat_torus`), and the target is separated because the model is affine over
  `Spec R`. The published
  `Descent.FiniteCoefficient.isMonHom_of_generic` therefore makes `φ` itself a
  monoid morphism. Take `j := Grp.homMk φ`; its base change composed with
  `M.genericIso.hom` is `ψ`.

## Closedness from the generic fibre

Let `R` be a noetherian domain with fraction field `K`, `M : IntegralModel R K G`
and `I : Type u`, with no finiteness assumption on `I`.

* `isClosedSubgroup_of_genericTorusMap`: if
  `j : (torus R I).toGrp ⟶ M.group` has
  `IsClosedSubgroup (M.genericTorusMap (torus R I) j)`, then
  `IsClosedSubgroup j`. Here `IsClosedSubgroup` means that the underlying scheme
  morphism is a closed immersion.

  Proof. Precompose `j` with the published Hopf identification
  `Diagonalizable.hopfSpecIso` to get `i` with diagonal source. Cancelling the
  isomorphism `M.genericIso` shows that the base change of `j` to `K` is a
  closed immersion. By `TorusClosedImmersionLocus.closed_baseChange_precomp_iso_iff`
  the same holds for the base change of `i`.

  `TorusClosedImmersionLocus.diagonal_closed_iff` turns this into surjectivity
  of the scalar extension to `K` of the diagonal coordinate map
  `δ := diagonalCoordinateMap i`, a bialgebra map into `R[ℤ^I]`.
  `DiagonalCoalgebraLocus.exists_nonzero_coefficient` gives, in each degree, a
  coordinate whose coefficient is nonzero, already over `R`. Then
  `surjective_of_coeff_ne_zero` (noetherian domain) makes `δ` surjective, so
  `Spec δ` is a closed immersion (`IsClosedImmersion.spec_of_surjective`). By
  `diagonalCoordinateMap_map`, `i` is `Spec δ` followed by the isomorphism
  `AffineCoordinates.hopfSpecIso`. Hence `i`, and so `j = e⁻¹ ≫ i`, is a closed
  immersion.

## Provenance

The module serves Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition B.2.4 (printed p. 656), for split tori. KP show that the
schematic closure in a smooth model of a torus `S`, split over `K`, is an
`𝔬`-torus once the maximal bounded subgroup of `S(K)` lies in the integral
points. For the split torus `D(ℤ^I)` that subgroup is `(A^×)^I`, which is the
hypothesis `hψ`.

The Lean route differs from the book:

* It assumes no smoothness of the model and uses no smoothening.
* It does not form a schematic closure. It constructs the integral homomorphism
  directly by coefficient descent, assuming an infinite residue field of `A`.
* It proves the closed-immersion property with the coefficient-ideal argument
  of `Langlands.Algebra.HopfPointIntegralClosure`. This replaces the
  weight-module argument in the proof of KP Lemma B.2.3.

Every other ingredient is a published Library or Mathlib result.

Drafted by Worker 5707 for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
