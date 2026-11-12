# Parabolic-left coverings over strictly Henselian valuation rings

This module proves the Iwasawa-type covering `G(K) = P(K) · G(R)` when `R` is
a strictly Henselian valuation ring with fraction field `K`. Strictly
Henselian means that `R` is a Henselian local ring whose residue field is
separably closed. The main application is the ring of integers of the maximal
unramified extension of a nonarchimedean local field. That ring is neither
complete nor of finite residue field, so the published complete-ring version
`Langlands.GroupScheme.IntegralParabolicCovering` does not apply to it.

All objects share one arbitrary universe `u`.

## Declarations

### The covering predicate

* `HasLeftIntegralCovering M H`, for `M : IntegralModel R K G` and a subgroup
  `H` of `rationalPoints G`, is the proposition
  `(H : Set _) * (M.integralPoints : Set _) = Set.univ`. In words, every
  `K`-point of `G` is a point of `H` times an integral point of `M`. Only the
  `IntegralModel` hypotheses on `R` and `K` are needed to state it (`R` a
  domain with fraction field `K`).
* `hasLeftIntegralCovering_iff` rewrites the predicate pointwise: for every
  `g` there are `h ∈ H` and `k ∈ M.integralPoints` with `h * k = g`.

### Sections of smooth schemes and torsors

In the next two results `R` is any Henselian local ring with separably closed
residue field.

* `nonempty_ringPoint_of_smooth`: if `X` over `Spec R` is smooth and
  surjective, then `X` has an `R`-point (`RingPoint R X R`).
* `nonempty_ringPoint_of_torsor`: let `H` be a smooth group scheme over
  `Spec R` acting on `X` (`ModObj H.X X`). Suppose that `X → Spec R` is flat,
  surjective and quasi-compact and that the shear `ModObj.leftSMul H.X X` is
  an isomorphism. Then `X` has an `R`-point. No connectedness of the special
  fibre of `H` is assumed.

### Lifting and covering for an explicit quotient

The data are as in the complete-ring module. There are group schemes `G` and
`P` over `Spec R`, a monomorphism `i : P ⟶ G` with `P` smooth, and a morphism
`q : G.X ⟶ Q`. The morphism `q.left` is flat, surjective and quasi-compact.
Finally `hfib` is the exact coset criterion: for every `T` over `Spec R` and
points `g h : T ⟶ G.X`, `g ≫ q = h ≫ q` holds exactly when `g⁻¹ * h` lies in
the image of `i` on `T`-points.

* `integral_lifts_of_flagQuotient`: every `R`-point of `Q` is `g ≫ q` for
  some `R`-point `g` of `G`. Here `R` is Henselian local with separably
  closed residue field.
* `exists_mul_integral`: in addition let `R` be a valuation domain with
  fraction field `K` and let `Q` be proper over `R`. Then every morphism
  `g : ringTest R K ⟶ G.X` equals `(h ≫ i) * (ringTestMap (R → K) ≫ k)`. Here
  `h` is a `K`-point of `P` and `k` is an `R`-point of `G`.
* `exists_mul_rationalPoint`: the same factorization for points
  `Over.mk (Spec.algebraMap R K) ⟶ G.X`. Its integral factor is a section
  of `G` over `Spec R`, restricted along `Spec K → Spec R`.

### Model forms

Let `M : IntegralModel R K G` and `N : IntegralModel R K P` be models, and let
`φ : N.Hom M f` be a model morphism over a generic morphism `f : P ⟶ G`. The
hypotheses above are required for `φ.hom`, and `N.IsSmooth` is assumed. As
before, `R` is a strictly Henselian valuation domain with fraction field `K`.

* `exists_parabolic_integral_factor`: every `g : rationalPoints G` equals
  `rationalPoints.map f h * M.integralPointMap x` for some
  `h : rationalPoints P` and some `x : M.integralSections`.
* `range_mul_integralPoints_eq_univ`: `Set.range (rationalPoints.map f) *
  M.integralPoints = Set.univ`.
* `modelData_range_mul_integralPoints_eq_univ`: the same equality for every
  `D : ReductiveParabolicSpreading.ModelData R K p`, for its ambient model.
  No quotient is supplied here.
* `range_mul_integralPoints_eq_univ_of_cocharacter`: suppose further that
  `R` is Noetherian and `IsReductive M.group` holds. Let `χ` be a
  cocharacter of `M.group` over `R`, and let `p : P ⟶ G` be a closed
  subgroup. Assume that `p ≫ M.genericIso.inv` has as range the generic
  dynamic parabolic `Dynamic.parabolic` of the base-changed cocharacter
  `Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ`. Then
  `Set.range (rationalPoints.map p) * M.integralPoints = Set.univ`.
* `hasLeftIntegralCovering_parabolic`: under the same hypotheses on `R` and
  `M`, and with `G.X.left` affine, `HasLeftIntegralCovering M H` holds. Here
  `H` is the group of `K`-points of the dynamic parabolic
  `Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
  M.genericIso.hom)`, that is, of `P_G(λ)` for the generic cocharacter `λ`
  of `χ` read in `G`.
* `baseChangeUnramified_hasLeftIntegralCovering_parabolic`: let `F` be a
  nonarchimedean local field and `G` a connected reductive group over `F`
  with `IsAffineHom G.X.hom`. Let `M : IntegralModel 𝒪[F] F G` have a
  connected reductive special fibre over `𝓀[F]`. Then the following holds
  for every cocharacter `χ` of `M.baseChangeUnramified.group` over
  `fixedFieldIntegers F`. Its generic dynamic parabolic in
  `baseChanged F (inertiaFixedField F) G` satisfies
  `HasLeftIntegralCovering M.baseChangeUnramified`. Its rational points
  times `M.baseChangeUnramified.integralPoints` are all of
  `rationalPoints (baseChanged F (inertiaFixedField F) G)`.

## Implemented proof

*Sections of smooth schemes.* Let `κ` be the residue field of `R` and `X₀`
the base change of `X` to `κ` (`ringBaseChange`). It is smooth and
surjective over `Spec κ`, so it is nonempty. The published
`hasDenseRationalPoints_of_smooth_of_isSepClosed` therefore gives a rational
point of `X₀`. `ringPointBaseChangeEquiv` and `rationalPointEquiv` turn it
into a `κ`-valued point `b` of `X` over `R`. The published Henselian lifting
`HenselianSections.exists_section_of_smooth_of_surjective` applies to the
surjection `R → κ`. It lifts `b` to a section `σ` of `X → Spec R`. That
section is the required `R`-point.

*Torsors.* `IntegralTorsorPoint.smooth_of_isIso_leftSMul` shows that `X` is
smooth over `Spec R`: it uses flatness, surjectivity and quasi-compactness of
`X → Spec R`, smoothness of `H` and invertibility of the shear. The previous
step then gives a section.

*Lifting.* Write `p₀` for the section of `Q` that corresponds to the given
`R`-point. The published fibre `Dynamic.flagQuotientFiber G q p₀` is the
pullback of `q` along `p₀`. `Dynamic.flagQuotientFiberModObj` lets `P` act on
it, and with `hfib` the shear is invertible
(`Dynamic.flagQuotientFiber_leftSMul_isIso`). Flatness, surjectivity and
quasi-compactness pass from `q.left` to the fibre by base change. The torsor
step gives an `R`-point of the fibre. Composed with the fibre inclusion
`Dynamic.flagQuotientFiberι`, it is an `R`-point of `G` whose image under
`q` is `p₀`.

*Covering.* The published valuative-criterion step
`IntegralParabolicCovering.exists_ringPoint_changeRing_eq` applies to the
proper `Q` over the valuation ring `R`. It extends `g⁻¹ ≫ q` to an `R`-point
`y` of `Q`, and the lifting step lifts `y` to an `R`-point `k` of `G`. By
`hfib`, `g * k|_K = h ≫ i` for some `K`-point `h` of `P`. Hence
`g = (h ≫ i) * (k⁻¹)|_K`, using `GrpObj.comp_inv`.
`exists_mul_rationalPoint` transports this through
`rationalPointEquiv_symm_left`.

*Model forms.* `exists_parabolic_integral_factor` transports `g` to a
fraction-field point of `M.group` through `M.genericIso.inv` and
`baseChangeBasePointsEquiv`, factors it, and transports back. It uses the
published identities `genericPoint_eq`, `genericPoint_map` and
`integralPointMap_eq` from the complete-ring module. These hold over any
domain. `range_mul_integralPoints_eq_univ` repackages this as an equality of
sets.

*Model data.* For `D : ModelData R K p`, the published
`ModelData.quotientMap_spec` applies with
`Langlands.Global.IntegralIwasawaFamily.relativeParabolicQuotient`, the
published proof of the relative parabolic quotient statement. It supplies
`Q` and `q` with all the hypotheses above, and `D.parabolicSmooth`
supplies smoothness of the subgroup model.

*Cocharacters.* `IntegralModel.DynamicParabolic.modelData` builds model
data from `χ`, `p`, the published `parabolicDynamic`, `IsReductive M.group`
and connected reductivity of every field fibre. The last input follows from
`IsReductive.isConnectedReductive_residueFiber` and
`fieldReductive_of_residueReductive`, as in the Library's local-field
`fieldReductive_localField`. Noetherianity of `R` is needed by
`DynamicParabolic.modelData`. For `hasLeftIntegralCovering_parabolic`, take
`p = Dynamic.Affine.parabolicHom λ` for the generic cocharacter `λ`. The
range hypothesis follows from `Dynamic.Affine.isRepresentedBy_parabolicHom`,
`IsRepresentedBy.comp_iso` and `Dynamic.parabolic_eq_comap_of_iso`, exactly
as in the Library's `range_parabolicHom_genericCocharacter`. The same
representability identifies `Set.range (rationalPoints.map p)` with the
`K`-points of `Dynamic.parabolic λ`.

*Unramified specialization.* The ring `fixedFieldIntegers F` meets the
hypotheses. It is a valuation subring of `inertiaFixedField F`, hence a
valuation domain with that fraction field. It is Henselian by
`fixedFieldIntegersIsHenselian`. Its residue field is an algebraic closure of
`𝓀[F]` by `fixedFieldResidueIsAlgClosure`, hence algebraically closed and
separably closed. It is a discrete valuation ring, hence Noetherian, by
`fixedFieldIntegersIsDVR_of_valuesFromBase` and `fixedFieldValuesFromBase`.
Reductivity of `M.baseChangeUnramified.group` is the published
`isReductive_baseChangeUnramified`. The generic group is affine because
`IsAffineHom` is stable under the pullback defining `baseChanged`.

## Provenance and scope

This is a derived local step. It follows the proof of Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), Theorem B.2.5 with
Lemma B.2.4, printed pp.543–544 / PDF pp.548–549, in the form of the
published complete-ring module `IntegralParabolicCovering`. That module
replaced the Henselian hypothesis of Lemma B.2.4 by adic completeness. This
module restores a Henselian hypothesis. It also replaces the finite residue
field and connected special fibre of Lemma B.2.4 (used there for Lang's
theorem) by a separably closed residue field: then a smooth surjective
scheme over the residue field has a rational point, by the published density
theorem. As in the complete-ring module, the quotient's geometry and the
coset criterion are explicit hypotheses in the general forms. In the
reductive cocharacter forms they come from the published
`relativeParabolicQuotient`. The Lean statements are not quoted from the
source.

The module proves no Levi decomposition of the parabolic and no link to
building data or root groups. It does not prove the special-stabilizer
identity `UnramifiedSpecialStabilizerStatement` or its uniqueness clause.
