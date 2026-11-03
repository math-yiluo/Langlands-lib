# Lie algebras of dynamic subgroups: proof

This module proves the published proposition `DynamicLieStatement`
([Dynamic.LieStatement](LieStatement.md)) as the theorem
`Langlands.GroupScheme.dynamicLie : DynamicLieStatement.{u}`. The theorem keeps
every binder of the statement: a field `k : Type u`, a group scheme `G` over
`Spec k` with `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, a
cocharacter `χ : 𝔾_m ⟶ G` and `X : lieKernel G k`. Neither smoothness nor a
nontrivial cocharacter is assumed, and no case distinction is made for the
trivial cocharacter. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

Write `g_n = weightSpace χ (Gm.powerHom _ n)`. All three equivalences are
reduced to statements about one family of vectors `c_n(X) ∈ Lie(G)(k)`,
`n ∈ ℤ`: the *weight coefficients* of `X`. The proof shows

* `X.val ∈ Z_G(χ)` if and only if `c_n(X) = X` for `n = 0` and `c_n(X) = 0` otherwise;
* `X.val ∈ P_G(χ)` if and only if `c_n(X) = 0` for all `n < 0`;
* `X.val ∈ U_G(χ)` if and only if `c_n(X) = 0` for all `n ≤ 0`.

It also shows that these three conditions describe `g_0`,
`⨆ n : ℕ, g_n` and `⨆ n : ℕ, g_(n+1)`. The sections below follow the sections
of the Lean file.

## 1. Weight coefficients (sections `GmIso` and `Weights`)

The Library decomposes the Lie algebra into weight spaces for split tori
`splitTorus S I`. It does not do so for `𝔾_m` itself. The proof transports
the cocharacter to the rank-one split torus along the published isomorphism
`splitTorus.gmIso S : 𝔾_m ≅ splitTorus S PUnit`.

* `gmIso_hom_apply` and `gmIso_inv_apply`: on points, this isomorphism
  preserves the unit coordinate. They follow from `isoOfPointModels_hom`.
* `comapIso_proj`: pulling the coordinate character `proj ()` back along
  `gmIso` gives `𝟙 (Gm _)`. This is checked on points with
  `CommGroupScheme.hom_ext_points`.
* `powerHom_eq_comapIso`: `Gm.powerHom _ n` is the pull-back of
  `rankOneCharacter k n = (characterLatticeEquiv k PUnit).symm (fun _ => n)`.
  This uses `characterLatticeEquiv_symm_eq`, the sum over `PUnit` and
  `comapIso_proj`.
* `weightSpace_powerHom`: hence `g_n` equals the weight space of
  `rankOneCharacter k n` for `torusHom k G χ = gmIso.inv ≫ χ`. This follows from
  the published `weightSpace_comapIso`.

The weight coefficients are
`weightCoeffs k G χ X = splitTorus.universalAdjointCoefficients PUnit G (torusHom k G χ) X`.
This is the finitely supported family, indexed by `PUnit → ℤ`, of coefficients
of the universal adjoint vector `Ad(torusHom(t)) X` over
`k[t^{±1}] = AddMonoidAlgebra k (PUnit → ℤ)`. Here `c_n(X)` is its value at
`fun _ => n`. The published split-torus lemmas give three facts:

* `weightCoeffs_mem`: `c_n(X) ∈ g_n`. This is `characterAdjointCoefficients_mem`.
* `weightCoeffs_of_mem`: if `X ∈ g_n`, the whole family is the single vector `X`
  at `fun _ => n`. This is `universalAdjointCoefficients_of_mem_weightSpace`.
* `weightCoeffs_sum`: the coefficients sum to `X`. This is
  `universalAdjointCoefficients_sum`.

From these:

* `mem_weightSpace_zero_iff`: `X ∈ g_0` if and only if `c_n(X) = X` for `n = 0`
  and `c_n(X) = 0` otherwise. In the reverse direction, `X = c_0(X) ∈ g_0`.
* `mem_iSup_weightSpace_iff`: for every `s : ℕ → ℤ`, `X ∈ ⨆ j, g_(s j)` if and
  only if `c_n(X) = 0` for every `n` outside the range of `s`.
  * Forward: by `Submodule.iSup_induction`. The condition is linear, and every
    vector of `g_(s j)` satisfies it by `weightCoeffs_of_mem`.
  * Backward: `X` is the finite sum of its coefficients. Each coefficient lies
    in some `g_(s j)` or vanishes.

  This lemma is compiled with the finite limit
  `set_option maxHeartbeats 2000000`.

## 2. Two coordinate systems (section `Chart`)

The membership criteria for dynamic subgroups in `Dynamic.AffineChart` use the
global sections `Γ(G, ⊤)` and the coaction `coaction χ : Γ(G, ⊤) → Γ(G, ⊤)[T^{±1}]`.
The Lie-coefficient interfaces (`Lie.kernelDerivationLinearEquiv`,
`Lie.kernelCoefficient`) use the chosen coordinates `Lie.coordinateAlgebra G`.
The two are compared through

* `chartCoordinates G = Spec.preimage ((Lie.coordinateIso G).hom.left ≫ G.X.left.isoSpec.hom)`.
  It is surjective (`chartCoordinates_surjective`): `coordinatesChart G` is an
  explicit right inverse.
* `pointRing_eq_pointCoordinates`: for every point `y` of `G` over an affine
  test algebra `A`, `AffineChart.pointRing y = chartCoordinates G ≫ Lie.pointCoordinates G y`.

## 3. Membership criteria in chart coordinates (section `Membership`)

Let `x` be a point of `G` over an affine test scheme `Spec A`.

* `chart_mem_parabolic_iff`: `x ∈ P_G(χ)` if and only if `pointRing x` kills
  every negative-degree coefficient of `coaction χ b`. The argument is that of
  the published `Corepresented.mem_parabolic_iff`, in the chart of
  `Dynamic.AffineChart`. An orbit extension gives a lift through `A[T]`. A lift
  of the coefficients gives an extension through `AffineChart.polynomialExtension`.
* `chart_mem_centralizer_iff`: `x ∈ Z_G(χ)` if and only if
  `coaction χ ≫ laurentCoeffMap (pointRing x) = pointRing x ≫ C ≫ toLaurent`.
  `laurentPoint` has the section `laurentPointInv`, and points over
  `Spec A[T^{±1}]` are determined by their chart coordinates.
* For `U_G(χ)` the published `AffineChart.mem_unipotent_iff` is used as is.

## 4. The comparison map `ψ` (sections `Laurent` and `Orbit`)

`laurentPsiAlg k : (k[t^{±1}])[ε] → (k[ε])[T^{±1}]` is a `k`-algebra map. It is
`TrivSqZeroExt.lift` of two parts:

* `laurentInl`: re-index exponents along `(PUnit → ℤ) ≃+ ℤ` and include
  coefficients by `inl`;
* `laurentInr = C(ε) · laurentInl`.

The coefficient lemmas `coeff_laurentPsiAlg_fst` and `coeff_laurentPsiAlg_snd`
say: the `n`-th coefficient of `ψ(z)` has constant part
`z.fst.coeff (fun _ => n)` and infinitesimal part `z.snd.coeff (fun _ => n)`.

`laurentHom k` is `Spec ψ` as a morphism over `Spec k`. Its source is the
Laurent test scheme `laurentScheme (dualMap k)`, that is `Spec (k[ε])[T^{±1}]`.
Its target is the affine test object of `(k[t^{±1}])[ε]`. Two lemmas describe
it:

* `laurentHom_comp_coefficient`: `Spec ψ` followed by the coefficient change
  `k[ε] → (k[t^{±1}])[ε]` is the first projection of the Laurent point
  `laurentPoint (dualMap k)`. This is a coefficientwise check of `ψ ∘ coefficientMap = C`.
* `laurentHom_comp_constant`: `Spec ψ` followed by the constant universal torus
  point and `gmIso.inv` is the second projection. Both sides have the unit
  coordinate `T`. The universal point is computed with the published
  `algebraPointsEquiv_universalPoint` (`pointsEquiv_universalPoint`), and
  `ψ(t) = T`.

## 5. The orbit identity and coefficient formulas (section `Identity`)

`dualPoint k X` is `X.val`, viewed as a point over `Over.mk (dualMap k)`.
`universalVector k χ X` is the universal adjoint vector
`(splitTorus.universalAdjoint PUnit G (torusHom k G χ) X).toMul`.

* `laurentPoint_comp_orbit_eq`:
  `laurentPoint (dualMap k) ≫ orbit χ (dualPoint k X) = laurentHom k ≫ (universalVector k χ X).val`.
  Both sides are products `χ(t) · X · χ(t)⁻¹`: the orbit map by definition, and
  the adjoint action by `adjoint_val`. The two lemmas of section 4 identify the
  factors.
* `coaction_comp_laurentCoeffMap`: this identity combines with
  `AffineChart.pointRing_laurentPoint_comp_orbit`, `AffineChart.pointRing_comp`
  and the bridge of section 2. The result is
  `coaction χ ≫ laurentCoeffMap (pointRing X) = chartCoordinates G ≫ pointCoordinates (universalVector) ≫ ψ`.
* `pointRing_coaction_coeff_fst` and `pointRing_coaction_coeff_snd`: write
  `θ = chartCoordinates G` and `D = Lie.kernelDerivationLinearEquiv G`. For every
  `b ∈ Γ(G, ⊤)` and `n ∈ ℤ`, the dual number
  `pointRing X ((coaction χ b).coeff n)` has
  * constant part `coordinateOrigin G (θ b)` if `n = 0` and `0` otherwise
    (from `Lie.pointCoordinates_kernel`);
  * infinitesimal part `D (c_n X) (θ b)` (from `universalAdjointCoefficients_apply`
    and `Lie.kernelCoefficient_apply`).

## 6. Assembly (section `Assembly` and `dynamicLie`)

Supporting lemmas:

* `eq_of_chart`: two Lie vectors agree when their derivations agree on every
  `θ b`. This uses surjectivity of `θ` and injectivity of `D`.
* `pointRing_dualPoint`: the chart coordinates of `X.val` itself.
* `counit_eq`: `AffineChart.counit G b = coordinateOrigin G (θ b)`. Both sides
  classify the identity point.

The three clauses:

* `mem_centralizer_iff_weightCoeffs`: by `chart_mem_centralizer_iff`, compare
  `n`-th coefficients and dual-number components. The constant parts always
  agree. The infinitesimal parts give `D (c_n X) (θ b) = D (if n = 0 then X else 0) (θ b)`.
* `mem_parabolic_iff_weightCoeffs`: by `chart_mem_parabolic_iff`. For `n < 0`
  the constant part vanishes, so the condition is `c_n(X) = 0`.
* `mem_unipotent_iff_weightCoeffs`: by `AffineChart.mem_unipotent_iff`. The
  negative coefficients are handled as for the parabolic clause. The constant
  coefficient must equal the image of the counit. Its constant part does so by
  `counit_eq`, and its infinitesimal part gives `c_0(X) = 0`.

`dynamicLie` combines these with `mem_weightSpace_zero_iff` and with
`mem_iSup_weightSpace_iff` for `s j = j` and `s j = j + 1`. Their ranges are
`{n ≥ 0}` and `{n ≥ 1}` (`not_mem_range_natCast_iff`,
`not_mem_range_natCast_add_one_iff`).

## Relation to the literature

The statement is Conrad–Gabber–Prasad, *Pseudo-reductive groups* (second
edition), Proposition 2.1.8(1). The implemented route differs from Step 1 of its
proof (printed pp.53–54) in two places, though the graded idea is the same:
membership is read off the graded pieces of the coordinate ring under the
coaction.

* `Lie(U_G(λ))` is computed with the Library's coordinate criterion for
  `U_G(χ)` (constant coefficient equal to the counit), not with the limit
  argument.
* `Lie(Z_G(λ))` is computed directly from the centralizer criterion, not as
  `Lie(P_G(λ)) ∩ Lie(P_G(−λ))`.

The weight spaces are matched with the graded pieces through the universal
adjoint vector and its finitely many coefficients.
