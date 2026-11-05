# The opposite chart of the standard intertwining quotient and height integrability

Lean module: `Langlands.Representation.Plancherel.ParabolicOppositeQuotient`. The measure lemma is
in `Langlands.QuotientIntegration`; the subgroup equivalence, the normalizer lemma and the chart
are in `Langlands.HarishChandraSchwartz`; the results for actual parabolics are in
`Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. In Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1, printed pp. 277–279 (PDF pp. 43–45), the standard
intertwining integral of `f(u' g)` runs over the quotient `(U ∩ U') \ U'`; its convergence is
proved by writing the quotient through the opposite part `Ū ∩ U'` and bounding the integrand
by negative powers of the height there. This module supplies the reflection-free part of that
argument for the actual rational-point groups of the conditional intertwining statement
(`ConditionalParabolicIntertwiningStatement`). It verifies the open-cell contraction data for
two parabolics with a common Levi, builds the chart `(Ū ∩ U')(F) ≃ₜ (U ∩ U')(F) \ U'(F)`, and
proves that `q ↦ ‖c⁻¹(q)‖ ^ (-s)` is integrable on the quotient for every regular
right-invariant quotient measure and large `s`. The arguments are derived from Library results,
not transcribed from the source.

## Setting and notation

- `Γ` is a topological group; `LeftQuotient H` is the actual quotient `H \ Γ` of left cosets
  `H g`, and `rightTranslate H g` is right translation by `g` on it.
- `F` carries `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`. `G` is a
  smooth affine group scheme over `Spec F`, locally of finite type (`[IsAffineHom G.X.hom]`,
  `[LocallyOfFiniteType G.X.hom]`, `[Smooth G.X.hom]`). `G(F)` is `rationalPoints G` with
  `rationalPointTopology F G.X`, a topological group.
- `r : ParabolicRootPresentation p l a` and `r' : ParabolicRootPresentation p' l' a` present two
  parabolics `p : P ⟶ G`, `p' : P' ⟶ G` with Levis `l`, `l'` and a common split component
  `a : A ⟶ M`, with `hLevi : l ≫ p = l' ≫ p'`. `n`, `n'` are geometric unipotent radicals
  (`hn`, `hn'`). As in the host statement, `Ppt`, `Upt`, `U'pt` are subgroups of `G(F)` with
  `hPpt`, `hUpt`, `hU'pt` identifying them with the actual points of `P`, `U` and `U'`, and
  `Mpt = parabolicLeviPointSubgroup p l`.
- `λ_P = groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p` and
  `λ_{P'} = groupHom r'.splitComponentCocharacter ≫ a ≫ l' ≫ p'` are the split-component
  cocharacters, and `Ū(F) = parabolicOppositeRadicalPoints r = U(λ_P⁻¹)(F)` (public module
  `ParabolicPointUniformNumerator`). `λ(t) = gmRationalPoint t ≫ λ.hom.hom`.
- `IsOpenCellContraction` and `productHomeomorph` are from `OpenCellIntersectionProduct`;
  `isOpenCellContraction_dynamic` is from `UnipotentIntersectionProduct`;
  `exists_integrable_rationalMatrixNorm_rpow_neg` is from `UnipotentHeightIntegrability`.

## Declarations

### Integrability through a complementary chart

- `QuotientIntegration.integrable_comp_factorQuotientHomeomorph_symm`: let `Γ` be locally
  compact, `H, K` subgroups and `m : H × K ≃ₜ Γ` with `m (h, k) = h * k`, and let `c` be the
  public chart `factorQuotientHomeomorph H Subtype.val m hm : K ≃ₜ LeftQuotient H`. Let `ν` be
  a regular measure on `LeftQuotient H` preserved by every `rightTranslate H g`, and `μK` a
  regular Haar measure on `K` (left invariant only). If `f : K → E` is `μK`-integrable and
  `f k⁻¹ = f k` for all `k`, then `q ↦ f (c⁻¹ q)` is `ν`-integrable.

### Subgroups

- `subgroupOfInfEquiv A B : A.subgroupOf B ≃ₜ* (A ⊓ B)` (definition), the identity on
  underlying points of `Γ`, with `coe_subgroupOfInfEquiv` (simp).
- `mem_normalizer_inf`: an element normalizing `A` and `B` normalizes `A ⊓ B`.
- `IsOpenCellContraction.quotientChart hc : V.subgroupOf U' ≃ₜ LeftQuotient (U.subgroupOf U')`
  (definition): the public `factorQuotientHomeomorph` of `hc.productHomeomorph`.
  `quotientChart_apply`: it sends `k` to the coset of `k`.

### Actual parabolics

- `splitComponentCocharacter_point_mem_parabolicLevi`: every `λ_{P'}(t)` lies in `Mpt`. (With
  `r' = r` and `hLevi = rfl` this also covers `λ_P(t)`.)
- `parabolic_isOpenCellContraction`: for `h' : IsSemidirectDecomposition P'pt Mpt U'pt` and
  `t ∈ Fˣ` with `t ^ n → 0`,
  `IsOpenCellContraction Ppt Ū(F) Upt U'pt Mpt (λ_{P'}(t)) (λ_P(t))`.
- `exists_integrable_quotientChart_symm_rationalMatrixNorm` (main theorem): assume moreover
  that `U'pt` is closed, let `ρ₀` be a closed representation of `G` on a nonempty `Fin N`, and
  let `qν` be a regular measure on `QuotientSpace (U := Upt) U'pt = LeftQuotient (Upt.subgroupOf
  U'pt)` preserved by every right translation. With `c` the `quotientChart` of
  `parabolic_isOpenCellContraction`, there is `D : ℕ` such that for every real `s > D` the
  function `q ↦ rationalMatrixNorm F ρ₀ (c⁻¹ q) ^ (-s)` is `qν`-integrable.

## Proofs as implemented

**Complementary chart.** `K` is locally compact as a closed-embedded copy of the locally compact
quotient (public `leftQuotient_locallyCompactSpace`). Put `M = map c⁻¹ ν`. It is regular
(`Measure.Regular.map`) and right invariant (public
`isMulRightInvariant_map_factorQuotientHomeomorph_symm`). Its inverse `M.inv` is therefore
left invariant and regular, so Mathlib's `isMulLeftInvariant_eq_smul_of_regular` gives
`M.inv = a • μK` and hence `M = a • μK.inv`, with `a = haarScalarFactor M.inv μK`. Since
`μK.inv = map inv μK` and `f ∘ inv = f`, `integrable_map_equiv` for `MeasurableEquiv.inv K`
shows that `f` is `μK.inv`-integrable, hence `M`-integrable (`Integrable.smul_measure_nnreal`).
Finally `integrable_map_equiv` for `c⁻¹` turns `M`-integrability of `f` into `ν`-integrability
of `f ∘ c⁻¹`. No right invariance of `μK` is needed, because `f` is inversion invariant.

**Subgroups.** `subgroupOfInfEquiv` sends `x` to its underlying point; the inverse uses the two
memberships of `A ⊓ B`. Both maps are continuous as subtype maps of the subspace topologies,
and multiplication is preserved by definition. `mem_normalizer_inf` applies
`Subgroup.mem_normalizer_iff` to both factors and `Subgroup.mem_inf`.

**Split-component values.** `λ_{P'}(t)` is the image of the point
`gmRationalPoint t ≫ (groupHom r'.splitComponentCocharacter ≫ a).hom.hom` under `l' ≫ p'`, and
`l' ≫ p' = l ≫ p`. This is `SubgroupFunctor.mem_range` after `Grp.comp_hom_hom`.

**Open-cell data.** Rewrite the four supplied subgroups with public identities:
`Ppt = P(λ_P)(F)` (`parabolic_eq_splitComponentCocharacter`), `Upt = U(λ_P)(F)` and
`U'pt = U(λ_{P'})(F)` (`range_comp_radical_eq` for `hn`, `hn'`), and `Mpt = Z(λ_P)(F)`
(`levi_eq_splitComponentCocharacter`). The two hypotheses of `isOpenCellContraction_dynamic`
are: `λ_{P'}(t) ∈ Z(λ_P)(F)`, which is the previous lemma; and `Z(λ_P)(F) ∩ U(λ_{P'})(F) = 1`,
which follows from `h'`, because the Levi projection of `h'` is the identity on `Mpt`
(`projection_levi`) and trivial on `U'pt` (`projection_unipotent`).

**Height integrability.** Let `K = Ū(F).subgroupOf U'pt` and `H₀ = Ū(F) ⊓ U'pt`, both with
their Borel structures. `Ū(F)` is closed (public `isClosed_unipotentPoints`), so `H₀` is closed
in `G(F)` and locally compact, and so is `K ≃ₜ* H₀`. Take the Haar measure `μK` on `K` and
`ν₀ = map e μK` on `H₀` for `e = subgroupOfInfEquiv`; it is a regular Haar measure
(`ContinuousMulEquiv.isHaarMeasure_map`, `Measure.Regular.map`). `H₀ ≤ U(λ_P⁻¹)(F)`, and every
`λ_P(t)` lies in `Mpt`, which normalizes `Ū(F)` (public
`parabolicLevi_le_normalizer_oppositeRadicalPoints`) and `U'pt` (`h'.levi_le_normalizer`),
hence normalizes `H₀` (`mem_normalizer_inf`). So
`exists_integrable_rationalMatrixNorm_rpow_neg` gives `D` with `x ↦ ‖x‖ ^ (-s)` integrable on
`H₀` for `s > D`. Pulling back along `e` (`integrable_map_equiv`) gives integrability of
`k ↦ ‖k‖ ^ (-s)` for `μK`. This function is inversion invariant (public
`rationalMatrixNorm_inv`), so the complementary-chart lemma, applied to `hc.productHomeomorph`,
gives the claim.

## Scope

The hypotheses on `qν` are regularity and right invariance; both are fields of
`QuotientIntegration.IsCompatible`. The module does not bound any intertwining integrand by a
power of the height, does not prove the Iwasawa or root-cone estimates, and does not prove
convergence on the region of the host statement. The exponent `D` is not explicit. Nothing here
completes the host conditional intertwining theorem.
