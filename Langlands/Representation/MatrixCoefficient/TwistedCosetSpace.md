# The twisted `ℓ²` space of a coset space and its left translations

Author: Worker 4988.

## Statements

`G` is a group, `J` a subgroup and `ψ : J →* ℂ` a group homomorphism into the
multiplicative monoid of `ℂ`. `α.out` is the representative that Mathlib chooses for
`α ∈ G ⧸ J`.

### Lifting functions on `G ⧸ J`

* `out_inv_mul_mem`: `(g J).out⁻¹ * g ∈ J`.
* `phase g = ψ ((g J).out⁻¹ * g)`. `phase_mul`: `phase (g * j) = phase g * ψ j` for
  `j ∈ J`. `phase_out`: `phase α.out = 1`.
* `lift F g = phase g * F (g J)` for `F : G ⧸ J → ℂ`.
  * `lift_mul`: `lift F (g * j) = lift F g * ψ j` for `j ∈ J`.
  * `lift_out`: `lift F α.out = F α`.
  * `lift_restrict`: if `f : G → ℂ` satisfies `f (g * j) = f g * ψ j` for all `g` and all
    `j ∈ J`, then `lift (α ↦ f α.out) = f`.
  * `lift_add`, `lift_smul`: `lift` is linear in `F`.
* `translateFun h F α = lift F (h⁻¹ * α.out)`, and `lift_translateFun`:
  `lift (translateFun h F) g = lift F (h⁻¹ * g)`.

From here on, `hψ : ∀ j, ‖ψ j‖ = 1`.

* `norm_phase`, `norm_lift`, `enorm_lift`: `‖phase g‖ = 1` and
  `‖lift F g‖ = ‖F (g J)‖`, also for the extended norm.
* `norm_translateFun`: `‖translateFun h F α‖ = ‖F (h⁻¹ • α)‖`.
* `enorm_eq_of_norm_eq`, `enorm_eq_one_of_norm_eq_one`: complex numbers with equal norms
  have equal extended norms; norm `1` gives extended norm `1`.

### The Hilbert space and the translations

* `L2 J` is Mathlib's `lp (fun _ : G ⧸ J => ℂ) 2`, that is, `ℓ²(G ⧸ J)`.
* `norm_eq_of_enorm_sq_eq`: two vectors with equal squared extended norms have equal norms.
* `tsum_enorm_translateFun`, `memℓp_translateFun`: `translateFun h` preserves the sum
  `∑' α, ‖F α‖ₑ ^ 2`, so it maps `ℓ²` into `ℓ²`.
* `translateₗ h`: the linear map `F ↦ translateFun h F` on `L2 J`, with
  `translateₗ_apply`, `lift_translateₗ` (`lift (translateₗ h F) g = lift F (h⁻¹ * g)`),
  `translateₗ_mul` (`translateₗ h ∘ translateₗ h' = translateₗ (h * h')`) and
  `translateₗ_one`.
* `translate h : L2 J ≃ₗᵢ[ℂ] L2 J`: left translation by `h` as a linear isometry
  equivalence. `translate_apply`, `translate_symm` (`(translate h).symm = translate h⁻¹`),
  `translate_mul_apply`.
* `translates`: the set of the operators `translate h`, `h ∈ G`, as bounded operators.
* `star_translate`: the adjoint of `translate h` is `translate h⁻¹`.
* `mem_centralizer_translates_iff`: `x` lies in the commutant
  `StarSubalgebra.centralizer ℂ (translates hψ)` iff
  `translate h (x F) = x (translate h F)` for all `h` and `F`.

### The vector `xi`

* `xi = lp.single 2 (1 J) (phase 1)⁻¹`, the twisted indicator vector of `J`.
* `lift_xi`: `lift xi g = ψ g` if `g ∈ J`, and `0` otherwise.
* `translate_xi`: `translate h xi = lp.single 2 (h J) c` for some `c` with `‖c‖ = 1`.
* `translate_xi_of_mem`: for `j ∈ J`, `translate j xi = d • xi` for some `d` with
  `‖d‖ = 1`.
* `eq_zero_of_apply_xi`: if `x` is in the commutant of the translations and `x xi = 0`,
  then `x = 0`. So `xi` is a separating vector for the commutant.
* `norm_star_apply_xi_apply`: for `x` in the commutant,
  `‖(star x xi) α‖ = ‖lift (x xi) α.out⁻¹‖`.

### Traciality

Now `G` is a topological group, `J` is open and contains the center `Z(G)`, and `μ` is a
Haar measure on `G ⧸ Z(G)` that is also right invariant.

* `norm_apply_xi_eq_norm_star_apply_xi`: if `μ (CentralCoset.centralImage J) ≠ ∞` and `x`
  is in the commutant of the translations, then `‖x xi‖ = ‖star x xi‖`.

## Provenance

These are internal helpers for the proof of the Remark of Renard IV.3.2
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
In that proof `J = K · Z(G)` for a small compact open subgroup `K`, and `ψ` is the central
character on `Z(G)` and trivial on `K`. The space `L2 J` models the right `K`-invariant
functions in `L²(G ⧸ Z(G), χ)`. Matrix coefficients `g ↦ ℓ(π(g) v)` with `v` fixed by `K`
satisfy `f (g * j) = f g * ψ j`, and `lift_restrict` identifies them with their values on
the representatives. On the commutant of the left translations, consider the vector
functional `x ↦ ⟪xi, x xi⟫`. It is complex linear in `x`, because Mathlib's inner product is
conjugate linear in its first argument. The equality `‖x xi‖ = ‖star x xi‖` of
`norm_apply_xi_eq_norm_star_apply_xi` is the usual criterion for this functional to be a
trace. By polarization it gives `⟪y xi, x xi⟫ = ⟪star x xi, star y xi⟫` for `x, y` in the
commutant (`Langlands.Analysis.inner_eq_inner_star_of_norm_eq` in `TracialFiniteness.lean`),
that is, `⟪xi, (star y * x) xi⟫ = ⟪xi, (x * star y) xi⟫`. This module proves only the norm
equality, not the trace identity. The
proof of the Remark uses it to bound the dimension of the `K`-fixed vectors. The constructions
are standard; the statements and proofs are Worker 4988's. The unimodularity input is
`CentralCoset.tsum_out_eq_tsum_out_inv` from `CentralCosetSum.lean`.

## Lean proof

* `out_inv_mul_mem`, `lift_restrict`: from `CentralCoset.exists_out_mk_eq_mul`,
  `(g J).out = g j` with `j ∈ J`. Then `phase g * ψ j = ψ 1 = 1`, so
  `lift (α ↦ f α.out) g = phase g * f g * ψ j = f g`.
* `lift_translateFun` is `lift_restrict` applied to `g ↦ lift F (h⁻¹ * g)`.
* `norm_translateFun`: `|phase| = 1` and `(h⁻¹ * α.out) J = h⁻¹ • α`
  (`MulAction.Quotient.mk_smul_out`).
* `tsum_enorm_translateFun`: reindex the sum by the permutation `α ↦ h⁻¹ • α`
  (`Equiv.tsum_eq`). The `ℓ²` norm is converted to the sum by
  `Langlands.Analysis.lp_two_enorm_sq_eq_tsum`, and the sum back to `Memℓp` by
  `memℓp_two_of_tsum_enorm_ne_top`, both from `Langlands/Analysis/FiberLIntegral.lean`.
* `translate`: `LinearEquiv.ofLinearMap` with the inverse `translateₗ h⁻¹`. The norm is
  preserved because the squared extended norms agree.
* `star_translate`: `LinearIsometryEquiv.star_eq_symm` and `translate_symm`.
* `mem_centralizer_translates_iff`: `StarSubalgebra.mem_centralizer_iff`; the adjoint
  condition reduces to commuting with `translate h⁻¹`.
* `lift_xi`: on `J`, `lift xi j = lift xi 1 * ψ j` by `lift_mul`, and `lift xi 1 = 1` since
  `xi` has the value `(phase 1)⁻¹` at `1 J`. Off `J`, the class of `g` is not `1 J`.
* `translate_xi`: `lift xi (h⁻¹ * β.out)` is nonzero only if `h⁻¹ * β.out ∈ J`, that is,
  `β = h J`. There its value is `ψ (h⁻¹ * (h J).out)`, of norm `1`.
* `eq_zero_of_apply_xi`: each `lp.single 2 α a` is a multiple of `translate α.out xi`, so `x`
  kills it by commutation. The vector `F` is the `ℓ²` sum of its single components
  (`lp.hasSum_single`), and `x` is continuous (`HasSum.mapL`).
* `norm_star_apply_xi_apply`: the coordinate at `α` is
  `⟪lp.single 2 α 1, x† xi⟫ = ⟪x (lp.single 2 α 1), xi⟫`
  (`ContinuousLinearMap.adjoint_inner_right`). `lp.single 2 α 1` is a unit multiple of
  `translate α.out xi`. Commute `x` past the translation, move the translation to the other
  side (`LinearIsometryEquiv.inner_map_map`) and use `translate_xi` for `α.out⁻¹`. The result
  is a unit multiple of `(x xi)` at the class of `α.out⁻¹`, that is, of
  `lift (x xi) α.out⁻¹` up to a phase.
* `norm_apply_xi_eq_norm_star_apply_xi`: let `Φ g = ‖lift (x xi) g‖ₑ ^ 2`. It is right
  `J`-invariant by `lift_mul` and left `J`-invariant because `translate j xi` is a unit
  multiple of `xi` and `x` commutes with `translate j`. Both squared norms are sums of
  squared coordinates: `∑' α, Φ α.out` for `x xi` (`lift_out`) and `∑' α, Φ α.out⁻¹` for
  `star x xi` (`norm_star_apply_xi_apply`). `CentralCoset.tsum_out_eq_tsum_out_inv` equates
  them.
