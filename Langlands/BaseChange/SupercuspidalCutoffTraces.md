# Traces of cut-off supercuspidal coefficients

The module `Langlands.BaseChange.SupercuspidalCutoffTraces` (namespace
`Langlands.BaseChange.SupercuspidalCutoff`) computes the operators `ρ(f_x)` of the cut-off
coefficients `f_x = cutoff π ℓ hn hπ hℓ x` of the module
`Langlands.BaseChange.SupercuspidalCutoffCoefficient`, and the trace of `π(f_x)`.

Setting: `F` a nonarchimedean local field (`[ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), `0 < n`, `GL_n(F)` Hausdorff with a Borel σ-algebra and a Haar
measure `μ`, `π` a supercuspidal representation of `GL_n(F)` on `V`, `ℓ` a linear form on `V`
that is smooth for the contragredient action, and `χ` a character of the centre with
`HasCentralCharacterRep π χ` (module `Langlands.BaseChange.PseudoCoefficient`). For a smooth
representation `ρ`, `ρ(f)` is the Library's `Hecke.integratedAction μ ρ hρ f`
(`ρ(f) w = ∫ f(g) ρ(g) w dμ(g)`), and `Character.distribution μ ρ hρ f` its trace.

## Central elements and integrability

- `centralUniformizerCenter`: the scalar uniformizer as an element of the centre.
- `coeff_central_mul`: `coeff π ℓ x (z g) = χ(z⁻¹) coeff π ℓ x g` for central `z`;
  `character_inv_mul_character`: `χ(z⁻¹) χ(z) = 1`; `mul_central_comm`.
- `continuous_matrixCoefficient`: `g ↦ L(ρ(g) w)` is continuous for smooth `ρ` and any linear
  form `L`; `continuous_coeff`.
- `integrable_levelSet_coeff_mul`, `integrable_cutoffFun_mul`: for continuous `b`, the product
  of `b` with the coefficient restricted to a level set `{ord det = j}`, or with `f_x`, is
  continuous with compact support, hence integrable.

## Intertwining

`integratedAction_cutoff_rho`: for every smooth `ρ` on `W` with `HasCentralCharacterRep ρ χ`,
`ρ(f_{π(h) x}) w = ρ(h) (ρ(f_x) w)`.

Proof. Two vectors of `W` agree when every linear form agrees on them
(`Module.forall_dual_apply_eq_zero_iff`), and `L(ρ(f) w) = ∫ f(g) L(ρ(g) w) dμ(g)`
(`Hecke.integratedAction_dual`). With `Φ(g) = ℓ(π(g⁻¹ h) x) L(ρ(g) w)`, the left side is
`∫ 1_{window}(g) Φ(g)` and the right side `∫ 1_{window}(g) Φ(h g)`, where the window is
`{0 ≤ ord det g < n}`. The function `Φ` is invariant under left multiplication by the scalar
uniformizer `z` (the factors `χ(z⁻¹)` from `π` and `χ(z)` from `ρ` cancel) and integrable on
every level set, so `PeriodicWindow.integral_window_comp_mul_left` (module
`Langlands.BaseChange.PeriodicWindowIntegral`, with `detOrd z = n`) identifies the two
integrals.

`cutoffActionMap` is the linear map `x ↦ ρ(f_x) w` and `cutoffIntertwiner` the resulting
intertwining map from `π` to `ρ`.

## Other representations

`integratedAction_cutoff_eq_zero`: if `π` and `ρ` are irreducible, `ρ` is admissible with
central character `χ`, and `ρ` is not isomorphic to `π`, then `ρ(f_x) = 0` for every `x`. The
intertwiner `x ↦ ρ(f_x) w` from `π` to `ρ` is zero by Mathlib's Schur lemma (the instance
`Subsingleton (IntertwiningMap π ρ)` for irreducible, non-isomorphic `π` and `ρ`, module
`Mathlib.RepresentationTheory.Irreducible`). Consequently `distribution_cutoff_eq_zero`:
`tr ρ(f_x) = 0`. No temperedness or unitarity of `ρ` is used.

## The representation itself

- `exists_integratedAction_cutoff_self`: if `π` is irreducible, there is `c : V → ℂ` with
  `π(f_x) w = c(w) x` for all `x` and `w`. For fixed `w` the map `x ↦ π(f_x) w` is an
  endomorphism of `π` (intertwining with `ρ = π`), hence a scalar by the Library's
  `admissibleSchur_scalarEndomorphism` (module `Langlands.Representation.Smooth.Schur.Proof`).
- `distribution_cutoff_self`: given such `c` and `x ≠ 0`, `tr π(f_x) = c(x)`. The range of
  `π(f_x)` lies in the line `ℂ x`, on which `π(f_x)` acts by `c(x)`; the trace is computed on that
  line by `Character.distribution_eq_subspace` (module
  `Langlands.Representation.Character.Basic`).

## Provenance

The trace conditions correspond to Kazhdan, *Cuspidal geometry of p-adic groups* (1986), source
ID `kazhdan-1986-cuspidal-geometry`, §5, Proposition 3 (a) and its proof (printed p. 28). There
`π` is square integrable, `v` is a unit vector, `f_π(g) = (π(g) v, v)` is the raw coefficient and
`d_π` the formal dimension; Kazhdan takes `h_π` with `d_π⁻¹ f_π − h_π ∈ I(G)` and obtains
`⟨π', h_π⟩ = δ_{π, π'}` for tempered `π'`, citing §1 of his reference [9]. His pairing is
`⟨π', h⟩ = Tr π'(h*)` with `h*(g) = h(g⁻¹)` (§1.2, printed p. 8), so a test function is evaluated
at `g⁻¹` against `π'(g)`. The Library's `Hecke.integratedAction` evaluates the test function at
`g` against `ρ(g)`; this is why the coefficient used here is the inverse-argument coefficient
`g ↦ ℓ(π(g⁻¹) x)`.

The intertwining argument written here is the one of the Markdown of the Library's statement
`SupercuspidalEllipticPseudoCoefficientStatement` (step 3 of its sketch), where the integral is
taken over `Z \ G`; it needs neither temperedness nor unitarity of `ρ`. The integral over
`Z \ G` is replaced by the window integral of `Langlands.BaseChange.PeriodicWindowIntegral`. The
normalization differs from Kazhdan's: the scalar `c` of `exists_integratedAction_cutoff_self`
comes from Schur's lemma and is not identified with a formal degree; its nonvanishing is proved
in `Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient`, and the pseudo-coefficient is
`c(s)⁻¹ f_s`.
