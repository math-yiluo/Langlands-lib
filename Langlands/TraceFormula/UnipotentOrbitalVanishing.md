# Twisted orbital integrals that vanish along a subgroup

The module `Langlands.TraceFormula.UnipotentOrbitalVanishing` proves a general criterion for the
vanishing of a twisted orbital integral: if the integrals of `f` along a subgroup `U`, taken at
the points of the twisted orbit, all vanish, and some compactness conditions hold, then the
twisted orbital integral of `f` vanishes. The proof uses only the Weil formula of a compatible
quotient measure, Fubini's theorem on `U × G` and dominated convergence. It uses no
normalization of measures and no Iwasawa decomposition.

## Setting

`G` is a Hausdorff topological group with its Borel σ-algebra. The main theorem also assumes
that `G` is σ-compact and has a compact open subgroup `K` (an `OpenSubgroup G` with
`IsCompact K`). `θ` is a continuous endomorphism of `G`, given as any `FunLike` type with a
`MonoidHomClass` instance. For `δ ∈ G`, `H = twistedCentralizer θ δ = {t | t⁻¹ δ θ(t) = δ}` is
its twisted centralizer, and it is closed (the Library's `isClosed_twistedCentralizer`, module
`Langlands.BaseChange.RegularTransferMeasures`). The Library's
`twistedOrbitalIntegral θ δ ν f` (module `Langlands.TraceFormula.TwistedOrbital`) is the Bochner
integral of the orbit function `Hx ↦ f(x⁻¹ δ θ(x))` against a measure `ν` on the left coset
space `H \ G`. It is `0` when the orbit function is not `ν`-integrable. `IsCompatible H μG μH ν`
(module `Langlands.Analysis.Local.QuotientMeasure`) contains the Weil formula
`∫_{H\G} (∫_H φ(t x) dμH(t)) dν = ∫_G φ dμG` for continuous compactly supported `φ`, together
with the integrability of the `H`-averages.

## Main theorem

`twistedOrbitalIntegral_eq_zero_of_unipotent` assumes:

- `μG` is left-invariant and finite on compact sets;
- `μH` is right-invariant, finite on compact sets and positive on nonempty open sets, and
  `IsCompatible H μG μH ν`;
- `U` is a closed subgroup with a measure `μU` that is left-invariant, finite on compact sets
  and positive on nonempty open sets;
- `H` normalizes `U`: `t u t⁻¹ ∈ U` for `t ∈ H` and `u ∈ U`;
- for every compact `C ⊆ G` there is a compact `D` containing every `t ∈ H` with `t ∈ U C`;
- for every compact `C ⊆ G` there is a compact `D` containing every `u ∈ U` with
  `u⁻¹ δ θ(u) ∈ C` (the map `u ↦ u⁻¹ δ θ(u)` is proper on `U`);
- `f : G → ℂ` is continuous with compact support and
  `∫_U f(x⁻¹ (u⁻¹ δ θ(u)) θ(x)) dμU(u) = 0` for every `x ∈ G`.

Its conclusion is `twistedOrbitalIntegral θ δ ν f = 0`.

## Proof

1. *Locally constant functions.* A function on `G` that is invariant under right translation by
   an open subgroup is continuous (`continuous_of_forall_mul_mem_eq`).
2. *Fibre vanishing* (`integral_eq_zero_of_integral_subgroup_eq_zero`). Let `h` be continuous
   with compact support and `∫_U h(u x) dμU(u) = 0` for every `x`. Then `∫_G h dμG = 0`.
   Put `W = tsupport(h) K`, which is compact, open and right `K`-invariant, and
   `β = 1_W / m` with `m(x) = μU{u | u⁻¹ x ∈ W}` (`fibreMass`, `fibreCutoff`). Then `β` is
   continuous by step 1, and `∫_U β(u⁻¹ x) dμU(u) = 1` for `x ∈ W`, by left invariance of `μU`
   (`integral_fibreCutoff`). Hence
   `∫_G h = ∫_G ∫_U h(x) β(u⁻¹ x) = ∫_U ∫_G h(x) β(u⁻¹ x) = ∫_U ∫_G h(u y) β(y) = ∫_G β(y) ∫_U h(u y) = 0`.
   The two exchanges of integrals use Mathlib's `integral_integral_swap_of_hasCompactSupport`,
   applied to continuous compactly supported functions on `G × U`. The middle equality uses
   left invariance of `μG`.
3. *Cutoffs adapted to `H`* (`cosetMass`, `cosetCutoff`). For `W` compact, open and right
   `K`-invariant, put `α_W = 1_{U W} / c` with `c(x) = μH{t ∈ H | t x ∈ U W}`. The cutoff `α_W`
   is left `U`-invariant because `H` normalizes `U` (`cosetCutoff_subgroup_mul`), and it is
   continuous (`continuous_cosetCutoff`). Its `H`-average `∫_H α_W(t x) dμH(t)` is `1` if some
   `t ∈ H` has `t x ∈ U W` and `0` otherwise (`integral_cosetCutoff_of_exists`,
   `integral_cosetCutoff_of_not_exists`), so it has norm at most `1`
   (`norm_integral_cosetCutoff_le`). Finiteness of `c(x)` comes from the compactness condition
   on `H ∩ U C`, positivity from openness of `W`, and the invariance of `c` under `H` from right
   invariance of `μH`.
4. *Conclusion.* Put `W_j = compactCovering G j · K` and
   `h_j(x) = α_{W_j}(x) f(x⁻¹ δ θ(x))` (`orbitCutoffFunction`). Each `h_j` is continuous. It
   has compact support: if `h_j(x) ≠ 0` then `x = u w` with `u ∈ U`, `w ∈ W_j`, and
   `u⁻¹ δ θ(u) ∈ W_j · tsupport(f) · θ(W_j)⁻¹`, so `u` lies in the compact set given by
   properness. By left `U`-invariance of `α_{W_j}`,
   `∫_U h_j(u x) du = α_{W_j}(x) ∫_U f(x⁻¹ u⁻¹ δ θ(u) θ(x)) du = 0`, so `∫_G h_j dμG = 0` by
   step 2. The Weil formula gives `∫_{H\G} (∫_H h_j(t x) dμH(t)) dν = 0`, and the `H`-average
   of `h_j` at `Hx` equals `(∫_H α_{W_j}(t x) dμH(t)) · f(x⁻¹ δ θ(x))`, because the orbit
   function is constant on `H`-cosets. By step 3 these functions are bounded by the norm of
   the orbit function. They converge pointwise to the orbit function, since every `x` lies in
   `W_j` for large `j`. If the orbit function is `ν`-integrable, dominated convergence
   (`tendsto_integral_of_dominated_convergence`) gives
   `twistedOrbitalIntegral θ δ ν f = lim 0 = 0`. Otherwise the integral is `0` by definition.

## Origin

The criterion is derived for this Library. It is used to prove `CuspFormOrbitalVanishingStatement`
(module `Langlands.BaseChange.CuspFormOrbitalVanishing`), with `θ` the identity of `GL_n(F)`, `δ`
an element of a proper standard Levi subgroup and `U` the unipotent radical. Henniart–Lemaire
(*Changement de base et induction automorphe pour `GL_n` en caractéristique non nulle*,
Mém. SMF 124, 2011, II.4.5, formula (1), printed pp. 86–88, following Laumon, Prop. 4.4.9)
obtain this vanishing from the descent formula. That formula expresses the (σ-)orbital integral
at such a `δ` through the orbital integral on the Levi subgroup of the constant term
`φ_{P,σ}(m) = δ_P(m)^{1/2} ∫_{U × K} φ(k⁻¹ m u k^σ)`, which vanishes when all the integrals
along `U` vanish. The module keeps only what that argument needs for the vanishing: the integrals
of `f` along the `U`-cosets of the twisted orbit. These are integrated against the cutoffs
`α_W` and the Weil formula, so the descent formula itself and its normalizations of measures
are not needed.
