# Twisted orbital integrals that vanish along an abelian fibre

The module `Langlands.TraceFormula.TwistedOrbitalFibreVanishing` proves an abstract vanishing
criterion for the twisted orbital integrals `twistedOrbitalIntegral θ δ ν φ`
(`∫ φ(x⁻¹ δ θ(x)) dν(x)` over the left coset space of the twisted centralizer, module
`Langlands.TraceFormula.TwistedOrbital`): if `φ` integrates to zero along every translate of an
abelian subgroup `U` on which the twisted conjugation acts bijectively, the twisted orbital
integral of `φ` is zero. No measure is normalized.

## Setting

`G` is a group; `θ : G →* G`; `δ ∈ G`; `H = twistedCentralizer θ δ`. The structure
`TwistedFibreData θ δ` (for a topological group `G`) consists of

- a closed subgroup `U` that is commutative and satisfies `θ(U) ⊆ U`;
- a closed subgroup `P` with `δ ∈ P`, `U ≤ P` and `H ≤ P`;
- a continuous homomorphism `π : P →* G` with `π p = 1 ↔ p ∈ U` and `π h = h` for `h ∈ H`.

Algebraic consequences proved in the module: `P` normalizes `U` (`inv_mul_mul_mem`,
`mul_mul_inv_mem`); `H ∩ U = 1` (`eq_one_of_mem_U_of_mem_centralizer`); the twisted
conjugation `twist : U →* U`, `a ↦ δ⁻¹ a δ θ(a)⁻¹`, is a homomorphism (it uses that `U` is
commutative) and is injective (`twist_injective`: `twist a = 1` means `a ∈ H`). The subgroup
`S = π⁻¹(H)` of `P` (as a subgroup of `G`) equals `U H`, with the factorization
`prodHomeomorph : H × U ≃ₜ S`, `(h, a) ↦ a h`, inverse `s ↦ (π s, s π(s)⁻¹)`.

## Main theorem

`TwistedFibreData.twistedOrbitalIntegral_eq_zero`: let `G` be in addition Hausdorff, locally
compact and second countable with its Borel σ-algebra, let `θ` be continuous and let `twist` be
surjective. Let `φ : G → ℂ` be continuous with `∫_U φ(x a y) dμ(a) = 0` for every Haar measure
`μ` on `U` and all `x, y ∈ G`. Then for every Haar measure `μG` on `G`, every Haar measure `μH` on
`H` that is right invariant, and every quotient measure `ν` on `H \ G` with
`IsCompatible H μG μH ν`, `twistedOrbitalIntegral θ δ ν φ = 0`.

## Proof

1. *Topology.* `H` is closed (`isClosed_centralizer`), so is `S` (`isClosed_S`, the image of the
   closed set `π⁻¹(H)` under the closed embedding of `P`), and `twist` is continuous.
   `twistEquiv`: since `U` is closed in `G`, it is locally compact and second countable, so the
   continuous bijective homomorphism `twist` is open by Mathlib's
   `MonoidHom.isOpenMap_of_sigmaCompact` and is an isomorphism of topological groups.
2. *A right-invariant measure on `S`.* Let `μU` be a Haar measure on `U`.
   `isMulRightInvariant_map_prodHomeomorph`: the image `μS` of `μH × μU` under `(h, a) ↦ a h` is
   right invariant. For `s = a' h'`, right translation by `s` corresponds to
   `(h, a) ↦ (h h', a · h a' h⁻¹)`, which preserves `μH × μU` because `μH` is right invariant and
   `μU`, a left-invariant measure on the commutative group `U`, is invariant under translation by
   `h a' h⁻¹ ∈ U` (Mathlib's `MeasurePreserving.skew_product`). `μS` is finite on compacts and
   positive on open sets as an image under a homeomorphism.
3. *A normalizing function for `H`.* The Library's `exists_continuous_isNormalizingFunction`
   (module `Langlands.Analysis.Local.QuotientNormalizingFunction`) gives a continuous
   `ρ : G → ℝ≥0` with `∫_S ρ(s g) dμS(s) = 1` for all `g`. By Tonelli for `μH × μU`, the fibre
   average `ρ'(g) = ∫⁻_U ρ(a g) dμU(a)` satisfies `∫_H ρ'(h g) dμH(h) = 1`: it is a normalizing
   function for `H` (`IsNormalizingFunction`).
4. *Weil's formula.* With `Φ(x) = φ(x⁻¹ δ θ(x))`, left `H`-invariant, the Library's
   `IsCompatible.integral_descend_eq` gives
   `twistedOrbitalIntegral θ δ ν φ = ∫_G ρ'(g) Φ(g) dμG(g)`; `ρ'` is finite `μG`-almost
   everywhere by `IsNormalizingFunction.ae_lt_top`.
5. *Fubini along the fibre* (`integral_fibreAverage_smul_eq_zero`, for any subgroup `U`, s-finite
   `μU` and left-invariant `μG`): if `∫_U Φ(a⁻¹ g) dμU(a) = 0` for every `g`, then
   `∫_G ρ'(g) Φ(g) dμG(g) = 0`. If the integrand is not integrable the Bochner integral is `0`.
   Otherwise `K(a, g) = ρ(a g) Φ(g)` is integrable on `U × G`, its iterated integral in `a` first
   is `∫_G ρ'(g) Φ(g) dμG(g)`, and the shear `(a, g) ↦ (a, a⁻¹ g)` preserves `μU × μG` (left
   invariance of `μG`). After the shear the inner integral is `∫_U ρ(g) Φ(a⁻¹ g) dμU(a) = 0`.
6. *The inner integral.* `Φ(a⁻¹ g) = φ(g⁻¹ δ · twist(a) · θ(g))` for `a ∈ U`. Since `twistEquiv`
   is an isomorphism of topological groups, the image of `μU` under it is a Haar measure on `U`,
   so `∫_U φ(g⁻¹ δ · twist(a) · θ(g)) dμU(a) = ∫_U φ(g⁻¹ δ · b · θ(g)) d(twist_* μU)(b) = 0` by
   the hypothesis on `φ` with `x = g⁻¹ δ` and `y = θ(g)`.

## Provenance

The criterion is formulated for this Library. It isolates the fibre argument behind the
vanishing of (twisted) orbital integrals of cusp forms off the elliptic set (Henniart–Lemaire,
*Changement de base et induction automorphe pour `GL_n` en caractéristique non nulle*, Mém. SMF
124 (2011), II.4.5 (1), printed pp. 86–88, and II.5.14, printed pp. 115–116): there `U` is the
unipotent radical of a parabolic subgroup `P = M U`, `π` the projection onto the Levi factor `M`,
and the twisted centralizer of `δ ∈ M` lies in `M`. The proof does not use the descent formula
itself, the Iwasawa decomposition, or any normalization of Haar measures.
