# One compactly supported kernel reproducing a realized vector at every adelic point

Provenance: internal. This module supplies the archimedean "reproducing kernel" step in the
Harish-Chandra finiteness argument for cusp forms (compare Borel–Jacquet, *Automorphic forms
and automorphic representations*, Proc. Sympos. Pure Math. 33 (1979), §1–§4, and
Harish-Chandra, *Automorphic forms on semisimple Lie groups*, LNM 62, Theorem 1). A smooth
vector that is `K∞`-finite and `Z(𝔤)`-finite is reproduced by convolution with a smooth
compactly supported function on `GL_n(F ⊗ ℝ)`. The Library proves this for one function
(`ArchimedeanGL.exists_central_reproducingKernel`). Here it is extended to finitely many
functions at once, and then to all slices of one realized vector.

Throughout, `μ` is a Haar measure on the archimedean group `G∞ = InfiniteAdelicGL F n` and
`ev f` is the continuous adelic function of a realized vector `f`.

## Several functions at once (`ArchimedeanGL`)

- `exists_centralKernel_forall_mem μ f V hV`: let `f_j` (`j` in a finite index type) be smooth
  functions and let `V_j` be a neighborhood of `f_j`. Then one compact-central kernel `κ`
  gives `smoothingLM μ κ f_j ∈ V_j` for every `j`.

  Proof: this follows the Library proof of the one-function approximation
  (`ArchimedeanCompactCentralApproximationProof`). For each `j`,
  `CompactIndexAverage.exists_average_neighborhood` gives an identity neighborhood `W₀ j`:
  averages of right translates by points of `W₀ j` stay in `V_j`. Put
  `W := (⋂ j, W₀ j)⁻¹`. Choose a conjugation-saturated neighborhood `T ⊆ W`, a normalized
  nonnegative kernel supported in `T`, and its average over the standard compact subgroup.
  This average is central, nonnegative, supported in `W` and of total mass one, so it serves
  every `j` at once.
- `exists_centralKernel_forall_reproduce μ f hf hz`: if moreover every `f_j` is
  `K∞`-finite and center-finite, then one compact-central kernel `κ` gives
  `smoothingLM μ κ f_j = f_j` for every `j`.

  Proof: let `Φ κ := (smoothingLM μ κ f_j)_j`. Its range lies in the product of the ranges of
  the one-function maps, which are finite-dimensional (`finite_range_centralSmoothingMap`).
  So the range of `Φ` is finite-dimensional and therefore closed in the product. By the first
  item, `(f_j)_j` lies in its closure (`nhds_pi`, `Filter.mem_pi'`), hence in the range.

## Realized vectors (`OperatorRealization`)

- `ReproducesAt μ κ f g`: for all `h ∈ G∞`,
  `ev f (g · h) = ∫ ev f (g · z) κ(z⁻¹ h) dμ(z)`. Here `κ` is a complex function on `G∞` and
  `g` an adelic point. This is the condition used in `Finiteness.lean`.
- `evaluate_toContinuous_zero/_add/_smul`: `ev` is linear in `f`.
- Propagation lemmas:
  - `ReproducesAt.rational`: from `g` to `γ g` for rational `γ`, since `ev f` is left
    `GL_n(F)`-invariant.
  - `ReproducesAt.mul_ofFinite`: from `g` to `g l` when right translation by `l` fixes
    `ev f`. The finite and archimedean components commute.
  - `ReproducesAt.mul_ofInfinite`: from `g` to `g a` for archimedean `a`. Apply the identity
    at `a h` and substitute `z ↦ a z` (left invariance, `integral_mul_left_eq_self`).
  - `ReproducesAt.of_decomposition`: let `γ g = a q` and let right translation by `y⁻¹ q_f`
    fix `ev f`. Then the identity at the finite point `y` gives it at `g`. Combine the three
    previous lemmas.
  - `ReproducesAt.finiteRepresentation`: the identity at `g d` for `f` is the identity at
    `g` for the finite translate `π(d) f`.
- `reproducesAt_ofFinite κ f y hκ`: if `κ` reproduces the archimedean slice of `f` at the
  finite point `y`, then the identity holds at `y`. This rewrites
  `smoothingLM_eq_rawConvolution`.
- `exists_kernel_forall_mem S μ f t`: for a finite set `t` of finite adelic points, one
  smooth compactly supported kernel gives the identity at every `y ∈ t`. The slices are
  `K∞`-finite and center-finite (`slice_properties`), so `exists_centralKernel_forall_reproduce`
  applies.
- `exists_reproducingKernel S μ f`: there is one smooth compactly supported kernel `κ` such
  that `ReproducesAt μ κ f g` holds at every adelic point `g`.

  Proof: let `L` be an open compact level of `f` (`exists_level`). Use a Siegel decomposition
  `γ g = a q` with `q` in a compact set `Q₁` (`exists_siegelDecomposition`). Finitely many
  points `y ∈ t` have level cosets covering the finite parts of `Q₁`
  (`exists_finite_level_cover`). Take the kernel of the previous item for `t` and conclude
  with `ReproducesAt.of_decomposition`.
- `integrable_reproduce`: the integrand is integrable when `κ` is continuous with compact
  support and `μ` is finite on compacts.
- `reproducing S μ hκ hκc`: for continuous compactly supported `κ`, the realized vectors with
  `ReproducesAt μ κ f g` at every `g`. This is a subrepresentation of the finite adelic
  action. Linearity uses `integral_add` and `integral_const_mul`; stability under `π(d)` is
  `ReproducesAt.finiteRepresentation`. `mem_reproducing` unfolds membership.
