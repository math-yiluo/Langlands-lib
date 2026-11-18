# Intertwiners to the reversed standard module along the tie classes

Module `Langlands.Representation.Archimedean.RealReverseInduced`, namespace
`Langlands.Archimedean.RealReverseInduced`.

## Purpose and provenance

Let `ds = dss_0 ++ ⋯ ++ dss_{c-1}` (`flat dss`) be a list of real blocks split into `c` classes
of ranks `sz_i = realRank (dss i)` (`sz dss i`), `N = ∑_i sz_i`. Let `Q` be the standard
parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of sizes `sz_i`. The main theorem
`reverseKernel` states: if the hypotheses of `RealLeviLimitStatement` hold for `ds` and `Q` and
every class standard module is irreducible, then every `(𝔤, K)`-intertwiner `T` from the
`O(N)`-finite standard module of `ds` to that of `ds.reverse` vanishes on every proper
`(𝔤, K)`-submodule.

This is internal infrastructure for the reverse-intertwiner step of Task 7069
(`RealReverseIntertwinerKernelStatement`, module `RealStandardIrreducibleCriterionReduction`) for
lists with induction blocks. For lists of characters only, the same step is proved in the
Library module `RealCharacterReverseKernel` (conditional on `RealBlockChartIntegrableStatement`,
`RealBlockParabolicIntegrationStatement` and `RealTemperedStandardIrreducibleStatement`). That
proof is a recursion over the tie classes of the exponents, starting from the last class
(`RealReverseRecursion.jac_eq_zero_of_transpose`, applied in
`RealCharacterReverseKernel.exists_testVector` to the tie-class sizes from
`RealCharacterLanglandsQuotient.exists_blocks`). Each step removes the whole last tie class, of
size `k + 1`. It uses the block Jacquet functional of `RealBlockFunctional` and the limit along
the block parabolic subgroup with diagonal blocks of sizes `N − k − 1` and `k + 1`
(`RealBlockLimitValue.exists_tendsto`, scaling by `diag(1_{N−k−1}, s·1_{k+1})`). The
construction here is not recursive. It uses one torus-averaged limit pairing `Θ` along the
parabolic subgroup `Q` of all tie classes at once (Library modules `RealLeviLimit`,
`RealLeviPairing`, `RealLeviWitness`, Worker 5220, Task 6749). The induction blocks are handled
by the split transpose of `RealReverseSplit.exists_splitTranspose` (with `RealSplitFrobenius`):
a surjective intertwiner `D : X(split ds) → X(ds)` such that the twisted images
`twistLin N (T w)` lie in the dual principal series `Y(split ds)` of the character list
`split ds`, with the transpose identities stated in the proof of `reverseKernel` below.

Provenance: derived. No literature statement is claimed. The method is the matrix-coefficient
asymptotics used to identify the Langlands quotient (compare Knapp, *Representation theory of
semisimple groups*, 1986, Ch. VIII), worked out here for the parabolic subgroup `Q`. Two inputs
are imported from Worker 5220's Library modules: the dependence of `Θ` on the allowed
coefficients only (`RealLeviPairing.theta_congr`) and the nonvanishing of `Θ` for the data of the
classes (`realLeviWitness`, module `RealLeviWitness`).

The results are conditional on two inputs, passed as hypotheses and not proved here:

- `RealLeviChartIntegrableStatement` (`hT1`, module `RealLeviChartIntegralStatement`; proved in the
  Library as `realLeviChartIntegrable`, module `RealLeviChartIntegrable`, which this module does not
  import);
- `RealLeviParabolicIntegrationStatement` (`hT3`, module `RealLeviParabolicIntegrationStatement`).

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is `unitaryCompact ℝ N` with Haar probability
measure `haarK N`. All integrals `∫ … dκ` without further mention are over `κ ∈ O(N)` with respect
to `haarK N`. For a list `ds` of real blocks of rank `N`:

- `X(ds) = StdSpace N ds = kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)`;
- `Y(ds) = DualSpace N ds`, the `O(N)`-finite functions of
  `principalSeries ℝ N (dualChar (realPositionCharacter ds))`;
- `⟨z, h⟩ = ∫ z(κ) h(κ) dκ` for `z ∈ Y(ds)`, `h ∈ X(ds)`.

From `RealLeviLimit` and `RealLeviSlices`: `cls sz p` is the block of the position `p`,
`Coord sz` are the coordinates of `N̄_Q`, `n̄(X) = lowerGL sz X`, `K_M = ∏_i O(sz_i)` with
measure `Measure.pi (fun i => haarK (sz i))` and `diag(κ) = bdK sz κ`, `d_s = scaleGL sz hs` for
`s > 0`. From `RealLeviModes` and `RealInducedTorusCore`: `slots ds N` lists the slots (positions
of the induction blocks), each with a weight `M`. `withModes S J` sets the modes of the slot list
`S` to the entries of `J`, and `coeffs L F` is the iterated Fourier coefficient of `F` along the
slots of `L` (with their modes). `c_Z(F) = coeffs (zeroModes (slots ds N)) F 1` takes all modes
`0`. A mode list `J` of length `|S|` is **jointly allowed** for `S` if `M ≤ |j|` at every slot of
`withModes S J`. For classes, `cl dss i = twist (shift dss i) (dss i)` is the twisted class list
of `RealLeviSlices`, with `shift dss i = start_i − (N − sz_i)/2`, where `start_i` is the first
position of the `i`-th diagonal block. On the positions of the `i`-th diagonal block, the raw
position characters of `flat dss` are those of the untwisted class `dss i`
(`RealLeviSlices.realPositionCharacter_flat`), not those of `cl dss i`. The twist compensates for
the difference between the half-modulus of the upper triangular Borel subgroup of `GL_N(ℝ)` and
that of `GL_{sz_i}(ℝ)`. The two normalized inducing characters, which include these half-moduli
(`principalSeriesCharacter`), agree on the torus of the `i`-th diagonal block:
`RealLeviSlices.principalSeriesCharacter_pad` says that the normalized inducing character of
`dualChar (realPositionCharacter (flat dss))` at a diagonal element supported in the `i`-th block
(entries `1` elsewhere) equals that of `dualChar (realPositionCharacter (cl dss i))` at the
block's entries. Consequently, restricting a function of `Y(flat dss)` to the `i`-th diagonal
block gives a function of `Y(cl dss i)` (`RealLeviSlices.slice_mem`). For example, take two
rank-one classes, with sign-trivial characters of exponents `0` and `−1`. On the first position
the global raw dual character is `1`. The first class has shift `0 − (2 − 1)/2 = −1/2`, and the
raw dual character of `cl dss 0` is `a ↦ |a|^{1/2}`. The half-modulus factor `|a|^{1/2}` of
`GL_2(ℝ)` at that position restores the equality of the normalized characters.
The global slot list `slots (flat dss) N` matches
the concatenation of the lifted class slot lists, so mode families `Js : Fin c → List ℤ` give
global mode lists `(List.ofFn Js).flatten` (`RealLeviDensity`).

## Statements

### The limit pairing (Library)

The limit pairing is `RealLeviPairing.theta (slots ds N) u h` (Library module `RealLeviPairing`),
for `u h : GL_N(ℝ) → ℂ`, `N = ∑_i sz_i`:

`Θ(u, h) = ∫_{K_M} ∫_{Coord sz → ℝ} c_Z(x ↦ u(x diag(κ)) · h(x n̄(X) diag(κ))) dX dκ`.

Up to unfolding this definition, it is the limit in `RealLeviLimitStatement` (`RealLeviLimit`)
and in `RealParabolicLimitValue.integral_coeffs_eq_of_eq`. This module uses two Library results
about it:

- `RealLeviPairing.theta_congr hu hu' hh hJ`: let `u, u'` be `O(N)`-finite functions of
  `principalSeries ℝ N (dualChar (realPositionCharacter ds))` and `h ∈ X(ds)`. If
  `coeffs (withModes (slots ds N) J) u (diag κ) = coeffs (withModes (slots ds N) J) u' (diag κ)`
  for every jointly allowed `J` of length `|slots ds N|` and every `κ ∈ K_M`, then
  `Θ(u, h) = Θ(u', h)`.
- `realLeviWitness hT1 c dss hanti hstrict hX` (module `RealLeviWitness`): under `hT1`, the
  exponent conditions `hanti`, `hstrict` for `flat dss` and the class sizes, and irreducibility
  of every class standard module (`hX`), there are `φ_i`, each an `O(sz_i)`-finite function of
  `principalSeries ℝ sz_i (dualChar (realPositionCharacter (cl dss i)))`, and
  `h_0 ∈ X(flat dss)`, such that `Θ(u, h_0) ≠ 0` for every `O(N)`-finite `u` of
  `principalSeries ℝ N (dualChar (realPositionCharacter (flat dss)))` whose coefficients along
  the global mode lists `(List.ofFn Js).flatten` at `blockDiagGL sz κ` are the products
  `∏_i coeffs (withModes (slots (cl dss i) sz_i) (Js i)) φ_i (κ_i)`, for every family `Js` with
  `(Js i).length = |slots (cl dss i) sz_i|` that is jointly allowed for every class, and every
  `κ` with `κ_i ∈ O(sz_i)` (*product coefficients of `⊗_i φ_i`*). (Its statement writes `Θ` as
  the explicit double integral.)

### Matrix coefficients from pairings

- `integral_mul_eq_of_forall W' hWK hWL hu hz huz hw g`: let `W'` be a subspace of `X(ds)`
  (`realRank ds` need not be `n` here; `X`, `Y` are taken in `GL_n(ℝ)`) stable under
  `realStandardRep n ds k` for `k ∈ O(n)` (`hWK`) and under `realStandardLie n ds` (`hWL`). Let
  `u, z` be `O(n)`-finite functions of `principalSeries ℝ n (dualChar (realPositionCharacter ds))`
  with `∫ u(κ) w(κ) dκ = ∫ z(κ) w(κ) dκ` for every `w ∈ W'` (`huz`). Then for every `w ∈ W'` and
  every `g ∈ GL_n(ℝ)`:

  `∫ u(κ g) w(κ) dκ = ∫ z(κ g) w(κ) dκ`.

### Values of the limit pairing

In this section `ds` satisfies the hypotheses of `RealLeviLimitStatement`: `realRank ds = N`
(`hN`), and with `t_p = realPositionBlockExponent ds p`, `t_q ≤ t_p` for `p ≤ q` (`hanti`) and
`t_q < t_p` when `cls sz p < cls sz q` (`hstrict`).

- `theta_eq_of_pairing hT1 hT3 hN hanti hstrict hu hz huz h`: let `u, z` be `O(N)`-finite
  functions of the dual principal series as above with `⟨u, w⟩ = ⟨z, w⟩` for every `w ∈ X(ds)`.
  Then `Θ(u, h) = Θ(z, h)` for every `h ∈ X(ds)`.
- `theta_eq_zero hT1 hT3 hN hanti hstrict hu hh h0`: if `u` is as above, `h ∈ X(ds)`, and
  `∫ u(κ g) h(κ) dκ = 0` for every `g ∈ GL_N(ℝ)`, then `Θ(u, h) = 0`. (This restates
  `RealLeviLimit.integral_coeffs_eq_zero` with `RealLeviPairing.theta`.)
- `transposeGL_scaleGL hs`: `d_sᵀ = d_s`.

### Vanishing on proper submodules

Here `ds = flat dss`, `N = ∑_j sz_j`, and `hanti`, `hstrict` are the hypotheses above for
`flat dss` and the class sizes; `hN` holds by `realRank_flat`.

- `coeffs_eq_of_split h`: if the coefficients of `u` and `u'` agree at every `diag κ`
  (`κ ∈ K_M`) along the global mode lists `(List.ofFn Js).flatten`, for every family `Js` with
  `(Js i).length = |slots (cl dss i) sz_i|` that is jointly allowed for every class
  (`slots (cl dss i) sz_i`), then they agree along every jointly allowed `J` for
  `slots (flat dss) N`. This turns the coefficients supplied by
  `RealLeviDensity.exists_density` into the hypothesis of `RealLeviPairing.theta_congr`.
- `theta_eq_zero_of_mem hT1 hT3 hanti hstrict hX W hWK hWL hW hy x` (**vanishing on proper
  submodules**): assume every class standard module is irreducible:
  `IsIrreducibleGKModule (realStandardRep sz_i (cl dss i)) (realStandardLie sz_i (cl dss i))`
  for all `i` (`hX`). Let `W ≠ ⊤` be a subspace of `X(flat dss)` stable under
  `realStandardRep N (flat dss) k` (`k ∈ O(N)`) and `realStandardLie N (flat dss)`. Then
  `Θ(x, y) = 0` for every `y ∈ W` and every `x ∈ Y(flat dss)`.

### Intertwiners to the reversed module

- `isCharacterList_split ds`: `split ds` (module `RealSplitFrobenius`: every induction block
  replaced by its two characters) is a list of characters.
- `dualChar_dualChar χ`: `dualChar (dualChar χ) = χ`.
- `reverseKernel hT1 hT3 hanti hstrict hX T hT W hW hWne` (**main theorem**): with `hanti`,
  `hstrict` for `flat dss` and the class sizes and irreducible class standard modules (`hX`), let
  `T : X(flat dss) →ₗ[ℂ] X((flat dss).reverse)` (both in `GL_N(ℝ)`) be a `(𝔤, K)`-intertwiner
  (`IsRealStandardIntertwiner N (realStandardRep N (flat dss).reverse)
  (realStandardLie N (flat dss).reverse) (flat dss) T`), and `W` a `(𝔤, K)`-submodule of
  `X(flat dss)` (`IsGKSubmodule`) with `W ≠ ⊤`. Then `W ≤ ker T`.

## Proofs

`integral_mul_eq_of_forall`. Apply `RealReverseTransfer.matrixCoefficient_eq_of_rel` with `μ` the
image of `haarK n` on the unitary group, both characters equal to `realPositionCharacter ds`
(a signed power, `isSignedPower ds`), the relation `P a b :⇔ ∃ w' ∈ W', a = w' ∧ b = w'`, and the
test functions `u` and `z` restricted to the unitary group. `P` is stable under `R(k)`
(`hWK`) and right derivatives (`hWL`, `realStandardLie_one_tmul_apply_coe`). At `g = 1` the two
matrix coefficients are `∫ w'(κ) u(κ) dκ` and `∫ w'(κ) z(κ) dκ`, equal by `huz`. So
`∫ w(κ g⁻¹) u(κ) dκ = ∫ w(κ g⁻¹) z(κ) dκ` (matrix coefficients as integrals by
`integral_map_toUnitaryGroup`). Finally `∫ u(κ g) w(κ) dκ = ∫ w(κ g⁻¹) u(κ) dκ`
(`RealReverseTransfer.integral_mul_inv_swap`, `w` lies in the principal series by
`realStandardModule_le_principalSeries`), and the same for `z`.

`theta_eq_of_pairing`. By the value form `RealParabolicLimitValue.integral_coeffs_eq_of_eq` (with
`h' = h`), it suffices that `∫ u(κ d_s) h(κ) dκ = ∫ z(κ d_s) h(κ) dκ` for every `s > 0`. This is
`integral_mul_eq_of_forall` with `W' = ⊤`.

`theta_eq_zero` is `RealLeviLimit.integral_coeffs_eq_zero`. `transposeGL_scaleGL`: `d_s` is
diagonal (`Matrix.diagonal_transpose`).

`coeffs_eq_of_split`. A jointly allowed `J` of length `|slots (flat dss) N|`
(`length_slots_flat`) is `(List.ofFn Js).flatten` for a family `Js` of per-class lengths
(`RealLeviDensity.exists_split`). The lifted class slots with modes `Js` have the same keys as
`withModes (slots (flat dss) N) J` (`map_key3_flat`), so `Js` is jointly allowed for every class
(`allowed_of_map_key3`, `liftSlot_mem_globalSlots`), and the hypothesis applies.

`theta_eq_zero_of_mem`. By `RealLeviProducts.exists_isProdForm`, `x` has product form on `K_M`:
`x(diag κ) = Σ_a C_a ∏_j w_{a,j}(κ_j)` with `w_{a,j} ∈ Y(cl dss j)`. For each `a`,
`RealLeviDensity.exists_density` (with `hX`, `W`, and the family `φ_j = w_{a,j}`) gives
`u_a ∈ annW W` (so `⟨u_a, w⟩ = 0` for `w ∈ W`) whose jointly allowed coefficients along the
lifted class slots at `diag κ` are `∏_j coeffs (w_{a,j}) (κ_j)`. Put `x' = Σ_a C_a u_a ∈ annW W`.

- `Θ(x, y) = Θ(x', y)`: by `RealLeviPairing.theta_congr` and `coeffs_eq_of_split`. For a family
  `Js` jointly allowed per class, the coefficient of `x` along the global modes at `diag κ`
  equals the coefficient along the lifted class slots (`coeffs_congr_key3`, `map_key3_flat`). By
  the product form this is `Σ_a C_a ∏_j coeffs (w_{a,j}) (κ_j)` (`coeffs_globalSlots`). The
  coefficient of `x'` is `Σ_a C_a` times the coefficient of `u_a` (`coeffs_sum_mul`), which is
  the same sum.
- `Θ(x', y) = 0`: `x'` and `0` have the same pairings with the `(𝔤, K)`-stable `W`, so
  `integral_mul_eq_of_forall` (with `z = 0`, `W' = W`, `w = y`) gives `∫ x'(κ g) y(κ) dκ = 0` for
  every `g`. Then apply `theta_eq_zero`.

`reverseKernel`. Write `ds = flat dss` and `L w = twistLin N (T w)` (module `RealReverseTwist`).
`exists_splitTranspose` (module `RealReverseSplit`) gives a surjective intertwiner
`D : X(split ds) → X(ds)` with `L w ∈ Y(split ds)` for every `w`. It also gives, for every `f`, a
`u_f ∈ Y(ds)` with `∫ u_f(κ g) w(κ) dκ = ∫ (L w)(κ gᵀ) f(κ) dκ` for all `w, g` (property U). And
for every `w`, it gives a `z_w ∈ Y(ds)` with `⟨z_w, D f⟩ = ⟨L w, f⟩` and
`∫ (L w)(κ g) f(κ) dκ = ∫ z_w(κ g) (D f)(κ) dκ` for all `f, g` (property Z).

1. *The subspace `V`.* Let `V ⊆ Y(ds)` be the set of `z` for which some `w ∈ W` satisfies
   `⟨z, D f⟩ = ⟨L w, f⟩` for every `f ∈ X(split ds)`. In Lean `V` is the preimage
   (`Submodule.comap`) under `z ↦ ⟨z, D ·⟩` of the image (`Submodule.map`) of `W` under
   `w ↦ ⟨L w, ·⟩`, built from `intPairing` (`RealReverseTransfer`), so it is a subspace.
   (`hmemV` unfolds membership.)
2. *`V` is a `(𝔤, K)`-submodule.* `O(N)`: if `z ∈ V` via `w`, then `k · z ∈ V` via
   `k · w ∈ W`. Apply the defining identity at `k⁻¹ · f` and use the intertwining properties of `D`
   and `T`, `twistLin` commuting with right translation by `O(N)`
   (`RealReverseTwist.rightTranslation_twistLin`), and right invariance of Haar measure
   (`integral_translate_mul`). Lie algebra: for a real matrix `Y0`, `R_{Y0} z ∈ V` via
   `realStandardLie (−Y0ᵀ) w`. Here `L` turns this into `R_{Y0} (L w)`
   (`RealReverseTwist.rightDerivative_twistLin`), and the two integration-by-parts identities
   `integral_rightDerivative_mul_add` (module `RealPairingAnnihilator`) for `(z, D f)` and
   `(L w, f)` combine. General elements of `ℂ ⊗ 𝔤𝔩_N(ℝ)` follow by `TensorProduct.inductionOn`.
   Hence `perp ds V` is a `(𝔤, K)`-submodule of `X(ds)` (`isGKSubmodule_perp`).
3. *`Θ(z, h) = 0` for every `z ∈ V` and `h ∈ X(ds)`.* Let `z ∈ V` via `w ∈ W`, and write
   `h = D f` (`D` onto). Take `z_w` from property Z. Since `D` is onto, `z` and `z_w` have the
   same pairings with `X(ds)`, so `Θ(z, D f) = Θ(z_w, D f)` (`theta_eq_of_pairing`). Take `u_f`
   from property U. At `g = d_s = d_sᵀ` (`transposeGL_scaleGL`), the two properties give
   `∫ u_f(κ d_s) w(κ) dκ = ∫ z_w(κ d_s) (D f)(κ) dκ`. The value form
   `integral_coeffs_eq_of_eq` then gives `Θ(u_f, w) = Θ(z_w, D f)`. Finally `Θ(u_f, w) = 0` by
   `theta_eq_zero_of_mem`, since `w` lies in the proper submodule `W`.
4. *`perp ds V = ⊤`.* Otherwise `perp ds V` is a proper `(𝔤, K)`-submodule. Take `φ`, `h_0` from
   `realLeviWitness hT1 c dss hanti hstrict hX`. `exists_density` (with `hX`, `W := perp ds V`,
   and the family `φ`) gives `u ∈ annW (perp ds V)` with the product coefficients of `⊗_i φ_i`,
   so `Θ(u, h_0) ≠ 0`. Since `V` is `O(N)`-stable and `u` vanishes on `perp ds V`,
   `exists_eq_of_vanishing` gives `z ∈ V` with the same pairings as `u` on `X(ds)`. Then
   `Θ(u, h_0) = Θ(z, h_0)` (`theta_eq_of_pairing`), which is `0` by step 3, a contradiction.
5. *Conclusion.* Let `w ∈ W` and take `z_w` from property Z. Then `z_w ∈ V` via `w`. For every
   `f`, `⟨L w, f⟩ = ⟨z_w, D f⟩ = 0`, because `D f ∈ perp ds V = X(ds)` (`mem_perp`). The function
   `L w` is an `O(N)`-finite element of the principal series of
   `dualChar (realPositionCharacter (split ds))`. Since `split ds` is a list of characters
   (`isCharacterList_split`), the `O(N)`-finite standard module of `split ds` is the `O(N)`-finite
   principal series (`realStandardModule_eq`). If `L w ≠ 0`,
   `RealReverseTransfer.exists_integral_mul_ne_zero` (for the dual signed power, with
   `dualChar_dualChar`) gives an `f` with `⟨L w, f⟩ ≠ 0`, a contradiction. So `L w = 0`, and
   `T w = twistLin (L w) = 0` because `twistLin` is an involution
   (`RealReverseTwist.twistLin_twistLin`).
