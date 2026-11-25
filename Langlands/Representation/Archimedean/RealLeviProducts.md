# Products over the classes of a block diagonal Levi subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviProducts`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It is
the second of three modules (`RealLeviSlices`, `RealLeviProducts`, `RealLeviDensity`) for the
density step of the single-shot Langlands-quotient argument. It states no `Prop`-valued statement
of its own. Its results are used by `RealLeviDensity`.

On the compact Levi subgroup `K_M = ∏_j O(sz_j)` (embedded block diagonally in `O(N)`) the
module shows:

1. every element of the global dual space is a finite sum of products of elements of the class
   dual spaces (`exists_isProdForm`);
2. iterated block Fourier coefficients along slots inside the blocks act factor by factor on such
   product forms (`coeffs_globalSlots`);
3. the free algebra of one class acts on the factors of that class (`isProdForm_lift`,
   `isProdForm_applyAll`).

No literature statement is claimed and nothing is cited; the provenance is internal ("derived").
Unprefixed names below are in the namespace `Langlands.Archimedean.RealLeviProducts`.

## Notation

As in `RealLeviSlices.md`: `start`, `pos`, `blockDiagGL`, `emb`, `embA`, `slice`, `repG`, `repC`,
`lieC`, `gensG`, `flat`, `sz`, `cl`, and `DualSpace`.

From the earlier modules `RealInducedBlockBound`, `RealInducedTorusCore`, `RealInducedTorusReduction`:
a `Slot N` records a block `p, p + 1` (with `p + 1 < N`), a covariance exponent
`α`, a weight `M`, a Fourier mode `j` and coordinates `x, y, w`. For a list `L` of slots,
`coeffs L F` is the iterated block Fourier coefficient
`Φ^{p_1}_{j_1} ⋯ Φ^{p_r}_{j_r} F`, where the Library's `blockFourierCoefficient N p j F g` is
`∫_0^{2π} F(r_p(θ) g) e^{-ijθ} dθ` with `r_p(θ) = blockRotation N p θ`, the rotation in the
coordinates `p, p + 1`. Only the fields `p` and `j` enter `coeffs`.

## Rotations inside a block

Section `Rotation`, sizes `sz : Fin c → ℕ`.

* `start_add_ne`: global positions of different classes differ. `start_add_lt`:
  `start_i + a < N` for `a < sz_i`.
* `blockRotation_start_add`: for `a + 1 < sz_i`,
  `blockRotation N (start_i + a) θ = emb sz i (blockRotation sz_i a θ)`. This is an entrywise
  comparison through `finSigmaFinEquiv` and the Library formula `blockRotation_apply`.
* `emb_mul_blockDiagGL`: `emb x · diag(κ) = diag(κ with x · κ_i in block i)`.

## Lifted slots and product coefficients

Section `Lift`.

* `liftSlot sz i s`: the slot `s` of `GL_{sz_i}` moved to the global position `start_i + s.p`
  (all other fields unchanged).
* `coeffs_liftSlots`: `coeffs (L.map (liftSlot i)) F (diag κ)` is the coefficient
  `coeffs L` of the slice `x ↦ F(diag(κ with x in block i))` at `κ_i`. Proof by induction on `L`:
  a rotation at a lifted position is `emb` of a block rotation (`blockRotation_start_add`), and
  `emb_mul_blockDiagGL` moves it into the block `i`.
* `coeffs_append`: `coeffs (A ++ B) F = coeffs A (coeffs B F)`.
* `coeffs_sum_mul`: `coeffs L (∑_a D_a f_a) = ∑_a D_a coeffs L f_a` for continuous `f_a`
  (linearity of the interval integral, Library `intervalIntegrable_blockFourier`).

Section `Prod`.

* `IsProdForm sz F C y` (for a finite index type `ι`, `C : ι → ℂ`,
  `y : ι → ∀ j, GL_{sz_j}(ℝ) → ℂ`): `F(diag κ) = ∑_a C_a ∏_j y_{a,j}(κ_j)` for every `κ` with
  `κ_j ∈ O(sz_j)` for all `j`.
* `prod_apply_update`, `update_mem_unitaryCompact`: bookkeeping for `Function.update`.
* `isProdForm_coeffs`: if `F` has product form with continuous factors, then
  `coeffs (L.map (liftSlot i)) F` has product form with the factors of the class `i` replaced by
  `coeffs L (y_{a,i})`. Proof: on `O(sz_i)` the slice of `F` through `κ` is
  `∑_a (C_a ∏_{j≠i} y_{a,j}(κ_j)) y_{a,i}`. Coefficients at `κ_i ∈ O(sz_i)` only depend on values
  on `O(sz_i)` (`coeffs_congr_of_eqOn` of `RealInducedTorusCore`), and `coeffs_sum_mul` applies.
* `globalSlots Ls l`: for class slot lists `Ls i : List (Slot sz_i)` and a list `l` of classes,
  the concatenation over `i ∈ l` of `(Ls i).map (liftSlot i)`.
* `isProdForm_globalSlots` (induction on a duplicate-free `l`, with `coeffs_append`) and
  **`coeffs_globalSlots`** (`l = finRange c`): for `F` of product form with continuous factors and
  `κ ∈ K_M`,
  `coeffs (globalSlots Ls (finRange c)) F (diag κ) = ∑_a C_a ∏_j coeffs (Ls j) (y_{a,j}) (κ_j)`.

## Spans of products

Section `Dec`.

* `exists_interp`: a finite-dimensional space `W` of functions `α → ℂ` has an interpolation
  formula `v = ∑_g v(x_g) f_g` for all `v ∈ W`, with finitely many points `x_g` and `f_g ∈ W`.
  Proof: extend the coordinate functionals of a basis of `W` to all functions
  (`LinearMap.exists_extend`). By the Library `exists_sum_of_separating` (evaluations separate
  `W`) each one agrees on `W` with a finite combination of evaluations.
* `prodSpan W`: for spaces `W_j` of functions on `α_j`, the span of the functions
  `κ ↦ ∏_j f_j(κ_j)` on `∏_j α_j` with `f_j ∈ W_j`. `consMul_mem`: if `h ∈ W_0` and
  `G ∈ prodSpan (W_{j+1})_j`, then `κ ↦ h(κ_0) G(tail κ)` lies in `prodSpan W`.
* **`mem_prodSpan`**: if every `W_j` is finite-dimensional and every coordinate slice
  `x ↦ F(κ with x at j)` of `F` lies in `W_j`, then `F ∈ prodSpan W`. Proof by induction on `c`:
  the interpolation formula of `W_0` applied to the slice at `0` gives
  `F(κ) = ∑_g f_g(κ_0) F(x_g, tail κ)`. Each `F(x_g, ·)` satisfies the hypothesis for the
  remaining coordinates (`Fin.cons_update`).

## Product form of the dual space

Section `App`, `dss : Fin c → List RealBlock`.

* `mK hκ i ∈ O(N)`: the element `diag(κ with 1 in block i)` for `κ ∈ K_M`, with `toUnits_mK`.
* `apply_blockDiagGL_update`: `u(diag(κ with x in block i)) = slice i (repG (mK hκ i) u) (x)`.
* `resK n V`: restriction of functions on `GL_n(ℝ)` to `O(n)`.
* **`exists_isProdForm`**: every `u ∈ DualSpace N (flat dss)` satisfies
  `IsProdForm (sz dss) u C (w_{a,j})` for some `n`, `C : Fin n → ℂ` and
  `w_{a,j} ∈ DualSpace sz_j (cl dss j)`. Proof: the `O(N)`-orbit span `O` of `u` is
  finite-dimensional (Library `kFiniteRep_isFiniteVector`). Let `W_j` be the image of `O` under
  `resK ∘ slice j`. By `apply_blockDiagGL_update` every coordinate slice of
  `F(κ) = u(diag κ)` on `K_M` is the restriction of `slice j (repG (mK) u)` with
  `repG (mK) u ∈ O`. Then `mem_prodSpan` writes `F` as a finite combination of products, and
  `Submodule.mem_span_set'` gives the finite sum.

## Acting in one class

Section `Step`.

* `Gens dss i`: the generator type `O(sz_i) ⊕ (ℂ ⊗ 𝔤𝔩_{sz_i}(ℝ))` of the class `i`.
* `slice_repG_eq_sum`: if `u` has product form with factors `w_{a,j}`, then
  `slice i (repG (mK hκ i) u) = ∑_a (C_a ∏_{j≠i} w_{a,j}(κ_j)) • w_{a,i}`. Both sides lie in the
  class principal series and agree on `O(sz_i)`, so they are equal (Library
  `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`).
* **`isProdForm_lift`**: for `b` in the free algebra on `Gens dss i`, `lift (gensG dss i) b u` has
  product form with the factors of the class `i` replaced by
  `lift (gens (repC i) (lieC i)) b (w_{a,i})`. Proof: by `apply_blockDiagGL_update` the value at
  `diag κ` is the slice at `κ_i` of `repG (mK) (lift b u)`. Then `repG_comm_lift` and
  `slice_lift` move the free algebra element to the class side, and `slice_repG_eq_sum` gives the
  sum.
* `applyAll b l u`: apply `b_i` (through `gensG dss i`) for every class `i` of the list `l`.
* `isProdForm_applyAll`: for duplicate-free `l` the factors of every class `j ∈ l` are replaced by
  `lift (gens (repC j) (lieC j)) (b j) (w_{a,j})`.
* `applyAll_mem`: a submodule stable under every `gensG dss i x` is stable under `applyAll b l`
  (`lift_mem`).
