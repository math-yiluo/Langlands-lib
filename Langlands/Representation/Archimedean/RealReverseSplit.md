# The transpose of an intertwiner to the reversed standard module

Module `Langlands.Representation.Archimedean.RealReverseSplit`, namespace
`Langlands.Archimedean.RealReverseSplit`.

## Purpose and provenance

Let `ds` be a list of real blocks of rank `n` (module `StandardModule`) and
`T : K(ds) → K(ds.reverse)` an intertwiner, where
`K(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` is the space of
`O(n)`-finite functions of the real standard module. Write

`L w = twistLin n (T w)`, i.e. `(L w)(g) = (T w)(twist g)`, `twist g = w₀ (gᵀ)⁻¹`

(module `RealReverseTwist`). The main theorem `exists_splitTranspose` gives the split map `D`
of module `RealSplitFrobenius` together with two transpose identities, for every `f` and
every `w` respectively. These identities turn statements about the matrix coefficients of
`T w` into statements about matrix coefficients of the dual principal series of `ds` against
`w` and against `D f`.

This module is internal infrastructure for the reverse-intertwiner step of the proof of
`RealStandardIrreducibleCriterionStatement` (`RealReverseIntertwinerKernelStatement`, module
`RealStandardIrreducibleCriterionReduction`)
for lists with induction blocks. It has no literature source. For lists of characters only, the
transpose argument is in modules `RealReverseTransfer` and `RealCharacterReverseKernel`.
Here the position characters of `ds.reverse` are matched with those of `split ds` instead of
those of `ds`, and the split map `D` takes the difference into account. Three maps of
`GL_n(ℝ)` occur. The transpose `g ↦ gᵀ` (`transposeGL`) reverses products. The inverse
transpose `g ↦ (gᵀ)⁻¹` (`conjAut`) is a group automorphism. The twist `g ↦ w₀ (gᵀ)⁻¹` is the
inverse transpose followed by left multiplication by the antidiagonal permutation matrix `w₀`
(`twist`, module `RealReverseTwist`). For `n ≥ 2` it is not a group homomorphism, because
`twist 1 = w₀ ≠ 1` (`twist_one`). It is an involution, `twist (twist g) = g` (`twist_twist`), and satisfies
`twist (g h) = twist g · conjAut h` (`twist_mul`).

Notation: `Φ^p_j = blockFourierCoefficient n p j` is the `j`-th Fourier coefficient along the
rotations `blockRotation n p θ` in the coordinates `p, p + 1` (Library module
`RealBlockFourierFinite`). `realInducedBlockAt ds p` is the induction block of `ds` at the first
position `p`, if any (module `RealBlockPositionData`). `haarK n` is the Haar probability
measure of `O(n)`. All integrals `∫ … dκ` below are over `κ ∈ O(n)` with respect to `haarK n`.

## Statements

### Positions of the split list and of the reversed list

- `realRank_reverse`: `realRank ds.reverse = realRank ds`.
- `realRank_cons'`: `realRank (b :: ds) = realRank [b] + realRank ds`.
- `split_reverse_position P happ hbase`: let `P : List RealBlock → ℕ → α` satisfy the
  concatenation law
  `P (xs ++ ys) i = if i < realRank xs then P xs i else P ys (i - realRank xs)` and, for every
  block `b` and `l < realRank [b]`, `P (splitBlock b) l = P [b] (realRank [b] - 1 - l)`. Then
  `P (split ds) l = P ds.reverse (realRank ds - 1 - l)` for every `ds` and every
  `l < realRank ds`.
- `realPositionSign_splitBlock`, `realPositionExponent_splitBlock`: the base case for the
  position sign and the position exponent.
- `realPositionCharacter_split`: for `l < realRank ds`,
  `realPositionCharacter (split ds) l = realPositionCharacter ds.reverse (realRank ds - 1 - l)`.
  So the position characters of `split ds` are those of `ds.reverse` in the opposite order.
- `realPositionCharacter_inv_apply`:
  `realPositionCharacter ds l x⁻¹ = (realPositionCharacter ds l x)⁻¹`.
- `dualChar_reverse_eq hn` (with `hn : realRank ds = n`), for `j : Fin n`:
  `dualChar (realPositionCharacter ds.reverse) j z = realPositionCharacter (split ds) (rev j) z⁻¹`.
- `dualChar_split_eq hn`:
  `dualChar (realPositionCharacter (split ds)) j z = realPositionCharacter ds.reverse (rev j) z⁻¹`.

These are the hypotheses on characters of `twistLin_mem_kFiniteFunctions` (module
`RealReverseTwist`). With them, the twist carries `O(n)`-finite functions of the principal
series of `split ds` to those of the dual principal series of `ds.reverse`, and `O(n)`-finite
functions of the principal series of `ds.reverse` to those of the dual principal series of
`split ds`.

### Induction blocks of the reversed list

`realInducedBlockAt_reverse`: if `realInducedBlockAt ds p = some d`, then
`realInducedBlockAt ds.reverse (realRank ds - 2 - p) = some d`.

### Rotations and the twist

- `w0GL_mul_blockRotation hp` (for `p + 1 < n`):
  `w₀ · blockRotation n p θ = blockRotation n (n - 2 - p) (-θ) · w₀`.
- `twist_blockRotation_mul hp`:
  `twist (blockRotation n p θ · g) = blockRotation n (n - 2 - p) (-θ) · twist g`.
- `blockFourierCoefficient_twistLin hp j F g`:
  `Φ^p_j (twistLin n F) g = Φ^{n-2-p}_{-j} F (twist g)`.
- `twistLin_tail hn hF`: if `F ∈ realStandardModule n ds.reverse` and `realRank ds = n`, then
  for every induction block `d` of `ds` at position `p`, every `j` with `|j| < |d.weight|` and
  every `g`, `Φ^p_j (twistLin n F) g = 0`. So the twist of a function of the standard module of
  `ds.reverse` satisfies the Fourier condition of the induction blocks of `ds`.

### Transposes

`exists_transpose_of_section`. Let `D : K(split ds) →ₗ[ℂ] K(ds)` be an intertwiner
(`IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) (split ds) D`) and
`Q : K(ds) →ₗ[ℂ] K(split ds)` a linear map that commutes with the right translations by
`O(n)`, with `D (Q h) = h` for all `h`. Let `x` be an `O(n)`-finite function of
`principalSeries ℝ n (dualChar (realPositionCharacter (split ds)))` with `∫ x(κ) f(κ) dκ = 0`
whenever `D f = 0`. Then there is an `O(n)`-finite `z` of
`principalSeries ℝ n (dualChar (realPositionCharacter ds))` with

- `∫ z(κ) (D f)(κ) dκ = ∫ x(κ) f(κ) dκ` for all `f ∈ K(split ds)`, and
- `∫ x(κ g) f(κ) dκ = ∫ z(κ g) (D f)(κ) dκ` for all `f ∈ K(split ds)` and `g ∈ GL_n(ℝ)`.

`exists_transpose_twist hn T hT hf`. Let `realRank ds = n`, let `T : K(ds) →ₗ[ℂ] K(ds.reverse)`
be an intertwiner
(`IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse) ds T`),
and let `f` be an `O(n)`-finite function of
`principalSeries ℝ n (realPositionCharacter (split ds))`. Then there is an `O(n)`-finite `u` of
`principalSeries ℝ n (dualChar (realPositionCharacter ds))` with

`∫ u(κ g) w(κ) dκ = ∫ (twistLin n (T w))(κ gᵀ) f(κ) dκ` for all `w ∈ K(ds)` and all `g`.

Here `gᵀ` is `transposeGL g`.

### Main theorem

`exists_splitTranspose ds hn T hT`. Let `realRank ds = n` and `T : K(ds) →ₗ[ℂ] K(ds.reverse)`
an intertwiner as above, and write `L w = twistLin n (T w)`. There is a linear map
`D : K(split ds) →ₗ[ℂ] K(ds)` such that

1. `D` is an intertwiner:
   `IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) (split ds) D`;
2. `D` is surjective;
3. for every `w ∈ K(ds)`, `L w` is an `O(n)`-finite function of
   `principalSeries ℝ n (dualChar (realPositionCharacter (split ds)))`;
4. for every `f ∈ K(split ds)` there is an `O(n)`-finite `u` of
   `principalSeries ℝ n (dualChar (realPositionCharacter ds))` with
   `∫ u(κ g) w(κ) dκ = ∫ (L w)(κ gᵀ) f(κ) dκ` for all `w ∈ K(ds)` and all `g`;
5. for every `w ∈ K(ds)` there is an `O(n)`-finite `z` of
   `principalSeries ℝ n (dualChar (realPositionCharacter ds))` with
   `∫ z(κ) (D f)(κ) dκ = ∫ (L w)(κ) f(κ) dκ` for all `f ∈ K(split ds)`, and
   `∫ (L w)(κ g) f(κ) dκ = ∫ z(κ g) (D f)(κ) dκ` for all `f ∈ K(split ds)` and all `g`.

## Proofs

`split_reverse_position`. Induction on `ds`. For `b :: ds`, `split (b :: ds) = splitBlock b ++
split ds` and `(b :: ds).reverse = ds.reverse ++ [b]`. Apply the concatenation law on both
sides (`realRank_splitBlock`, `realRank_reverse`). If `l < realRank [b]`, the left side is
`P (splitBlock b) l` and the right side is
`P [b] (realRank [b] + realRank ds - 1 - l - realRank ds)`; conclude with `hbase`. Otherwise
the left side is `P (split ds) (l - realRank [b])` and the right side is
`P ds.reverse (realRank [b] + realRank ds - 1 - l)`; conclude with the induction hypothesis.
The index identities are `omega`.

`realPositionSign_splitBlock`, `realPositionExponent_splitBlock`: for a character block both
sides are the datum at position `0`. For `.induced e` the two positions are checked by `rfl`:
`lowChar e` has sign `0` and exponent `t - ℓ/2`, which are position `1` of `[.induced e]`, and
`highChar e` has sign `(ℓ + 1) mod 2` and exponent `t + ℓ/2`, which are position `0`
(module `RealSplitFrobenius`).

`realPositionCharacter_split`: rewrite both characters with `realPositionCharacter_eq_charFun`
and use `split_reverse_position` for `realPositionSign` and `GramFormula.realPositionExponent`, whose
concatenation laws are `realPositionSign_append` and `realPositionExponent_append`.

`realPositionCharacter_inv_apply`: `charFun` is multiplicative with `charFun 1 = 1`
(`charFun_mul`, `charFun_one`). `dualChar_reverse_eq` and `dualChar_split_eq` follow from
`realPositionCharacter_split` at the index `rev j` resp. `j`, using `Fin.val_rev` and `hn`.

`realInducedBlockAt_reverse`: induction on `ds` following the cases of `realInducedBlockAt`.
For a leading character block or an induction block at position `p + 2`, the block lies in
the initial segment `ds.reverse` of `(b :: ds).reverse = ds.reverse ++ [b]`
(`realInducedBlockAt_append_of_lt`, with `realInducedBlockAt_lt` for the bound) and the
induction hypothesis applies. For `.induced e` at position `0`, the block is the final segment
`[.induced e]` at position `realRank ds` (`realInducedBlockAt_append_of_le`).

`w0GL_mul_blockRotation`: first `w₀ r_p(θ) w₀ = r_{n-2-p}(-θ)`, by comparing entries
(`w0Mat_mul_mul_w0Mat_apply`, `blockRotation_apply`, `Fin.val_rev`; the cases are closed by
`omega` or `rfl`, using `sin(-θ) = -sin θ`, `cos(-θ) = cos θ`). Then multiply on the right by
`w₀` (`w0GL_mul_self`). `twist_blockRotation_mul`: `twist (r g) = twist r · conjAut g` and
`twist r = w₀ r` for `r ∈ O(n)` (`twist_mul`, `twist_of_mem`); then use
`w0GL_mul_blockRotation`.

`blockFourierCoefficient_twistLin`: by `blockFourierCoefficient_eq_coeff` both sides are
Fourier coefficients of periodic functions of `θ`. By `twist_blockRotation_mul` the function
`θ ↦ (twistLin n F)(r_p(θ) g)` is `θ ↦ F(r_{n-2-p}(-θ) twist g)`, and the `j`-th Fourier
coefficient of `θ ↦ φ(-θ)` is the `(-j)`-th coefficient of `φ` (`coeff_comp_neg`,
`periodic_blockRotation_mul`).

`twistLin_tail`: `realInducedBlockAt_lt` gives `p + 1 < n`. By
`blockFourierCoefficient_twistLin` the coefficient is `Φ^{n-2-p}_{-j} F (twist g)`. By
`realInducedBlockAt_reverse`, `d` is the induction block of `ds.reverse` at position
`n - 2 - p`. Since `|-j| = |j| < |d.weight|`, the Fourier condition in the definition of
`realStandardModule n ds.reverse` gives `0`.

`exists_transpose_of_section`. `exists_pairing_transpose_of_rep` (module
`RealReverseTransfer`), applied to `Q` and `x`, gives an `O(n)`-finite `z` of the dual principal
series of `ds` with `∫ z h = ∫ x (Q h)` for all `h ∈ K(ds)`. For `f ∈ K(split ds)`,
`D (f - Q (D f)) = 0`, so `∫ x (f - Q (D f)) = 0` by hypothesis, and
`∫ z (D f) = ∫ x (Q (D f)) = ∫ x f` (linearity of the integral; the integrands are products
of continuous functions on the compact group). This is the first identity. For the second,
`integral_mul_transfer` (module `RealReverseTransfer`, intertwiner `D`, `v = z`, `u = x`) at
`g⁻¹` gives `∫ (D f)(κ g⁻¹) z(κ) dκ = ∫ f(κ g⁻¹) x(κ) dκ`. Both sides are turned into the
claimed integrals by `integral_mul_inv_swap` for `ds` and for `split ds`.

`exists_transpose_twist`. By `twistLin_mem_kFiniteFunctions` and `dualChar_reverse_eq`,
`v = twistLin n f` is an `O(n)`-finite function of the dual principal series of `ds.reverse`.
`exists_pairing_transpose` gives `u` with `∫ u h = ∫ v (T h)` for all `h ∈ K(ds)`. Then for
`w ∈ K(ds)` and `g`:

- `∫ u(κ g) w(κ) dκ = ∫ w(κ g⁻¹) u(κ) dκ` (`integral_mul_inv_swap` for `ds`);
- `= ∫ (T w)(κ g⁻¹) v(κ) dκ` (`integral_mul_transfer` at `g⁻¹`);
- `= ∫ (T w)(twist(κ gᵀ)) f(κ) dκ` (`integral_mul_inv_eq_twist` with
  `twist (twist κ) = κ`).

`exists_splitTranspose`. Take `D` and `Q` from `RealSplitFrobenius.exists_splitMap ds hn`: `D`
is an intertwiner, `Q` commutes with `O(n)`, `D ∘ Q = id` (so `D` is surjective), and `D f = 0`
implies `∫ a f = 0` for every continuous `O(n)`-finite `a` whose block Fourier coefficients
`Φ^p_j a` vanish on `O(n)` for `|j| < |d.weight|` at every induction block `d` of `ds` at
position `p`. Item 3 is `twistLin_mem_kFiniteFunctions` with `dualChar_split_eq`, since `T w`
is an `O(n)`-finite function of the principal series of `ds.reverse`
(`mem_kFiniteFunctions_principalSeries`). Item 4 is `exists_transpose_twist`. Item 5 is
`exists_transpose_of_section` for `x = L w`: its kernel hypothesis is the kernel property of
`exists_splitMap`, whose Fourier condition holds by `twistLin_tail` because `T w` lies in
`realStandardModule n ds.reverse`.
