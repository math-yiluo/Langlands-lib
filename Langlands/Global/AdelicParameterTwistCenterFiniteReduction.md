# Center finiteness of twists from the finite Harish-Chandra transfer: proof

Module `Langlands.Global.AdelicParameterTwistCenterFiniteReduction`. Its main theorem
`Langlands.Global.parameterTwistCenterFiniteReduction` proves
`ParameterTwistCenterFiniteReductionStatement`: `ParabolicLeviCenterRestrictionStatement`
implies `ParameterTwistCenterFiniteStatement`.

## Auxiliary lemmas

For a closed subgroup `p : P → G`, a compact `K` with `P(𝔸) K = G(𝔸)` and its Iwasawa height,
with `m_P(g)^λ = hK.heightPower lam g`:

- `IsIwasawaCompact.heightPower_one`: `m_P(1)^λ = 1`;
- `IsIwasawaCompact.heightPower_pair`: for a maximal compact `K`,
  `m_P((a, b))^λ = m_P((a, 1))^λ m_P((1, b))^λ` (from `height_pair_of_maximal`);
- `IsIwasawaCompact.isLeftInvariantUnder_unipotentImage_parameterTwist`: if `φ` is left
  invariant under the image of `V(𝔸)` for a unipotent `V → P`, so is `φ_λ`
  (from `heightPower_unipotent_mul`);
- `functionInfiniteSlice_unipotent_mul`: the infinite slices `a ↦ φ(a, b)` of such a `φ` are
  left invariant under the image of `V(F_∞)`, because `(v, 1)` lies in the image of `V(𝔸)`
  (`map_ofInfinite`).

## The proof of the implication

Fix the data of `ParameterTwistCenterFiniteStatement`. Write `P`, `M`, `U` for `fam.P I`,
`fam.M I`, `fam.U I`, and `𝔷`, `𝔷_M` for the centers of the complex enveloping algebras of
`G(F_∞)` and `M(F_∞)`. Let `φ` be smooth, left invariant under `U(𝔸)`, with every infinite
slice killed by an ideal `J` of `𝔷` of finite codimension, and let `λ` be given.

1. *The finite transfer.* The family supplies connected reductivity of `G`, the parabolic, the
   geometric unipotent radical and the rational Levi. Multiplication `M × U → P` is an
   isomorphism by `IsRationalLeviSubgroup.isIso_subgroupMultiplication_of_radical`. The smooth
   structure of `M` is `fam.leviSmooth I`, and its commutator datum is
   `adelicDifferentialCommutator_of_smooth`. The premise at the translate `a = 1` gives a finite
   algebra homomorphism `p : 𝔷 → 𝔷_M` compatible with Levi restriction of left
   `U(F_∞)`-invariant functions. The Library's `exists_cofinite_center_ideal_of_leviRestriction`
   gives an ideal `I_M` of `𝔷_M` of finite codimension. `I_M` kills the Levi restriction
   `m ↦ f(l(m))` of every such `f` killed by `J`.
2. *The character of the Levi.* Put `h(x) = m_P((x, 1))^λ` on `G(F_∞)` and `χ(m) = h(ι(m))` on
   `M(F_∞)`, where `ι` is the inclusion of `M(F_∞)` in `G(F_∞)`. Inside the proof,
   `m_P(p(y) x)^λ = m_P(p(y))^λ m_P(x)^λ` for `y ∈ P(𝔸)` follows from `height_map_mul` and
   `height_map`. (The Library's `IsIwasawaCompact.heightPower_map_mul` states the same identity
   with the factor written as `parameterPower F P lam y`.) Since `(ι(m), 1)` is the image of a
   point of `P(𝔸)`, this gives `h(ι(m) x) = χ(m) h(x)`. Hence `χ` is multiplicative, and `χ(1) = 1`. The function `h` is
   smooth by `hasSmoothHeightPairings_of_maximalCompact` at the finite point `1`, and `χ` is
   its plot-smooth pullback along `ι` (`IsPlotSmooth.postcomp`).
   `exists_centerShift_plotSmoothMultiplication` gives an algebra endomorphism `θ` of `𝔷_M`
   with `w · (χ u) = χ · (θ(w) · u)` for all `w ∈ 𝔷_M` and all plot-smooth `u` on `M(F_∞)`.
3. *The ideal.* Let `J_λ = (θ ∘ p)⁻¹(I_M)`. It has finite codimension, because
   `𝔷 / J_λ` embeds into `𝔷_M / I_M` (`Langlands.Algebra.quotientFinite_comap`).
4. *`J_λ` kills every slice.* Fix a finite point `b`. Let `f` be the slice of `φ` at `b` and
   `F` the slice of `φ_λ` at `b`. By `heightPower_pair`, `F = c_b · h · f` with the constant
   `c_b = m_P((1, b))^λ`. Let `z ∈ J_λ` and `g ∈ G(F_∞)`. Write `R_g` for right translation by
   `g`.
   - `(z F)(g) = (z (R_g F))(1)`, since the center action commutes with right translations for
     connected reductive `G` (`plotSmoothCenterAction_rightTranslation`).
   - Evaluating at `1 = ι(1)` and using the transfer for the left `U(F_∞)`-invariant function
     `R_g F` gives `(z (R_g F))(1) = (p(z) · u_F)(1)`, where `u_F(m) = F(ι(m) g)`.
   - By `h(ι(m) g) = χ(m) h(g)`, `u_F = c_b h(g) · χ · u_f` with `u_f(m) = f(ι(m) g)`.
     Hence `p(z) · u_F = c_b h(g) · χ · (θ(p(z)) · u_f)`.
   - The function `R_g f` is left `U(F_∞)`-invariant and killed by `J`, because the center
     action commutes with `R_g` and `J` kills `f`. Since `θ(p(z)) ∈ I_M`, step 1 gives
     `θ(p(z)) · u_f = 0`.

   So `(z F)(g) = 0` for every `g`. The single ideal `J_λ` kills every infinite slice of `φ_λ`,
   which is `IsCenterFiniteFunction F G hsmooth hcalc (hK.parameterTwist φ lam)`.

## Sources

The proof adapts the finite center transfer of Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series* (1995), I.2.17, printed pp. 37–38, to the twist in Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.2, p. 191,
where "`φ_λ ∈ 𝒜_P`" is asserted. In I.2.17 a Harish-Chandra homomorphism `i : 𝔷 → 𝔷_M`, with
`𝔷_M` finitely generated over `i(𝔷)`, compares annihilating ideals of a function on
`U(𝔸) \ G` and of its normalized restrictions to `M`. Here the transfer is used in the
unnormalized convention of `ParabolicLeviCenterRestrictionStatement`, so no
`ρ_P`-normalization appears. The step specific to the twist, that multiplication by the
character `m ↦ m_P(m)^λ` of `M(F_∞)` changes the center action of `M(F_∞)` by an algebra
endomorphism `θ` of `𝔷_M`, comes from the Leibniz rule and the universal property of the
enveloping algebra (`exists_centerShift_plotSmoothMultiplication`). Composing `θ` with the
transfer, a single contraction of a cofinite ideal kills every slice of `φ_λ`.
