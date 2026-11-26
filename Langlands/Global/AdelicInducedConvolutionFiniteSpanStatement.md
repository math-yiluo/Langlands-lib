# Finite span of the integrated induced action on `A^2_P`

Module `Langlands.Global.AdelicInducedConvolutionFiniteSpanStatement` states one proposition,
`Langlands.Global.InducedConvolutionFiniteSpanStatement`. It proves nothing.

## Statement

Data, as in the Library's `EisensteinImaginaryAxisHolomorphyStatement`:

- a number field `F : Type`, a connected reductive `G`, a parabolic `p : P → G` (closed
  immersion) with geometric unipotent radical `iU : U → P`, a Levi `l : M → P` and a
  presentation `r : ParabolicRootPresentation p l a` of the split component `a : A → M` (with
  `hA`, `hT` and the instances of that presentation);
- a maximal compact subgroup `K` of `G(𝔸)` with `hK : IsIwasawaCompact p K`
  (`P(𝔸) K = G(𝔸)`), for which some minimal parabolic `p₀ : P₀ → G` also satisfies
  `IsIwasawaCompact p₀ K`;
- a closed matrix embedding `rho : G → GL_N` (`IsClosedSubgroup rho`) and the smooth-structure
  data `hsmooth`, `hcalc`;
- `v` with `IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v`, that is,
  `v ∈ A^2_P` (module `Langlands.Global.AdelicSquareIntegrableInducedForms`);
- `φ` with `IsLeftFiniteTestFunction F G K_∞ φ`, `K_∞ = K.comap (ofInfinite F G)`: continuous,
  compactly supported, its left translates by `K_∞` span a finite-dimensional space, and it is
  left invariant under an open subgroup of `G(𝔸_f)` (module
  `Langlands.Global.AdelicWavePacketTranslationReduction`).

Conclusion: there are `m : ℕ`, functions `w : Fin m → (G(𝔸) → ℂ)` and
`b : Fin m → (X^*(P) ⊗ ℂ → ℂ)` such that

1. every `w i ∈ A^2_P` (same `K`, `rho`, `hsmooth`, `hcalc`, `p`, `iU`, `l`);
2. every `b i` is holomorphic in linear coordinates on all of `X^*(P) ⊗ ℂ`
   (`IsHolomorphicInCoordinatesOn (b i) univ`), that is, entire;
3. for every `λ ∈ X^*(P) ⊗ ℂ`, `hK.inducedConvolution λ φ v = ∑ i, b i λ • w i` as functions on
   `G(𝔸)`.

Here `hK.inducedConvolution λ φ v (x) = ∫ φ(h) v(x h) exp⟨λ, H_P(x h) − H_P(x)⟩ dh` (module
`Langlands.Global.AdelicEisensteinConvolutionIdentity`) for `Measure.haar` on `G(𝔸)` and the
Iwasawa height `H_P` of `hK`; the half-modulus is part of `v`, as in Lapid's normalization.

The presentation data `a`, `r`, `hA`, `hT` do not occur in the conclusion. They fix `P = MU` as
a parabolic with a Levi and a presented split component, in the same form as the Library's
Eisenstein series statements, so that the proposition applies to the data of `IsWavePacket`.
Like `WavePacketConvolutionStatement`, the proposition quantifies over every parabolic with
these data (not only over parabolics containing a fixed minimal one), over every such `K`
(which need not be in good position for the Levi `l`), and over every test function of
`IsLeftFiniteTestFunction`; such `φ` is only continuous, left `K_∞`-finite and left invariant
under an open subgroup of `G(𝔸_f)`, not smooth or bi-`K`-finite. The comparison with the
sources below works under exactly these hypotheses.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  - I.1.4, pp.4–5: a fixed minimal parabolic `P₀` with Levi `M₀`; standard parabolics are those
    containing `P₀`, each with a unique standard Levi containing `M₀`. The maximal compact `K`
    can be required to satisfy (i) `G(𝔸) = P₀(𝔸) K` and (ii)
    `P(𝔸) ∩ K = (M(𝔸) ∩ K)(U(𝔸) ∩ K)` with `M(𝔸) ∩ K` maximal compact in `M(𝔸)`, for every
    standard `P = MU`; the remark on p.5 calls (ii) "useful but not indispensable".
  - I.2.17, pp.37–38: for a standard `P = MU`, a function on `U(𝔸) M(F) \ G(𝔸)` is automorphic
    if it has moderate growth, is smooth, `K`-finite and `𝔷`-finite. The algebras `𝔷` and `𝔷^M`
    act on smooth functions on `U(𝔸) \ G(𝔸)` by right and by left translation, and there is a
    homomorphism `i : 𝔷 → 𝔷^M` relating the two actions through the half-modulus normalization
    `ϑ'(g) = m_P(g)^{-ρ_P} ϑ(g)`. The relation used below applies the normalization to both
    functions: `(z.ϑ)' = i(z).ϑ'` for smooth `ϑ` and `z ∈ 𝔷`. The formula printed on p.37,
    `z.φ = i(z).φ'`, omits the normalization of `z.φ`; read literally with `z = 1` it would give
    `φ = φ'`. Mœglin–Waldspurger use the relation to pass between `𝔷`-finiteness of `ϑ` and
    `𝔷^M`-finiteness of `ϑ'` (pp.37–38), which is what the normalized form gives. Since
    `ϑ ↦ ϑ'` is injective, it also gives the kernel equivalence used in step 4 below: `z`
    annihilates `ϑ` exactly when `i(z)` annihilates `ϑ'`.
    "The finiteness theorem (see [HC] Theorem 1)" generalizes to these forms: the automorphic
    forms with `K`-types in a given finite set that are annihilated by a given ideal of finite
    codimension in `𝔷` form a finite-dimensional space.
  - IV.1.1–IV.1.3, pp.135–137: for a fixed finite set `𝔨` of `K`-types and a fixed orbit `𝔓`
    of irreducible cuspidal representations of a standard Levi, the space `A(M, π)_𝔨` is
    finite-dimensional (IV.1.3, p.136). This is the fixed-cuspidal-orbit instance of the
    finiteness theorem; the proposition concerns all of `A^2_P` and rests on the general
    theorem of I.2.17.
  - IV.1.7, p.139: the action `i(π, h)` on the inducing data of the algebra `𝓗_𝔨` of smooth
    compactly supported bi-`𝔨`-finite functions, "a multiple of the induced representation",
    and the relation (*) between `E(i(π, h) φ, π)` and the convolution of `E(φ, π)` by `h`.
- J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §7: printed p.33 (PDF p.45), the
  operator `I_P(λ, y)` on the inducing data, which depends on `λ`; printed p.34 (PDF p.46), the
  identity `E(x, I_P(λ, y) φ, λ) = E(x y, φ, λ)`. With the half-modulus absorbed into the
  inducing function, `I(λ, φ)` is the integral of `I_P(λ, h)` against `φ(h) dh` (module
  `Langlands.Global.AdelicEisensteinConvolutionIdentity`).
- Harish-Chandra, *Automorphic forms on semisimple Lie groups* (notes by J. G. M. Mars),
  Lecture Notes in Math. 62, Springer 1968, registered as
  `provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`: Chapter I,
  Theorem 1, p.8, the finiteness theorem cited by Mœglin–Waldspurger as [HC] Theorem 1. Its
  proof, pp.19–20, normalizes the constant term along a cuspidal subgroup by the factor
  `d(m) = |det(Ad(m)|_𝔲)|^{1/2}`, uses `μ(z)' = d⁻¹ ∘ μ(z) ∘ d` for the homomorphism `μ` of
  centers, and applies the normalization to `z f` as well as to `f`; this is the analogue of the
  normalized relation above.
- A. Borel, *Linear algebraic groups*, 2nd ed., GTM 126 (1991), registered as
  `borel-1991-linear-algebraic-groups-second`, Theorem 20.9 (i), p.228: the minimal parabolic
  `k`-subgroups of a connected reductive `k`-group are conjugate under `G(k)`.
- A. Borel, *Lie groups and linear algebraic groups, I. Complex and real groups* (lecture notes,
  2000–2001), registered as `borel-lie-groups-linear-algebraic-groups-2000`, §6.7, p.47: the
  maximal compact subgroups of a real reductive group are all conjugate under its identity
  component.

## Provenance

Derived. The proposition packages what the proof of convolution stability of wave packets needs
from the finiteness theorem (the route is described under `WavePacketConvolutionStatement` in
`AdelicWavePacketTranslationReduction.md`). Write `f_λ = I(λ, φ) v`, `K_∞` and `K_f` for the
archimedean and finite parts of `K`, and `L` for the open subgroup of `G(𝔸_f)` under which `φ`
is left invariant. The functions `f_λ` lie in one finite-dimensional subspace of `A^2_P`, by the
following comparison with the setting of Mœglin–Waldspurger.

1. *Each `f_λ` lies in `A^2_P`* (the `K_∞`-finiteness and `𝔷`-finiteness are shown in 2
   and 4). For `x ∈ G(𝔸)`, `f_λ(x) = ∫ φ(h) v(x h) exp⟨λ, H_P(x h) − H_P(x)⟩ dh`. Since
   `H_P(q x) = H_P(q) + H_P(x)` for `q ∈ P(𝔸)`, the difference `H_P(x h) − H_P(x)` is unchanged
   when `x` is multiplied on the left by `P(𝔸)`, so the left `U(𝔸) M(F)`-invariance and the
   `A_M`-equivariance `v(a x) = δ_P(a)^{1/2} v(x)` (`IsSplitComponentEquivariant`) pass to
   `f_λ`. For `x = q k` with `q ∈ P(𝔸)` and `k ∈ K` the difference is `H_P(k h)`. The height
   `H_P` is bounded on compact subsets of `G(𝔸)`: the map `P(𝔸) × K → G(𝔸)`, `(q, k) ↦ q k`,
   is the orbit map of a continuous transitive action of a σ-compact locally compact group, hence
   open, so a compact subset of `G(𝔸)` lies in `Q K` for a compact `Q ⊆ P(𝔸)`, and `H_P` is
   continuous on `P(𝔸)`. As `K · supp φ` is compact,
   `C_λ = sup {|exp⟨λ, H_P(k h)⟩| : k ∈ K, h ∈ supp φ}` is finite, and for all `x ∈ G(𝔸)`
   `|f_λ(x)| ≤ C_λ ∫ |φ(h)| |v(x h)| dh`.  (B)
   - *Square integrability.* Write `‖ϑ‖² = ∫_{K × [M]} δ_P(m)⁻¹ |ϑ(m k)|² dk dm` for the norm in
     `IsSquareIntegrableInducedForm` (Haar probability on `K`, `[M] = A_M M(F) \ M(𝔸)`), for
     `ϑ` left `U(𝔸) M(F)`-invariant with `|ϑ(a x)| = δ_P(a)^{1/2} |ϑ(x)|` for `a ∈ A_M`. The
     right translates `R(h) ϑ (x) = ϑ(x h)`, `h ∈ G(𝔸)`, are again of this form, and
     `‖R(h) ϑ‖ = ‖ϑ‖`: this is the unitarity of the normalized induced representation at
     `λ = 0` (Arthur §7, p.33, with the half-modulus included in `ϑ`; his norm on p.32 is the
     same Iwasawa integral). It rests on the decomposition of Haar measure
     `∫_{G(𝔸)} f = ∫_K ∫_{M(𝔸)} ∫_{U(𝔸)} f(m u k) du dm dk` (Arthur p.32, for a standard
     parabolic and his `K`). The decomposition holds for the stated `K` and Levi `l` as well:
     `du dm` is a left Haar measure on `P(𝔸) = M(𝔸) U(𝔸)`, so the right side is a positive
     Radon measure on `G(𝔸)` invariant under `P(𝔸) × K` acting by `(q, k)·x = q x k⁻¹`; this
     action is transitive because `P(𝔸) K = G(𝔸)`, the stabilizer of `1` is the compact diagonal
     copy of `P(𝔸) ∩ K`, and an invariant measure on a homogeneous space with compact stabilizer
     is unique up to a positive factor. Haar measure on the unimodular group `G(𝔸)` is also
     invariant under this action, so the right side is a multiple of it. By (B)
     for `x = m k` and Minkowski's integral inequality in `L²(K × [M], δ_P(m)⁻¹ dk dm)`,
     `‖f_λ‖ ≤ C_λ ∫ |φ(h)| ‖R(h) v‖ dh = C_λ ‖φ‖_{L¹} ‖v‖ < ∞`.
   - *Moderate growth.* If `|v(y)| ≤ c ‖y‖^n`, then (B) and `‖x h‖ ≤ c' ‖x‖ ‖h‖` with
     `‖h‖` bounded on `supp φ` give `|f_λ(x)| ≤ c'' ‖x‖^n`.
   - *Smoothness.* `f_λ = ψ⁻¹ · R(φ)(ψ v)` with `ψ = exp⟨λ, H_P(·)⟩` and
     `R(φ) ϑ (x) = ∫ φ(h) ϑ(x h) dh`. It is smooth because `ψ v` is smooth and `φ` has compact
     support: `x e^{tX} h = x h e^{t Ad(h⁻¹) X}`, so derivatives in `x` pass under the
     compactly supported integral, without smoothness of `φ`.
2. *Types and level, uniformly in `λ`.* Since `H_P(x k) = H_P(x)` for `k ∈ K` and Haar measure
   is invariant, `f_λ(x k) = I(λ, φ(k⁻¹ ·)) v (x)` for `k ∈ K`. For `k ∈ K_∞`, the right
   `K_∞`-translates of `f_λ` are therefore images of the left translates of `φ` under the linear
   map `φ₁ ↦ I(λ, φ₁) v`, which commutes with the `K_∞`-actions. The left translates of `φ` span a
   finite-dimensional representation `W_φ` of `K_∞`, so the `K_∞`-types of every `f_λ` lie in
   the finite set `τ` of types of `W_φ`. For `k ∈ L ∩ K_f`, `φ(k⁻¹ ·) = φ`, so every `f_λ` is
   right invariant under the subgroup `L ∩ K_f` of `G(𝔸_f)`. This subgroup is open: `K` is the
   product of its images in `G(F_∞)` and `G(𝔸_f)` (their product is a compact subgroup
   containing `K`), so these images are `K_∞ = K ∩ G(F_∞)` and `K_f = K ∩ G(𝔸_f)`, and each is
   a maximal compact subgroup of its factor (a larger compact subgroup of one factor times the
   other image would be a compact subgroup strictly containing `K`). In the totally
   disconnected group `G(𝔸_f)`, the open subgroup `L` contains a compact open subgroup `C`.
   The intersection `C°` of the `K_f`-conjugates of `C` is
   an intersection of finitely many of them (the normalizer of `C` is open), hence open, and
   `K_f C°` is a compact subgroup containing `K_f`; by maximality `C° ⊆ K_f`, so the open
   subgroup `C°` lies in `L ∩ K_f`.
3. *Passage to a standard parabolic and to Mœglin–Waldspurger's `K`.* Fix `P₀`, `M₀` and a
   `K' = K'_∞ K'_f` satisfying I.1.4 (i)–(ii), as Mœglin–Waldspurger allow. (The supplied `K`
   satisfies (i) for the supplied `p₀`, but (ii) is not assumed; the comparison does not use
   `p₀`.) The parabolic `P` contains a minimal parabolic `F`-subgroup, which is
   `G(F)`-conjugate to `P₀` (Borel 20.9 (i); in the Library, the theorems
   `Langlands.GroupScheme.parabolicContainsMinimalStatement` and
   `Langlands.GroupScheme.minimalParabolicConjugacy`, the latter after Borel–Tits 4.13 (b)), so
   `P' = γ P γ⁻¹ ⊇ P₀` for some `γ ∈ G(F)`; let `M'` be its standard Levi and `U'` its unipotent
   radical. Since `P(F) = M(F) U(F)`, `U(𝔸) M(F) = U(𝔸) P(F)` depends on `P` only, not on the
   Levi `l`, and `γ U(𝔸) P(F) γ⁻¹ = U'(𝔸) M'(F)`. By step 2, `K_∞` is a maximal compact
   subgroup of `G(F_∞)`, and so is `K'_∞`. The maximal compact subgroups of the real reductive
   group `G(F_∞) = (Res_{F/ℚ} G)(ℝ)` are conjugate (Borel §6.7, under its identity component;
   in the Library, `Langlands.Global.InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy`,
   which gives `t` with `K'_∞ = t K_∞ t⁻¹`). Choose `g ∈ G(F_∞)` with `K'_∞ = g K_∞ g⁻¹` and put
   `T f (x) = f(γ⁻¹ x g)`. Then `T` is a linear bijection from functions on
   `U(𝔸) M(F) \ G(𝔸)` to functions on `U'(𝔸) M'(F) \ G(𝔸)`. It preserves smoothness and
   moderate growth (`‖γ⁻¹ x g‖` is bounded by a constant times a power of `‖x‖`), commutes with
   right translations by `G(𝔸_f)` (which commute with `g`) and with the right action of `𝔷`
   (`T(R(u) f) = R(Ad(g) u)(T f)` for `u` in the enveloping algebra, and `Ad(g)` fixes `𝔷`
   because `G` is connected). For the right action of `k' ∈ K'_∞`,
   `R(k') T f (x) = f(γ⁻¹ x g · g⁻¹ k' g) = T(R(g⁻¹ k' g) f)(x)` with `g⁻¹ k' g ∈ K_∞`.
   Hence `T` carries right `K_∞`-finite functions with types in `τ` to right `K'_∞`-finite
   functions with types in the set `τ^g` of the representations `k' ↦ σ(g⁻¹ k' g)`, `σ ∈ τ`.
   The functions `T f_λ` are right invariant under `L ∩ K_f`,
   hence under an open normal subgroup `L°` of `K'_f` (the intersection of the finitely many
   `K'_f`-conjugates of the open subgroup `L ∩ K_f ∩ K'_f`), so they are `K'_f`-finite with
   types among the irreducible representations of the finite group `K'_f / L°`. Altogether the
   `K'`-types of all `T f_λ` lie in one finite set.
4. *One annihilating ideal for all `λ`.* Let `J ⊆ 𝔷` be an ideal of finite codimension
   annihilating `v` (part of `v ∈ A_P`); it annihilates `T v`. Moreover
   `T f_λ = Ψ⁻¹ · R(φ^g)(Ψ · T v)` with `Ψ = T ψ` and `φ^g(h) = φ(g⁻¹ h g)` (Haar measure on
   `G(𝔸)` is invariant under conjugation). The function `Ψ`
   is left `U'(𝔸)`-invariant and satisfies `Ψ(m x) = χ(m) Ψ(x)` for `m ∈ M'(𝔸)` and a
   character `χ` of `M'(𝔸)`, because `H_P(q x) = H_P(q) + H_P(x)` for `q ∈ P(𝔸)` and
   `γ⁻¹ M'(𝔸) γ ⊆ P(𝔸)`. The half-modulus normalization of I.2.17 transports `J` as follows.
   With `ϑ' = m_{P'}^{-ρ_{P'}} ϑ` for smooth left `U'(𝔸)`-invariant `ϑ`, the normalized
   relation `(z.ϑ)' = i(z).ϑ'` (see Sources) and the injectivity of `ϑ ↦ ϑ'` show that `z ∈ 𝔷`
   annihilates `ϑ` exactly when `i(z)` annihilates `ϑ'` for the left translation action. Here
   `(T f_λ)' = Φ⁻¹ · R(φ^g)(Φ · (T v)')` with `Φ = m_{P'}^{ρ_{P'}} Ψ`, which is again left
   `U'(𝔸)`-invariant and `M'(𝔸)`-equivariant for a character `χ'`. For `u` in the enveloping
   algebra of `Lie M'(F_∞)` acting by left translation, `u.(Φ ϑ) = Φ · σ(u).ϑ`, where `σ` is
   the automorphism of that enveloping algebra
   extending `Y ↦ Y + c(Y)` for the linear form `c = ±dχ'` (the sign is that of the convention
   for the left action), and left translations commute with the right convolution `R(φ^g)`. Hence
   `i(z).(T f_λ)' = Φ⁻¹ · R(φ^g)(Φ · i(z).(T v)') = 0` for `z ∈ J`. The fixed factor
   `m_{P'}^{-ρ_{P'}}` and the `λ`-dependent twist are absorbed together into `Φ`, whose shift
   `σ` cancels between `Φ⁻¹` and `Φ`; so the same `J` annihilates every `T f_λ`, and every
   `f_λ` because `T` commutes with `𝔷`.
5. *Finiteness.* By 3 and 4 the functions `T f_λ` are automorphic forms on
   `U'(𝔸) M'(F) \ G(𝔸)` in the sense of I.2.17 (moderate growth, smooth, `K'`-finite,
   `𝔷`-finite), with `K'`-types in one finite set and annihilated by `J`. By the finiteness
   theorem of I.2.17 they span a finite-dimensional space, hence so do the `f_λ` (apply `T⁻¹`).
   Their span `V` lies in `A^2_P` by 1; choose `w` a basis of `V` among the `f_λ`.
6. *Entire coefficients.* For each `x`, `λ ↦ f_λ(x)` is entire: the integrand is entire in `λ`,
   and it is bounded locally uniformly in `λ` because `φ` has compact support and `H_P` is
   bounded on compact sets. Point evaluations span the dual of `V`; choosing points `x_j` with
   `(w_i(x_j))` invertible, the coordinates `b i λ` of `f_λ` are fixed linear combinations of
   the values `f_λ(x_j)`, hence entire.

The relation (*) of IV.1.7 is the analogue for the algebra `𝓗_𝔨` of smooth bi-`𝔨`-finite `h`.
The steps above use only the properties of `φ` in `IsLeftFiniteTestFunction`: continuity and
compact support, finiteness of its left `K_∞`-translates, and left invariance under `L`.

## Scope

This module states the finite-span proposition and does not prove it. The comparison above uses
the finiteness theorem and the center-action relation of Mœglin–Waldspurger I.2.17, and the
conjugacy results cited in step 3, among them the Library theorems
`Langlands.GroupScheme.parabolicContainsMinimalStatement`,
`Langlands.GroupScheme.minimalParabolicConjugacy` and
`Langlands.Global.InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy`.
