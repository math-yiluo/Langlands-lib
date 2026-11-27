# The finite discrete content of square-integrable automorphic forms: reduction to two inputs

Module `Langlands.Global.AdelicFiniteProjectionReduction` reduces the published
`Langlands.Global.SquareIntegrableFormFiniteProjectionStatement` (module
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`) to two propositions:

- the published `Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement`
  (module `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`), Harish-Chandra's
  finiteness theorem, used here for the parabolic `P = G`;
- a new proposition, `SquareIntegrableProjectionAutomorphyStatement`: the orthogonal projection
  onto a closed invariant subspace of `L²([G])` of the class of a smooth square-integrable
  function of a fixed type `(J, L, E)` is the class of an automorphic form of the same type.

It proves the implication `squareIntegrableFormFiniteProjection_of_reduction`, together with the
comparisons it needs between Lapid's `A²_P` for an isomorphism `p` and functions on `[G]`. It
proves neither input proposition.

| Declaration | Kind | Source |
| --- | --- | --- |
| `SquareIntegrableProjectionAutomorphyStatement` | statement | derived: Harish-Chandra 1966, §7–8, Theorem 1; Getz–Hahn Theorem 6.2.4 and Corollary 6.2.5; Borel–Jacquet §3.2, §4.1–4.3; Mœglin–Waldspurger I.2.1–I.2.5 |
| `parabolicQuotientSubgroup_eq_rationalSubgroup_of_isIso` | theorem (proved) | internal |
| `isLeftInvariantUnder_canonicalSubgroup_of_isIso` | theorem (proved) | internal |
| `functionInfiniteSlice_sum` | theorem (proved) | internal |
| `isAdelicSmoothFunction_sum` | theorem (proved) | internal |
| `isInfiniteSubgroupFiniteFunction_sum` | theorem (proved) | internal |
| `finiteDimensional_span_infiniteSlices` | theorem (proved) | internal |
| `finite_quotient_iInf` | theorem (proved) | internal |
| `exists_combination_type` | theorem (proved) | internal |
| `exists_finiteDimensional_of_ae_eq` | theorem (proved) | internal |
| `squareIntegrableFormFiniteProjection_of_reduction` | theorem (proved) | internal |

All names are in the namespace `Langlands.Global`.

## Sources

Page numbers are printed pages, with one-based PDF pages in parentheses.

- J. R. Getz and H. Hahn, *An introduction to automorphic representations* (2024), registered as
  `getz-hahn-2024-automorphic-representations` (file SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`):
  - Theorem 6.2.4, p.160 (PDF p.174), after Harish-Chandra 1966, §8, Theorem 1: for a
    `K_∞`-finite, `Z(𝔤)`-finite function `φ` on `G(F_∞)` there is `f ∈ C_c^∞(G(F_∞))`, invariant
    under `K_∞`-conjugation and supported in any given neighbourhood of `1`, with `R(f)φ = φ`.
  - Corollary 6.2.5 and its proof, p.160 (PDF p.174): `X(R(f)φ) = R(f_X)φ` for `X ∈ U(𝔤)`, with
    `f_X ∈ C_c^∞(G(F_∞))`; this is how derivatives pass under the convolution integral.
  - Theorem 6.3.4, p.164 (PDF p.178), the adelic form of Harish-Chandra's finiteness theorem
    (Theorem 6.2.6, p.161, PDF p.175).
  - Theorems 4.4.1 and 4.4.2, p.114 (PDF p.129): for an affine algebraic group over `ℝ`, the
    group of real points has finitely many connected components, every maximal compact subgroup
    meets all of them, and any two maximal compact subgroups are conjugate.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations* (1979), registered
  as `borel-jacquet-1979-automorphic` (file SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`), one-based PDF pages
  189–190 of the retained volume: §3.2, p.194 (`Z` is the greatest `F`-split torus of the centre
  of `G`; the idempotent `e_L` of a compact open subgroup `L ≤ G(𝔸_f)`, with `f * e_L = f` if
  and only if `f` is right invariant under `L`); §4.1, p.194 (smooth functions on
  `G(𝔸) = G_∞ × G(𝔸_f)`); §4.2, p.195 (automorphic forms of type `(ξ, J, K_∞)`); §4.3, p.195:
  `G(𝔸) = G(F) · C · G_∞ · L` with `C ⊂ G(𝔸_f)` finite, (i) the space of automorphic forms of a
  fixed type is finite-dimensional, (ii) a smooth function satisfying 4.2 (a)–(c) with a central
  character `χ` of `Z(𝔸)/Z(F)` and `|f| ∈ L^p(Z(𝔸)G(F) \ G(𝔸))` for some `p ≥ 1` is slowly
  increasing.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition` (folder fingerprint
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`), chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (file SHA-256
  `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`): I.2.1, p.19 (PDF p.2),
  `G = A_G G^1`, with `G^c = G^1` for a number field; I.2.2, p.20 (PDF p.3), the height `‖g‖`
  defined by the embedding `i_G : G → SL_{2n}` of I.1.1 as `∏_v sup_{r,s} |g_{rs}|_v`, with
  (i) `‖g‖ ≥ c > 0` and (viii) `c ‖a‖^{t'} ‖g‖^t ≤ ‖a g‖` for `a ∈ A_G`, `g ∈ G^c`; I.2.4,
  pp.25–26 (PDF pp.8–9), the counting lemma: (a)(i) `∑_{γ ∈ G(k)} 1_C(x⁻¹ γ y) ≤ c ‖x‖^r` for
  all `x, y` and a compact `C`, and the proof deduces from it the bound (a)(ii) for the integral
  over `G(k) Z_G`; I.2.5, Lemma, p.27 (PDF p.10): right convolution by a smooth compactly
  supported function gives functions of moderate growth, in (b) for square-integrable
  functions with a unitary central character, and the Remark after the Lemma.
- Harish-Chandra, *Discrete series for semisimple Lie groups. II* (1966), registered as
  `harish-chandra-1966-discrete-series-ii` (file SHA-256
  `3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`):
  - §7, p.15, the setting: `𝔤` is a real reductive Lie algebra, `θ` an involution of `𝔤` with
    eigenspaces `𝔨` (for `1`) and `𝔭` (for `−1`) such that `Q(X) = −tr(ad X ad θ(X))` is
    positive definite on the derived algebra; `G` is a connected Lie group with Lie algebra `𝔤`
    and `K` the analytic subgroup for `𝔨`; `K` is compact and `(k, X) ↦ k exp X` is an analytic
    diffeomorphism of `K × 𝔭` onto `G`.
  - §2, p.6: the convolution is `(f * g)(x) = ∫ f(y) g(y⁻¹x) dy`.
  - §8, Theorem 1, p.18, with its proof pp.18–19: in the setting of §7, let `𝔷` be the centre of
    the enveloping algebra of `𝔤_ℂ` and `𝔎` the subalgebra generated by `1` and `𝔨_ℂ`. If `f` is
    a smooth function on `G` with values in a finite-dimensional complex space and the
    functions `z f`, `z ∈ 𝔷𝔎`, span a finite-dimensional space, then for every neighbourhood `U`
    of `1` there is `α ∈ C_c^∞(G)` with support in `U` and `α(k x k⁻¹) = α(x)` (`k ∈ K`) such
    that `f * α = f`.
- A. Borel, *Lie groups and linear algebraic groups, I. Complex and real groups* (lecture notes,
  2000–2001), registered as `borel-lie-groups-linear-algebraic-groups-2000` (file SHA-256
  `784f2fc696cc43c5e4375b8d1414439cce180a7273caa620aa27a9c4d8d1809c`), §6.3, Proposition and
  Remark, pp.42–43 (PDF pp.42–43): an algebraic subgroup `H ≤ GL_n(ℝ)` stable under
  `θ(g) = ᵗg⁻¹` is reductive, `K = H ∩ O_n` is a maximal compact subgroup with Lie algebra
  `𝔨 = 𝔥 ∩ 𝔬_n`, and `(k, X) ↦ k exp X` is a diffeomorphism of `K × 𝔭` onto `H`, where `𝔭` is
  the space of symmetric matrices in `𝔥`; conversely a real reductive algebraic subgroup of
  `GL_n(ℝ)` is, after conjugation, stable under `θ` (Mostow 1955; Borel–Harish-Chandra 1962,
  Lemma 1.8).

## Setting and conventions

`L²([G])` is `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)` on the canonical quotient
`[G] = A_G G(F) \ G(𝔸)`, and
`R = RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG` is the right
regular representation of `G(𝔸)` on it. A class `f` is related to a function `φ` on `G(𝔸)` by
`f =ᵐ fun y => φ y.out`, where `y.out` is a representative in `G(𝔸)` of `y ∈ [G]`; this is
meaningful for functions that are left invariant under `A_G G(F)`. The archimedean compact
subgroup is `K_∞ = K.comap (ofInfinite F G)`. Smoothness is the Library's
`IsAdelicSmoothFunction` (continuity, smooth archimedean slices and one open level in
`G(𝔸_f)`), which follows Borel–Jacquet §4.1 with the common level of §4.2; the Markdown of
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction` explains this convention.

A *type* `(J, L, E)` consists of an ideal `J` of finite codimension of the centre
`𝔷 = AdelicEnvelopingCenter F G hsmooth`, an open subgroup `L` of `G(𝔸_f)` and a
finite-dimensional space `E` of functions on `K_∞`. A function `φ` has this type if it is right
invariant under `L`, every `z ∈ J` annihilates every smooth infinite slice of `φ` under
`plotSmoothCenterAction`, and every function `k ↦ φ(g k)` on `K_∞` lies in `E`. These are the
conditions 2–4 of `ParabolicHarishChandraFinitenessStatement`. They express Borel–Jacquet's
type `(ξ, J, K_∞)` of §4.2, with the `K_∞`-types fixed by `E` and the Hecke condition replaced by
the level `L`.

## Statement

### `SquareIntegrableProjectionAutomorphyStatement`

For a number field `F : Type`, a group `G` with `IsAffineHom G.X.hom`, `IsAffine G.X.left`,
`LocallyOfFiniteType G.X.hom` and `hG : IsConnectedReductive G`, a subgroup `K` of `G(𝔸)` with
`IsMaximalCompactSubgroup F G K`, a matrix representation `rho` with `IsClosedSubgroup rho`, and
`hsmooth`, `hcalc`: let `(J, L, E)` be a type and `φ : G(𝔸) → ℂ` a function such that

1. `φ` is left invariant under `rationalSubgroup F G` (that is `G(F)`) and under
   `RestrictionSplitCentre.canonicalSubgroup F G` (that is `A_G`);
2. `IsAdelicSmoothFunction F G φ`;
3. `φ` has type `(J, L, E)`;

and let `f ∈ L²([G])` with `f =ᵐ fun y => φ y.out`. Then for every subspace `V` of `L²([G])`
with `V.HasOrthogonalProjection` that is invariant under every `R g`, there is `ψ : G(𝔸) → ℂ`
such that

- `IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K_∞ rho ψ`: `ψ` is left
  invariant under `G(F)`, smooth, `K_∞`-finite, `𝔷`-finite and of moderate growth for the adelic
  norm of `rho`;
- `ψ` is left invariant under `A_G`;
- `ψ` has the same type `(J, L, E)`;
- `V.starProjection f =ᵐ fun y => ψ y.out`.

Correspondence and provenance (derived). In a Hilbert space the subspaces with an orthogonal
projection are the closed ones, so `V` ranges over the closed `G(𝔸)`-invariant subspaces of
`L²([G])`. The proposition isolates the analytic steps 3–6 of the argument recorded for
`SquareIntegrableFormFiniteProjectionStatement` in the Markdown of
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`, for one function and with the type
fixed in advance. It holds by the following classical argument.

1. *Equivariance of the projection.* Since `R` is unitary and `V` is invariant, `P_V` commutes
   with every `R g`, hence with every integrated operator `R(β) = ∫ β(g) R(g) dg`,
   `β ∈ C_c(G(𝔸))`. So `P_V f` is fixed by `R(L)`. Let `Φ` be the span of the right
   `K_∞`-translates `R(k)φ = φ(· k)` of `φ`; it is finite-dimensional, since the functions
   `k ↦ φ(g k)` lie in `E`, and it contains `φ`. If `φ_1, …, φ_n` is a basis of `Φ` and
   `R(k)φ = ∑ a_i(k) φ_i`, then each `a_i` is a linear combination of functions `k ↦ φ(g_j k)`
   (evaluate at points `g_j` where the matrix `(φ_i(g_j))` is invertible), so `a_i ∈ E`, and
   `R(k) P_V f = ∑ a_i(k) P_V f_i` with `f_i` the class of `φ_i`.
2. *A common reproducing kernel.* Write `G_∞ = G(F_∞)` and `(y, b)` for the point of `G(𝔸)`
   with archimedean component `y` and finite component `b`. Every element of `Φ` is left
   invariant under `G(F)`, right invariant under `L` (right translations by `G_∞` and by
   `G(𝔸_f)` commute) and has smooth slices. The slice at `b` of `R(k)φ`, `k ∈ K_∞`, is the
   right translate by `k` of the slice of `φ` at `b`, and right translation by `k` commutes with
   the action of `𝔷` because `Ad(k)` fixes `𝔷`
   (`Langlands.Automorphic.GroupSchemeFunctions.adelicEnvelopingCenterConjugation`). So `J`
   annihilates the slices of every element of `Φ`.

   *The Cartan setting on `G_∞°`.* `G_∞` is the group of real points of the connected reductive
   `ℝ`-group obtained from `G` by restriction of scalars, so it has finitely many connected
   components (Getz–Hahn, Theorem 4.4.1). `K_∞` is a maximal compact subgroup of `G_∞`: the
   compact group `K` lies in the product of its projections to `G_∞` and to `G(𝔸_f)`, which is
   compact, so by maximality `K` is this product and `K_∞` is its archimedean projection; a
   compact subgroup of `G_∞` containing `K_∞`, times the finite projection, is a compact
   subgroup of `G(𝔸)` containing `K`. Realize `G_∞` as an algebraic subgroup of some `GL_n(ℝ)`
   stable under `θ(g) = ᵗg⁻¹` (Borel's notes, §6.3, Remark). By the Proposition of §6.3,
   `K_0 = G_∞ ∩ O_n` is a maximal compact subgroup and `(k, X) ↦ k exp X` is a diffeomorphism
   of `K_0 × 𝔭_0` onto `G_∞`, where `𝔨_0 = Lie(K_0)` and `𝔭_0` are the eigenspaces of
   `dθ(X) = −ᵗX` in `𝔤 = Lie(G_∞)`. Harish-Chandra's form is
   `Q(X) = −tr(ad X ad dθ(X)) = tr(ad X ∘ (ad X)^*)` for the inner product
   `(A, B) ↦ tr(A ᵗB)` on `𝔤`, so `Q(X) > 0` unless `X` is central, and `Q` is positive definite
   on the derived algebra. By Getz–Hahn, Theorem 4.4.2, `K_∞ = u K_0 u⁻¹` for some `u ∈ G_∞`.
   Conjugating by `u` gives an involution `θ_∞` of `𝔤` with fixed algebra `𝔨 = Lie(K_∞)`,
   `−1`-eigenspace `𝔭`, the same positivity, and a diffeomorphism of `K_∞ × 𝔭` onto `G_∞`.
   Since `𝔭` is connected, the identity component is `G_∞° = K_∞° exp 𝔭`, the diffeomorphism
   restricts to `K_∞° × 𝔭 → G_∞°`, and `K_∞ ∩ G_∞° = K_∞°` is the compact analytic subgroup
   for `𝔨`. So `G_∞°` with `θ_∞` and `K_∞°` is in the setting of Harish-Chandra 1966, §7.

   *Application of Harish-Chandra's theorem.* Fix a compact open subgroup `L' ≤ L` (compact open
   subgroups form a neighbourhood basis of `1` in `G(𝔸_f)`). By Borel–Jacquet §4.3,
   `G(𝔸) = G(F) · T · G_∞ · L'` for a finite set `T ⊂ G(𝔸_f)` (their `C`); let `c` run through
   representatives of the components of `G_∞`. For `ϕ ∈ Φ` and `x ∈ G_∞°` put
   `Λ_ϕ(x) = (ϕ((c x, t)))_{c, t ∈ T}`, and let `Λ = (Λ_{φ_1}, …, Λ_{φ_n})`, a smooth function on
   `G_∞°` with values in a finite-dimensional space. Since `Λ_{R(k)ϕ} = Λ_ϕ(· k)` for
   `k ∈ K_∞°` and `Φ` is stable under `R(K_∞)`, the right `K_∞°`-translates of `Λ`, and hence
   its images under `𝔎` (the algebra generated by `1` and `𝔨_ℂ`), lie in the finite-dimensional
   space of tuples `(Λ_{ϕ_1}, …, Λ_{ϕ_n})`, `ϕ_i ∈ Φ`. Left-invariant differential operators
   commute with left translation by `c`, so `z ∈ 𝔷` acts on `Λ_ϕ` through the slices of `ϕ` at
   the points of `T`, which `J` annihilates. Hence `z(uΛ) = 0` for `z ∈ J` and `u ∈ 𝔎`, and the
   functions `(z u) Λ = z(uΛ)`, `z ∈ 𝔷`, `u ∈ 𝔎`, span a finite-dimensional space. Harish-Chandra
   1966, §8, Theorem 1 (the source of Getz–Hahn, Theorem 6.2.4) gives `α ∈ C_c^∞(G_∞°)`,
   invariant under conjugation by `K_∞°` and supported in a given neighbourhood of `1`, with
   `Λ * α = Λ`. With Harish-Chandra's convolution `(Λ * α)(x) = ∫ Λ(y) α(y⁻¹ x) dy` (§2) and the
   unimodularity of `G_∞°`, this reads `Λ(x) = ∫ α̌(h) Λ(x h) dh` with `α̌(h) = α(h⁻¹)`, that is
   `φ_i((c x, t)) = ∫_{G_∞°} α̌(h) φ_i((c x h, t)) dh` for all `i`, `c`, `t ∈ T` and
   `x ∈ G_∞°`.

   *Extension to `G(𝔸)`.* Every `g ∈ G(𝔸)` is `δ (c x, t) l` with `δ ∈ G(F)`, `x ∈ G_∞°`,
   `t ∈ T` and `l ∈ L'`. Since `G_∞` commutes with `G(𝔸_f)`, `g h = δ (c x h, t) l` for
   `h ∈ G_∞°`, and the left `G(F)`-invariance and right `L'`-invariance of `φ_i` give
   `φ_i(g) = ∫ α̌(h) φ_i(g h) dh`. Let `β = α̌ ⊗ e_{L'}` on `G(𝔸) = G_∞ × G(𝔸_f)`, with `α̌`
   extended by zero to `G_∞` and `e_{L'}` the idempotent of Borel–Jacquet §3.2. Then
   `R(β)φ_i = φ_i` for every `i`, so `R(β)ϕ = ϕ` for every `ϕ ∈ Φ`, `φ` included. Hence
   `f = R(β) f` and `f_i = R(β) f_i`, and by step 1 `P_V f = R(β) P_V f` and
   `P_V f_i = R(β) P_V f_i`. One kernel reproduces `φ` and all the `φ_i`, so no commutation of
   `R(β)` with right translations by components of `K_∞` outside `K_∞°` is needed.
3. *Regularity.* For a class `w ∈ L²([G])` let `w̃` be its pullback to `G(𝔸)`, left invariant
   under `A_G G(F)`. The class `R(β)w` is represented by
   `R(β)w(x) = ∫_{G(𝔸)} β(h) w̃(x h) dh = ∫_{G(𝔸)} β(x⁻¹ y) w̃(y) dy`, a continuous function on
   `G(𝔸)`, left invariant under `A_G G(F)`, right invariant under `L'`, with smooth archimedean
   slices (differentiate `β(x⁻¹ y)` in `x`, as in the proof of Mœglin–Waldspurger I.2.5, Lemma).
4. *Growth.* Let `G(𝔸)^1` be the norm-one subgroup (`AdelicGroupPoints.normOneSubgroup F G`,
   the common kernel of the norms of the rational characters). Then `G(𝔸) = A_G G(𝔸)^1`
   (Mœglin–Waldspurger I.2.1, where `G^c = G^1` for a number field), `A_G ∩ G(𝔸)^1 = 1` since a
   point of `A_G` is determined by the norms of the rational characters, so `G(𝔸)` is the
   direct product `A_G × G(𝔸)^1`, and `G(F) ≤ G(𝔸)^1`
   (`AdelicGroupPoints.rationalSubgroup_le_normOneSubgroup`). So
   `A_G G(F) = A_G × G(F)`, and the Haar measure of `A_G G(F)` is `da` times counting measure for
   a suitable Haar measure `da` of `A_G`. The canonical measure is Weil compatible with these
   Haar measures (`RestrictionSplitCentre.canonicalMeasure_isCompatible`). Folding the integral
   of step 3, integrating first along `A_G` and then summing over `G(F)`, gives
   `R(β)w(x) = ∫_{[G]} K(x, y) w(y) dy` with `K(x, y) = ∑_{δ ∈ G(F)} β^♭(x⁻¹ δ y)` and
   `β^♭(h) = ∫_{A_G} β(a h) da` (`A_G` is central). `R(β)w` is left invariant under `A_G G(F)`, `K`
   is so in each variable, and every class of `[G]` has representatives in
   `G(𝔸)^1`; take `x, y ∈ G(𝔸)^1`. If `β(a x⁻¹ δ y) ≠ 0`, then `a` lies in the image `A_C` of
   `C = supp β` under the projection `G(𝔸) → A_G`, a compact set, and `x⁻¹ δ y` lies in the
   compact set `C' = A_C⁻¹ C`. Hence
   `|K(x, y)| ≤ ‖β‖_∞ vol(A_C) · #{δ ∈ G(F) : x⁻¹ δ y ∈ C'} ≤ c ‖x‖^r`
   uniformly in `y`, by Mœglin–Waldspurger I.2.4 (a)(i) for `C'`; this is the passage from the
   sum over `G(k)` to the integral over `G(k) Z_G` in the proof of I.2.4 (a)(ii). By the same
   folding, `∫_{[G]} |K(x, y)| dy ≤ ‖β‖_{L¹(G(𝔸))}`. The Cauchy–Schwarz inequality, applied to
   `|K| |w| = |K|^{1/2} · |K|^{1/2} |w|`, gives for `x ∈ G(𝔸)^1`
   `|R(β)w(x)|² ≤ ∫_{[G]} |K(x, y)| dy · sup_y |K(x, y)| · ‖w‖₂² ≤ c ‖β‖_{L¹} ‖x‖^r ‖w‖₂²`.
   A general `x ∈ G(𝔸)` is `a x₁` with `a ∈ A_G` and `x₁ ∈ G(𝔸)^1`, and
   `R(β)w(x) = R(β)w(x₁)`; Mœglin–Waldspurger I.2.2 (i) and (viii) give
   `‖x₁‖ ≤ c'' ‖x‖^{1/t}`. It remains to compare `‖x‖` with the norm defined by `rho`. Let `N`
   be the rank of `rho`; the proposition allows every `N : ℕ`.
   - *`N > 0`.* Mœglin–Waldspurger's height `‖·‖` (I.2.2) is defined by the embedding
     `i_G : G → SL_{2n}` of their I.1.1, and its rank `M = 2n` can be taken positive (`n ≥ 1`).
     This height is bounded by `RepresentationGrowth.adelicSourceNorm` of the matrix
     representation `i_G`, whose normalized local factors are the maxima of the entries of `g`
     and of `g⁻¹`. `RepresentationGrowth.closedImmersionAdelicHeightDomination`, applied with
     `0 < N`, `0 < M` and the closedness of `rho`, bounds the adelic height of `i_G` by a
     constant times a natural power of `RepresentationGrowth.adelicHeight F G rho`. For a
     representation of positive rank `d`, `adelicHeight` is `adelicSourceNorm` times the
     positive constant `d ^ (∑_v mult v)`
     (`RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm`). So
     `|R(β)w(x)| ≤ C · adelicSourceNorm F G rho x ^ s` for some `C > 0` and `s ≥ 0`, which is
     `HasModerateGrowthFunction F G rho`.
   - *`N = 0`.* The height comparison above does not apply, and none is needed. The group
     `GL_0(𝔸)` has one element. Since `rho` is a closed embedding, the induced map
     `G(𝔸) → GL_0(𝔸)` is injective (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`), so
     `G(𝔸)` is a single point. Then `R(β)w` takes a single value `v`, and
     `|R(β)w(x)| ≤ (|v| + 1) · adelicSourceNorm F G rho x ^ 0` with real exponent `0`. This is
     `HasModerateGrowthFunction F G rho` with constant `|v| + 1 > 0` and exponent `0`.
5. *Representatives.* Let `ψ` and `ψ_i` be the functions of step 3 for `w = P_V f` and
   `w = P_V f_i`; by step 2 they represent `P_V f` and `P_V f_i`, and by step 4 they have
   moderate growth. Two continuous left `A_G G(F)`-invariant functions that agree almost
   everywhere on `[G]` agree everywhere, because the projection `G(𝔸) → [G]` is open and the
   canonical measure is positive on nonempty open sets
   (`RestrictionSplitCentre.canonicalMeasure_isOpenPosMeasure`). Applied to `ψ(· l)` and `ψ`,
   `l ∈ L` (both represent `P_V f = R(l) P_V f`), this gives the right invariance of `ψ` under
   `L`; applied to `ψ(· k)` and `∑ a_i(k) ψ_i` (which represent `R(k) P_V f` and
   `∑ a_i(k) P_V f_i`), it gives `ψ(g k) = ∑ a_i(k) ψ_i(g)`, so every `k ↦ ψ(g k)` lies in `E` and
   `ψ` is `K_∞`-finite.
6. *Centre.* For `z ∈ J`, differentiating under the integral gives `z(R(β)w) = R(β_z)w` with
   `β_z` again smooth and compactly supported (as in the proof of Getz–Hahn Corollary 6.2.5),
   and `R(β_z) f = 0` since `R(β_z)φ = z(R(β)φ) = zφ = 0`. So `zψ` represents
   `R(β_z) P_V f = P_V R(β_z) f = 0`, and `zψ = 0` by continuity.

No growth condition is assumed on `φ`: square integrability on `[G]` suffices for step 4. For
`V = L²([G])` the proposition says that a smooth left `A_G G(F)`-invariant function of a fixed
type that is square integrable on `[G]` has moderate growth. This compares with
Borel–Jacquet §4.3 (ii), which assumes a central character of `Z(𝔸)/Z(F)`, `Z` the greatest
`F`-split torus of the centre of `G`, and with the Remark after Mœglin–Waldspurger I.2.5, Lemma.
The argument above does not need a central character: it divides by `A_G` instead.

## Proved results

### The parabolic `P = G`

The following two theorems take a presented parabolic `p : P → G` with
`r : ParabolicRootPresentation p l a` and `IsIso p`, for a connected reductive `G`.

- `parabolicQuotientSubgroup_eq_rationalSubgroup_of_isIso hG r hU`: with
  `hU : LeviSubgroup.IsGeometricUnipotentRadical iU`,
  `parabolicQuotientSubgroup F p iU l = rationalSubgroup F G`, that is `U(𝔸) M(F) = G(F)`.
  Proof: `l` is an isomorphism (`IsRationalLeviSubgroup.isIso_of_isIso_parabolic`) and `P` is
  connected reductive (`IsConnectedReductive.of_iso`). Its trivial unipotent radical
  (`hasTrivialUnipotentRadical`, applied to the fields of `hU.1`) gives
  `SubgroupFunctor.range iU = ⊥`, so the image of `U(𝔸)` is trivial. The image of `M(F)` is
  `G(F)`: it lies in `G(F)` (`rationalImage_le_rationalSubgroup`), and every rational point of
  `G` is the image of its transport by `inv (l ≫ p)` (`map_rational_affinePointsTarget`). The
  proof follows that of the Library theorem `StandardParabolicFamily.parabolicQuotientSubgroup_top`.
- `isLeftInvariantUnder_canonicalSubgroup_of_isIso hG r hφ`: for `φ` with
  `IsSplitComponentEquivariant p l φ` (Lapid's `A^n_P` condition), `φ` is left invariant under
  `RestrictionSplitCentre.canonicalSubgroup F G`. Proof: for `x ∈ A_G`, its transport `y` by
  `inv (l ≫ p)` lies in `A_M` (`RestrictionSplitCentre.map_mem_canonicalSubgroup`), and
  `p(l(y)) = x`. Writing `y` as the image of a point `t` of the canonical split torus of `M`
  (`canonicalSubgroup_eq_imageSubgroup`), `l(y)` is the image of `t` under
  `canonicalComponent F M ≫ l`, which is central after composition with `p` (centrality of a
  split component, transported along the isomorphism `l ≫ p` by `IsCentral.comp_iso`). So
  `parameterPower_halfModulus_map_of_isCentral` gives `l(y)^{ρ_P} = 1`, and the `A^n_P`
  condition at `y` reads `φ(x g) = φ(g)`.

### Linear combinations

- `functionInfiniteSlice_sum`: the infinite slice of `y ↦ ∑ j, c j * v j y` at `b` is
  `∑ j, c j • functionInfiniteSlice F G (v j) b` (pointwise computation).
- `isAdelicSmoothFunction_sum`: finite linear combinations of functions with
  `IsAdelicSmoothFunction` have it. Continuity is preserved by finite sums; the slices form a
  submodule (`plotSmoothFunctions` is a `Submodule`); the level is the intersection `⨅ j, L j`
  of the levels, open as a finite intersection of open sets.
- `isInfiniteSubgroupFiniteFunction_sum`: finite linear combinations of `K_∞`-finite functions
  are `K_∞`-finite: the span of the right translates of the combination lies in the supremum of
  the finitely many finite-dimensional spans of the right translates of the terms.
- `finiteDimensional_span_infiniteSlices`: for a `K_∞`-finite `φ`, the span of the functions
  `k ↦ φ(g k)`, `g ∈ G(𝔸)`, is finite-dimensional. Proof: with `S` the finite-dimensional span of
  the right translates `φ(· k)`, the linear map `Ψ : Module.Dual ℂ S → (K_∞ → ℂ)`,
  `ℓ ↦ (k ↦ ℓ(φ(· k)))`, sends evaluation at `g` to `k ↦ φ(g k)`; so the span lies in the range
  of `Ψ`, which is finite-dimensional.
- `finite_quotient_iInf`: for ideals `J j`, `j : Fin k`, of a commutative `ℂ`-algebra, each of
  finite codimension, `⨅ j, J j` has finite codimension. Proof: it is the kernel of the linear map
  to `∏ j, Z ⧸ J j`, whose target is finite-dimensional; the induced map on the quotient is
  injective (`Submodule.ker_liftQ_eq_bot`, `Module.Finite.of_injective`).
- `exists_combination_type`: a finite linear combination `φ = ∑ j, c j · v j` of functions
  satisfying `IsAutomorphicFunctionOn` (for any subgroup `Γ`) has a type `(J, L, E)`: `J` is the
  intersection of annihilating ideals of the terms, `L` the intersection of their levels, and
  `E` the span of the functions `k ↦ φ(g k)`. The annihilation by `J` uses
  `functionInfiniteSlice_sum` and the linearity of `plotSmoothCenterAction F G hsmooth hcalc z`.

### `L²` classes

- `exists_finiteDimensional_of_ae_eq m o hS`: for a measure `m` on `X`, a map `o : X → Y` and a
  finite-dimensional space `S` of functions `Y → ℂ`, there is a finite-dimensional subspace `W` of
  `Lp ℂ 2 m` containing every class `x` with `x =ᵐ[m] fun y => ψ (o y)` for some `ψ ∈ S`.
  Proof: the functions `ψ ∈ S` with `y ↦ ψ (o y)` in `L²` form a subspace `T ≤ S`; `W` is the
  range of the linear map `T → Lp ℂ 2 m` taking the class (`MemLp.toLp`). A class `x` as above
  makes `y ↦ ψ (o y)` square integrable (`MemLp.ae_eq`) and equals its image (`Lp.ext`).

### The reduction

`squareIntegrableFormFiniteProjection_of_reduction hHC hB`: with
`hHC : ParabolicHarishChandraFinitenessStatement.{0}` and
`hB : SquareIntegrableProjectionAutomorphyStatement`, the statement
`SquareIntegrableFormFiniteProjectionStatement` holds. Proof (as implemented): introduce the data,
the instance `LocallyOfFiniteType P.X.hom`, `IsIso p` and `Smooth G.X.hom`.

1. By `parabolicQuotientSubgroup_eq_rationalSubgroup_of_isIso`, each `v j` satisfies
   `IsAutomorphicFunctionOn` for `G(F)` (the first component of
   `IsSquareIntegrableInducedForm`).
2. `exists_combination_type` gives a type `(J, L, E)` of `φ = ∑ j, c j · v j`. The function `φ` is
   left invariant under `G(F)` (from the terms), under `A_G` (from
   `isLeftInvariantUnder_canonicalSubgroup_of_isIso` and the `A^n_P` component of
   `IsSquareIntegrableInducedForm`), and smooth (`isAdelicSmoothFunction_sum`).
3. `hHC`, applied to `q = p`, `iV = iU`, `l' = l`, with `r.isCompatible.parabolic`,
   `r.isCompatible.levi`, `hU`, `hK` and the multiplication isomorphism
   `ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical`, gives that the span `S`
   of the automorphic functions on `U(𝔸) M(F) \ G(𝔸)` of type `(J, L, E)` is finite-dimensional.
   `exists_finiteDimensional_of_ae_eq`, with `o = Quotient.out`, gives a finite-dimensional
   `W ≤ L²([G])`.
4. For a closed invariant `V`, `hB` applied to `φ` and `f` gives `ψ` with
   `V.starProjection f =ᵐ fun y => ψ y.out`. Since `U(𝔸) M(F) = G(F)`, `ψ` lies in `S`, so
   `V.starProjection f ∈ W`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

- Proved: the implication from `ParabolicHarishChandraFinitenessStatement` and
  `SquareIntegrableProjectionAutomorphyStatement` to `SquareIntegrableFormFiniteProjectionStatement`,
  including, for a presented parabolic that is an isomorphism, `U(𝔸) M(F) = G(F)` and the
  `A_G`-invariance of `A^n_P` functions, and the closure of smoothness, `K_∞`-finiteness and
  types under finite linear combinations.
- Not proved here: `ParabolicHarishChandraFinitenessStatement` and
  `SquareIntegrableProjectionAutomorphyStatement`. The integrability component of
  `IsSquareIntegrableInducedForm` is not used: square integrability of `φ` on `[G]` enters only
  through `f ∈ L²([G])`.
