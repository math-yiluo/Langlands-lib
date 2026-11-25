# The Rao function

**GKT §4.5** (pp. 121–131): (4.15), **Lemma 4.35**, **Corollary 4.36**, **Definition 4.37**,
**Lemma 4.38**, **Lemma 4.40**, **Proposition 4.41**, **Corollary 4.42**, **Lemma 4.44**,
**Lemma 4.45**; and **Lemma 4.29** of §4.4.1 (p. 116).

The module `Langlands.Theta.Metaplectic.RaoFunction` treats a commutative `D = E`: a field `K` with
an involution `τ` (`τ = id`: `D = E = F`; `τ ≠ id`: a quadratic extension `E/F`), so that the
reduced norm is the determinant and `r = 1`. `h` is a non-degenerate `-ε`-Hermitian form on a
finite-dimensional `K`-space `V` (the book's `W`), `X` a Lagrangian, `P = P(X)`, `e` a standard basis
with `X = span {eᵢ}` (`e.lagrangianFst`) and `w_S = e.weylElement S`. `[NeZero (2 : K)]` is assumed
from the definition of the Rao function on (the Bruhat decomposition uses five-term decompositions).
The quaternionic case is not treated.

## Content

- `siegelRestrict h X : P(X) →* (X ≃ₗ[K] X)`, `p ↦ p|_X`, and `siegelDet h X : P(X) →* Kˣ`,
  `p ↦ det(p|_X)` (`coe_siegelDet`); `pairing h A B : A →ₗ[K] B →ₛₗ[τ] K`, `(a, b) ↦ h a b`.
- **Lemma 4.29**: `siegelDet_mul_conj_siegelDet` — for `g ∈ P(X) ∩ P(Y)` with `V = X ⊕ Y` a
  polarization, `det(g|_Y) · det(g|_X)^τ = 1` (`det_mul_conj_det_eq_one` of `Determinant.lean`).
- **Lemma 4.35**: `exists_siegelDet_mul_siegelDet_eq` — if `p₁ g p₂ = g` with `p₁, p₂ ∈ P(X)`, then
  `p₁` preserves `K₀ = X ∩ g X` and `det(p₁|_X) det(p₂|_X) = det(q) det(q)^τ` for the map `q`
  induced by `p₁` on `X/K₀`. Proof: `p₁ = g p₂⁻¹ g⁻¹` preserves `gX`, so `det(p₂|_X) = det(p₁|_{gX})⁻¹`;
  `det(p₁|_X)` and `det(p₁|_{gX})` split off the same factor `det(p₁|_{K₀})`
  (`LinearMap.det_eq_det_mul_det`); the quotients `X/K₀`, `gX/K₀` are in non-degenerate duality
  through `h` (`LinearMap.liftQ₂`), and `det_mul_conj_det_eq_one` applies.
- **Corollary 4.36**: `mk_siegelDet_mul_siegelDet_eq` (for any `w ∈ G`, `p₁ w p₂ = p₁' w p₂'` gives
  `det(p₁ p₂|_X) ≡ det(p₁' p₂'|_X)` modulo norms) and `StandardBasis.raoFunction_eq` (every
  decomposition `g = p₁ w_S p₂` computes the Rao function). For two subsets of the same size,
  `w_S` and `w_{S'}` are conjugate under `P` (`exists_weylElement_eq_conj`, through the reindexed
  standard basis: `reindex_fst`, `reindex_snd`, `lagrangianFst_reindex`, `weylElement_reindex`).
- **Definition 4.37**: `StandardBasis.raoFunction e : h.isometryGroup → Kˣ ⧸ normSubgroup τ`,
  `x(g) = det(p₁ p₂|_X)` for the decomposition chosen by the Bruhat decomposition
  (`exists_mem_doubleCoset` of `Bruhat.lean`).
- **Lemma 4.40**: `raoFunction_mul_mul : x(p₁ g p₂) = x(p₁) x(g) x(p₂)`,
  `raoFunction_of_mem : x(p) = det(p|_X)`, `raoFunction_weylElement : x(w_S) = 1`, and
  `raoFunction_inv : x(g⁻¹) = x(g)⁻¹ (-ε)^{|S|}` for `g ∈ P w_S P` (from `w_S² = -ε` on `W_S`:
  `weylElement_mul_self_fst`, `weylElement_mul_self_mem`, `coe_siegelDet_weylElement_mul_self`).
- **Lemma 4.44** and **Lemma 4.38**: `raoFunction_conj` — for two standard bases `e, f` (same index
  type) and the isometry `π : eₖ ↦ fₖ` (`IsometryEquiv.toIsometryGroup`, `weylElement_eq_conj`:
  `w^f_S = π w^e_S π⁻¹`, `map_isometryEquiv_lagrangianFst`), `x_f(π g π⁻¹) = x_e(g)`; this is
  Lemma 4.44 with `α = π`. `raoFunction_eq_of_lagrangianFst_eq`: if `e, f` span the same `X`, then
  `x_e = x_f` (Lemma 4.38).
- **Proposition 4.41**: `raoFunction_mul` — if `g₁ ∈ P w_{S₁} P`, `g₂ ∈ P w_{S₂} P`,
  `g₁ g₂ ∈ P w_S P` and `ρ = L(X, g₁⁻¹ X, g₂ X)`, then there is `t : ℕ` with
  `|S₁| + |S₂| + dim ρ = |S| + 2t` and `x(g₁ g₂) = x(g₁) x(g₂) (-ε)^t det(ρ)`.
  Proof: by Theorem 4.31, `g₁ = p₁ κ₁ p⁻¹`, `g₂ = p κ₂ p₂⁻¹`, so it comes down to
  `x(κ₁ κ₂) = (-ε)^{|T₁| + |T₄|} det(Y_{T₄}, (-, -)_b)` (private `raoFunction_kappa`). Instead of the
  book's factorization (4.17), `κ₁ κ₂ = n(c) w_{T₂ ∪ T₃ ∪ T₄} q` (private `exists_kappa_eq`), where
  `n(c)` carries `Y` to the Lagrangian `κ₁ κ₂ w_{T₂ ∪ T₃ ∪ T₄} Y`, a complement of `X` because
  `b(Y_{T₄}) = X_{T₄}`; `q ∈ P` acts on `X` by `-ε` on `X_{T₁}`, by `x ↦ -ε b(x*)` on `X_{T₄}` and
  trivially elsewhere, and `det(q|_X)` is computed by splitting off `w_{T₁}²` and restricting to
  `X_{T₄}` (private `coe_siegelDet_of_apply`, `det_eq_det_restrict_of_sub_mem`; the matrix of
  `x ↦ b(x*)` in the basis `(eᵢ)` is the transpose of the Gram matrix of `(-, -)_b` in `(eᵢ*)`).
- **Corollary 4.42**: `raoFunction_mul_of_det_eq_one` — if `-ε = 1` and all Leray invariants have
  trivial determinant, `x` is a homomorphism.
- **§4.5.7, Lemma 4.45**: for `a ≠ 0` with `a^τ = s a` (`s = ±1`), `scale h a s ha` is the form
  `a h` (the book's `W^a`), `-(ε s)`-Hermitian (`scale_apply`); its isometry group is that of `h`
  (`isometryGroup_scale`, the identification `toScaleIsometryGroup`); `StandardBasis.scale` is the
  standard basis `{eᵢ} ∪ {(a^τ)⁻¹ eᵢ*}` of `W^a` (the book's `{eᵢ} ∪ {eᵢ* (1/a)}`; `scale_fst`,
  `scale_snd`, `lagrangianFst_scale`), and `raoFunction_scale`: for `g ∈ P w_S P`,
  `x_a(g) = x(g) (a^τ)^{-|S|}` modulo norms (`≡ x(g) a^{|S|}`). Proof: `w^a_S = d w_S` with `d ∈ P`
  acting by `a^τ` on `X_S` and trivially on the other `eᵢ`. In the book's convention the same lemma
  reads `x_a(g) = x(g) a^{-r|S|}`; the two agree through `x = τ(x_book)`.
- Tools: `signUnit K u` (a sign as a unit of `K`), `basisFst`, `blockFstBasis`, `blockSndBasis`
  (the bases `(eᵢ)` of `X` and `X_A`, `(eᵢ*)` of `Y_A`), `basisFst_repr`, `blockFstBasis_repr`
  (coordinates are read off with the `eᵢ*`), `det_eq_prod_of_apply_basisFst`,
  `siegelDet_eq_one_of_mem_siegelUnipotent`.

## Conventions

The determinant is Mathlib's on the left space `V`. Under the dictionary of Proposition B.6 the
matrix of an endomorphism of the book's right space `W` in a basis is `τ` of its matrix on `V`, so
this `x` is `τ` of the book's `x`, which is `≡ x_book⁻¹` modulo `𝒩(E^×)` (for `τ = id` the two agree;
the Library's unitary block has `χ^{Lib} = (χ^{book})⁻¹`,
`lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic` of
`Langlands.Theta.DualPair.Unitary.StandardOperator`). Gram matrices, and hence
`det(ρ)`, are the same in both conventions.

## Remarks on the book's text

- **Proposition 4.41 and Lemma 4.34.** In the book's conventions (right spaces, forms
  `τ`-semilinear in the first variable, Remark B.5) one has `det(ρ) = det(b)^τ`, not `det(b)` as
  Lemma 4.34 says (`⟨b eᵢ*, eⱼ*⟩ = b_{ji}^τ`). Correspondingly Proposition 4.41 as printed holds for
  the convention used here, while in the book's own convention its factor should be
  `(-ε)^{rt} ε^{r dim ρ} det(ρ)`. The two differ only when `ε = -1` and `r · dim ρ` is odd, that is
  for unitary groups of Hermitian spaces (`τ ≠ id`). Example: `W` Hermitian of dimension 2,
  `g₁ = w`, `g₂ = n(b) w` with `b e* = e β`, `β^τ = -β`: the book's `x(g₁ g₂)` is `β` and
  `det(ρ) = -β`.
- **Proof of Proposition 4.41.** The book's count `|S| = |T₁| + |T₂| + |T₄|` should read
  `|S| = |T₂| + |T₃| + |T₄|` (`g₁ g₂ ∈ P w_{T₂ ∪ T₃ ∪ T₄} P`); with it the identity
  `|S₁| + |S₂| - |S| + |T₄| = 2(|T₁| + |T₄|)` holds.
- **Lemma 4.35.** It says that `p₁` preserves `ker(c) = X ∩ g⁻¹X`. From `p₁ g p₂ = g`,
  `p₁ = g p₂⁻¹ g⁻¹` preserves `X ∩ gX`, and it is `p₂` that preserves `X ∩ g⁻¹X` (for `g = w_S` the two
  spaces coincide, which is the case the book computes). The lemma is proved here with `X ∩ gX`, by a
  coordinate-free argument instead of block matrices and the commutative diagram.

## Not done here

- The quaternionic case (`r = 2`, reduced norm on `M_n(D)`, §4.1.2).
- Remark 4.39 and Remark 4.43 (the other convention `w'_S`), and the examples of Corollary 4.42
  (symmetric `W`, quaternionic skew-Hermitian `W`).
- The Rao function is defined relative to a standard basis; Lemma 4.38 shows that it depends only on
  `X` (for bases indexed by the same type).

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.1.2,
  Lemma 4.2, pp. 95–96; Remark B.5 and Proposition B.6, p. 611; §4.4.1, Lemma 4.29, p. 116; §4.4.3,
  Theorem 4.31, pp. 119–121; §4.5, (4.15), Lemmas 4.34, 4.35, Corollary 4.36, Definition 4.37,
  Lemma 4.38, pp. 121–126; Lemma 4.40, Proposition 4.41, Corollary 4.42, pp. 127–129; Lemma 4.44,
  p. 130; §4.5.7, Lemma 4.45, pp. 130–131.

## Declarations

In `Langlands.EpsilonHermitianForm`: `siegelRestrict`, `siegelRestrict_apply`, `siegelDet`,
`coe_siegelDet`, `pairing`, `pairing_apply`, `siegelDet_mul_conj_siegelDet`,
`exists_siegelDet_mul_siegelDet_eq`, `mk_siegelDet_mul_siegelDet_eq`,
`IsometryEquiv.toIsometryGroup`, `IsometryEquiv.toIsometryGroup_apply`, `signUnit`, `coe_signUnit`,
`signUnit_one`, `signUnit_inv`, `scale`, `scale_apply`, `isometryGroup_scale`,
`toScaleIsometryGroup`, `coe_toScaleIsometryGroup`.

In `Langlands.EpsilonHermitianForm.StandardBasis`: `weylElement_eq_conj`,
`map_isometryEquiv_lagrangianFst`, `reindex_fst`, `reindex_snd`, `lagrangianFst_reindex`,
`weylElement_reindex`, `exists_weylElement_eq_conj`, `basisFst`, `basisFst_apply`, `blockFstBasis`,
`blockFstBasis_apply`, `blockSndBasis`, `blockSndBasis_apply`, `basisFst_repr`, `blockFstBasis_repr`,
`det_eq_prod_of_apply_basisFst`, `weylElement_mul_self_fst`, `weylElement_mul_self_mem`,
`coe_siegelDet_weylElement_mul_self`, `siegelDet_eq_one_of_mem_siegelUnipotent`, `raoFunction`,
`raoFunction_eq`, `raoFunction_mul_mul`, `raoFunction_of_mem`, `raoFunction_weylElement`,
`raoFunction_inv`, `raoFunction_conj`, `raoFunction_eq_of_lagrangianFst_eq`, `raoFunction_mul`,
`raoFunction_mul_of_det_eq_one`, `scale`, `scale_fst`, `scale_snd`, `lagrangianFst_scale`,
`raoFunction_scale`.

Private: `exists_equiv_map_eq`, `exists_raoFunction_eq`, `kappa`, `mem_filter_iff`, `nb_snd`,
`nb_fst`, `kappa_fst_zero`, `kappa_fst_one`, `kappa_fst_two`, `kappa_fst_three`, `kappa_fst_four`,
`kappa_snd_zero`, `kappa_snd_one`, `fin_five_cases'`, `exists_kappa_eq`,
`det_eq_det_restrict_of_sub_mem`, `coe_siegelDet_of_apply`, `raoFunction_kappa`, `mul_one_mul`,
`comm_aux`, `card_filter_or₃`, `mul_one_mul_one`.

## Dependencies

- `Langlands.Group.Classical.Bruhat`, `Langlands.LinearAlgebra.EpsilonHermitian.Determinant`.
- Mathlib: `LinearAlgebra.Quotient.Bilinear`, `Tactic.LinearCombination`.
