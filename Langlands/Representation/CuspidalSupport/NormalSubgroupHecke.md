# The Hecke space of an open normal subgroup

Author: Worker 1789.

This is a supporting module for the proof of Renard's VI.4.2 Proposition
(`RationalNormKernelHeckeProof`). It is written for an arbitrary topological
group G, an open normal subgroup H and an irreducible smooth complex
representation ρ of H, in namespace `Langlands.CuspidalSupport.NormalHecke`.
The proof module then sets G = G(F) and H = ⁰G. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.2, printed
pp.151–152 / PDF pp.157–158. Renard's computation uses only that ⁰G is open and
normal, so it works for any open normal H. The declarations here are internal
helpers; their content comes from that computation.

## Definitions

- `heckeSubmodule H ρ`: the functions φ : G → `Module.End ℂ ρ` with
  φ(h g h') = ρ(h) φ(g) ρ(h') for h, h' ∈ H, whose support has finite image in
  G ⧸ H. This is Renard's H(G,ρ) (VI.4.2.1) with H in place of ⁰G. For
  H = ⁰G it is definitionally the published `rationalNormKernelHecke G ρ`.
- `heckeConvolution H ρ φ ψ`, the function
  x ↦ ∑ᶠ_{q ∈ G ⧸ H} φ(q.out) ψ(q.out⁻¹ x). For H = ⁰G it is definitionally
  the published `rationalNormKernelConvolution G ρ`.
- `inducedRep H ρ`: the published `compactInductionFunctor H` applied to ρ.
- `endValue H ρ hH α g`: the endomorphism w ↦ α(f_w)(g) of ρ. Here f_w is the
  published `unitFunction` (supported on H, f_w(h) = ρ(h) w) and `hH` says that
  H is open.
- `heckeFunction`, `heckeMap`, `endOfHecke`: for φ in the Hecke space,
  w ↦ (x ↦ φ(x) w) is an H-equivariant map ρ → Res_H ind_H^G ρ. `endOfHecke φ` is
  its image under the published `cosetSum` of the open adjunction, which is the
  endomorphism f ↦ ∑_{Hx ∈ H\G} r(x⁻¹)·(φ(·)(f(x))).
- `heckeEquiv H ρ hH : End (inducedRep H ρ) ≃ₗ[ℂ] heckeSubmodule H ρ`, given by
  α ↦ `endValue α`, with inverse `endOfHecke`.

## Results and proofs

**Cosets.** `leftQuotientEquiv` identifies the published `LeftQuotient H`
(cosets Hx) with G ⧸ H (cosets xH). Both are quotients of G by the same
relation, because H is normal. `finite_mk_image_iff` compares the images of a
set in the two quotients. `finsum_leftQuotient_eq` turns a sum over H\G into a
sum over G ⧸ H when the summand is invariant under right multiplication by H.
`finsum_quotient_mul_inv` and `finsum_leftQuotient_mul_inv` reindex along
q ↦ x q⁻¹ when the summand is invariant on both sides.

**Irreducibility.** In an irreducible representation, an invariant subspace
that contains a nonzero vector is everything (`mem_of_isIrreducible`), and a
nonzero vector exists (`exists_ne_zero_of_isIrreducible`).
`injective_of_twisted` says that a nonzero T with T σ(k) = σ(c k) T is injective,
because its kernel is invariant. The equivalence does not use this lemma. It is
kept for the later VI.4.3 proofs.

**φ_α lies in the Hecke space.** The published equivariance of `unitMap` and of α
give α(f_{ρ(h)w})(g) = α(f_w)(g h) (`endValue_mul_right`). The covariance of
induced functions gives α(f_w)(h g) = ρ(h) α(f_w)(g) (`endValue_mul_left`).
Together they give the bi-invariance (`endValue_bi`). For the finiteness
(`endValue_finite`), pick w₀ ≠ 0. Let X be the set of cosets meeting the support
of α(f_{w₀}); it is finite by the published `quotientSupport_finite`. The vectors
w such that every g with α(f_w)(g) ≠ 0 lies in a coset of X form a subspace.
It is invariant: Hg k = Hg for k ∈ H by normality, and α(f_{ρ(k)w})(g) =
α(f_w)(g k). It contains w₀, so it is all of ρ by irreducibility. Hence the
support of `endValue α` lies in the cosets of X.

**The two maps are inverse.** The published `cosetSum_comp_unitMap` gives
`endOfHecke φ` (f_w) = (x ↦ φ(x) w), so `endValue (endOfHecke φ) = φ`
(`endValue_endOfHecke`); this is the right inverse. For the left inverse,
`end_ext` shows that two endomorphisms that agree on every f_w are equal. Every
endomorphism α is the coset sum of α ∘ `unitMap` (`hom_eq_cosetSum`, from the
published `cosetSum_unitMap`, which is Renard's decomposition (VI.4.2.2), and
`cosetSum_resIntertwining_comp`).

**Inverse formula.** `eval_endOfHecke` states
`endOfHecke φ` (v)(x) = ∑ᶠ_{q ∈ H\G} φ(q.out)(v(q.out⁻¹ x)). The coset sum is
∑_{Hy} φ(x y⁻¹)(v(y)). Evaluation at x commutes with this finite sum
(`map_finsum` with the published `hasFiniteSupport_cosetTerm`). The function
Ψ(g) = φ(g)(v(g⁻¹ x)) is invariant under left and right multiplication by H, by
the bi-invariance of φ, the covariance of v and normality. So
`finsum_leftQuotient_mul_inv` reindexes the sum along y ↦ x y⁻¹.

**Composition.** `eval_hom_eq` writes any α by the inverse formula applied to
`endValue α`. Applied to α(β(f_w))(x), it gives
∑ᶠ_{q ∈ H\G} φ_α(q.out)(φ_β(q.out⁻¹ x) w). The summand is right H-invariant, so
`finsum_leftQuotient_eq` turns it into the sum over G ⧸ H. The convolution sum
has finite support by `endValue_finite`, so evaluation at w commutes with it.
This gives `heckeEquiv_mul`: e(α * β) = `heckeConvolution` (e α) (e β), where
α * β is the composition α ∘ β.

## Scope

The equivalence needs ρ irreducible only for the finiteness of the support of
φ_α. Everything else holds for any smooth ρ.
