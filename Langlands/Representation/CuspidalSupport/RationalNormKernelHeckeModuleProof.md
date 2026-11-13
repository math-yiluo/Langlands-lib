# Proof of Renard VI.4.2 (after the Proposition): right H(G, ρ)-modules and the adjunction

Module `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeModuleProof`.
Author: Worker 130 (task `31647676-0fa8-4bfb-984c-ad3601495dfe`).

`Langlands.CuspidalSupport.rationalNormKernelHeckeModule` proves the published
`Langlands.CuspidalSupport.RationalNormKernelHeckeModuleStatement.{uF, uV}` for arbitrary
universes. Source: David Renard, *Représentations des groupes réductifs p-adiques*,
VI.4.2, the paragraphs after the Proposition, printed pp.152–153 / PDF pp.158–159
(registered source `renard-2026-representations-groupes-reductifs-padiques`). The proof
adds no hypothesis.

## Structure

The module first proves general lemmas in namespace
`Langlands.CuspidalSupport.NormalHecke`, in the setting of the published module
`NormalSubgroupHecke`: G is a topological group, H an open normal subgroup
(`hH : IsOpen (H : Set G)`, `[H.Normal]`), ρ a smooth representation of H and τ a smooth
representation of G. The final theorem applies them with H = `rationalCommonNormKernel G`.
The published `isOpen_rationalCommonNormKernel` gives openness and the published instance
`rationalCommonNormKernel_normal` gives normality. The statement's `rationalNormKernelHecke G ρ`
and `rationalNormKernelConvolution G ρ` are definitionally the published `heckeSubmodule H ρ`
and `heckeConvolution H ρ`, as in the published proof `rationalNormKernelHecke_equiv`.

Notation: f_w = `unitFunction … w` is the function supported on H with f_w(1) = w. For an
H-map ψ : ρ → Res τ, s₀(ψ) = `SmoothRep.ofHom (cosetSum H hH τ ρ ψ)` is the published
coset sum of `Induction.OpenAdjunction`, s₀(ψ)(v) = ∑_{Hx ∈ H\G} τ(x⁻¹) ψ(v(x)). The
published `cosetSum_comp_unitMap` gives s₀(ψ)(f_w) = ψ(w).

### Definition

- `heckeRightAction H ρ τ ψ φ w = ∑ᶠ q : G ⧸ H, τ(q.out) (ψ (φ(q.out⁻¹) w))`. This is
  literally the statement's `act ψ φ w`. The name was chosen to avoid the existing
  `Hecke.heckeAction`.

### General lemmas

1. `hom_eq_cosetSum_restrict`: every G-map s : ind_H^G ρ → τ equals the coset sum of its
   restriction w ↦ s(f_w). Proof: the published decomposition `cosetSum_unitMap` writes
   v as the coset sum of the unit map. `cosetSum_resIntertwining_comp` moves s inside the
   sum. This is Renard's (VI.4.2.2) applied under s.
2. `cosetSum_eq_finsum_inv` (needs H normal): the coset sum is the formula (VI.4.2.6),
   s₀(ψ)(v) = ∑ᶠ_{q ∈ H\G} τ(q.out) ψ(v(q.out⁻¹)). Put Ψ(x) = τ(x⁻¹) ψ(v(x)). Ψ is left
   H-invariant by the H-equivariance of v and ψ (`eval_mul_left`). It is also right
   H-invariant, since x h = (x h x⁻¹) x with x h x⁻¹ ∈ H by normality. The published
   reindexing `finsum_leftQuotient_mul_inv` at x = 1 turns ∑ Ψ(q.out) into
   ∑ Ψ(q.out⁻¹). That sum is the right-hand side.
3. `hom_apply_eq_finsum`: if ψ(w) = s(f_w) for all w, then s(v) is given by (VI.4.2.6).
   This combines 1 and 2.
4. `hom_comp_unitFunction`: let α ∈ End(ind_H^G ρ) and φ : G → End ρ with
   α(f_w)(g) = φ(g)(w). If ψ(w) = s(f_w) for all w, then (α ≫ s)(f_w) = (ψ · φ)(w). Proof:
   by 3, (α ≫ s)(f_w) = s(α(f_w)) = ∑_{q ∈ H\G} τ(q.out) ψ(φ(q.out⁻¹) w). The summand
   Φ(g) = τ(g) ψ(φ(g⁻¹) w) is right H-invariant because φ(h g)(u) = ρ(h)(φ(g)(u)) (from
   the H-equivariance of α(f_u)) and ψ is an H-map. The published `finsum_leftQuotient_eq`
   then replaces the sum over H\G by the sum over G ⧸ H.

### The five clauses of the statement

- **Clause 1, `exists_heckeRightAction`.** Given ψ and φ ∈ H(G, ρ), the map
  ψ' : w ↦ (e⁻¹(φ) ≫ s₀(ψ))(f_w) is an H-map. It is built as
  `(resIntertwining …).comp (unitMap …)`. Lemma 4 with α = `endOfHecke H ρ hH φ` (the
  published inverse of the Hecke identification) gives ψ'(w) = (ψ · φ)(w). The hypothesis
  of lemma 4 is the published `endValue_endOfHecke`.
- **Clause 2, associativity, `heckeRightAction_heckeRightAction`.** Write φ = e(α) and
  φ' = e(β) with e = `heckeEquiv H ρ hH` (surjective; ρ is irreducible). Let s₀ = s₀(ψ).
  Lemma 4 for α and s₀ shows that ψ' (with ψ'(w) = (ψ · φ)(w)) satisfies
  ψ'(w) = (α ≫ s₀)(f_w). Lemma 4 applied twice more rewrites both sides:
  (ψ' · e(β))(w) = (β ≫ (α ≫ s₀))(f_w) and (ψ · e(α * β))(w) = ((α * β) ≫ s₀)(f_w).
  The published `heckeEquiv_mul` identifies e(α * β) with the convolution e(α) ∗ e(β).
  Since α * β = β ≫ α in `End` (`End.mul_def`), associativity of composition
  (`Category.assoc`) closes the goal. The hypotheses of lemma 4 for e(α) are the
  definitional value formula `heckeEquiv_apply`.
- **Clause 3, unit, `heckeRightAction_unit`.** Let φ_e be ρ on H and 0 off H. The term at
  q = 1 is τ(g) ψ(ρ(g⁻¹) w) with g = (1 : G ⧸ H).out ∈ H. Since ψ is an H-map this equals
  τ(g) τ(g⁻¹) ψ(w) = ψ(w). For q ≠ 1, q.out⁻¹ ∉ H, so φ_e(q.out⁻¹) = 0 and the term
  vanishes (`finsum_eq_single`). This clause uses neither openness nor irreducibility.
- **Clause 4, A-linearity of the adjunction.** For any linear equivalence e with
  e(α)(g)(w) = α(f_w)(g), lemma 4 with α = e⁻¹(φ) gives
  (e⁻¹(φ) ≫ s)(f_w) = (ψ_s · φ)(w). The needed value formula
  e⁻¹(φ)(f_w)(g) = φ(g)(w) follows from the hypothesis on e and `e.apply_symm_apply`.
- **Clause 5, bijectivity with inverse (VI.4.2.6), `existsUnique_hom_unitFunction`.**
  Existence: s₀(ψ) satisfies s₀(ψ)(f_w) = ψ(w) (`cosetSum_comp_unitMap`) and the formula
  (VI.4.2.6) (lemma 2). Uniqueness: if s(f_w) = ψ(w) for all w, lemma 3 and lemma 2 give
  s(v) = s₀(ψ)(v) for every v. Hence s = s₀(ψ) by extensionality of intertwining maps
  (`SmoothRep.ofHom_hom`).

## Relation to the source

Renard states these facts for an irreducible summand ρ of Res π with π supercuspidal. The
Lean proof uses only that ⁰G is open and
normal in G(F) and that ρ is irreducible; irreducibility enters only through the
published `heckeEquiv` and `heckeEquiv_mul`, in clause 2. Admissibility, finite
dimensionality and countability are not used. The right action is shown through the
transported action on `Hom_G(Π, τ)` (lemma 4), not by direct manipulation of the double
sum. This route differs from a direct computation, but proves exactly the stated clauses.
