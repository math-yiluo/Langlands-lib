# The rank-one factorization and the rank-one exchange at a chamber point

This derived, internal unit proves the rank-one part of Kaletha–Prasad
Proposition 7.1.1(1) on the apartment of `KPApartmentData`, without AS 1, and
deduces the rank-one exchange used in the Iwahori factorization at a chamber
point (Kaletha–Prasad Proposition 7.3.12). Opposite factor pairs (the
conclusion of Kaletha–Prasad Proposition 2.11.17) are a hypothesis,
`RelativeRoot.HasRankOneFactorization i`; they are not proved here.

## Statement

`ChamberRankOneExchangeStatement` quantifies over an arbitrary-universe field
`k`, a commutative group scheme `S` and an affine group scheme `G` over
`Spec k`, a monomorphism `i : S → G`, a map `ω : kˣ → ℝ` and apartment data
`D : KPApartmentData i ω`. It assumes

- `S` is a split torus (`IsSplitTorus S.toGrp`);
- the set `Φ = relativeRoots i` of relative roots is finite;
- the rationalizations of `Φ` and of the restricted torus characters span the
  rational character space;
- every nonidentity root point has an opposite factor pair
  (`RelativeRoot.HasRankOneFactorization i`);
- AS 4 in the form: every extended affine root `ψ` of `D` satisfies
  `ψ ∈ D.affineRoots ∨ 2 • ψ ∈ D.affineRoots`.

For every chamber `C` of `D.affineRoots`, every `x ∈ C` and every `a ∈ Φ` it
concludes the set inclusion

`U_{-a,x,0} · U_{a,x,0} ⊆ U_{a,x,0} · U_{-a,x,0} · Z(k)^♯_x`,

where `U_{b,x,0}` is `D.filtration x b 0` and `Z(k)^♯_x` is
`D.sharpCentralizer {x}`. The theorem `chamberRankOneExchange` proves it.

## Supporting results

On valuations of the root datum (`IsRootDatumValuation`, from V 1 and V 5):
`apply_inv` (`φ_a(g⁻¹) = φ_a(g)`), `min_le_apply_mul` (the ultrametric
inequality), `apply_mul_eq_right_of_lt` (`φ_a(g g′) = φ_a(g′)` when
`φ_a(g′) < φ_a(g)`) and `opposite_snd` (V 5 for the second element of an
opposite pair: `φ_{-a}(u″) = -φ_a(u)`).

On the apartment (`KPApartmentData`, for a point `x` with valuation `x_b`):

- `eval_translation_eq_of_factor`: if `n = r₁ v r₂ ∈ N(k)` with
  `v ∈ U_b(k) ∖ {1}`, `r₁, r₂ ∈ U_{-b}(k)`, `n` negating `b`, and `n` moves
  `x` by the translation `w`, then `⟨b, w⟩ = -2 x_b(v)`.
- `weylAction_mul_factorPairs_eq_one`: for opposite pairs `p` of
  `v′ ∈ U_{-c}(k) ∖ {1}` and `q` of `w ∈ U_c(k) ∖ {1}`, the product
  `(q₁ w q₂)(p₁ v′ p₂)` acts trivially on characters.
- `val_conj_eq_of_eval_eq_zero`: a normalizer point acting trivially on
  characters whose translation part vanishes on `c` preserves `x_c` under
  conjugation.
- `le_val_of_mul_eq`: the depth bound `x_c(y) ≥ x_c(v)` of KP 7.1.1(1).
- `exists_rankOne_factorization` (KP 7.1.1(1) without the fixed-point
  property of `z`): for `v ∈ U_c(k) ∖ {1}`, `v′ ∈ U_{-c}(k) ∖ {1}` with
  `x_c(v) = t`, `x_{-c}(v′) = t′` and `t + t′ > 0`, there are
  `x′ ∈ U_{-c}(k)`, `z ∈ Z(k)` and `y ∈ U_c(k)` with `v v′ = x′ z y`,
  `x_{-c}(x′) ≥ t′`, `x_c(y) ≥ t`, and `x_c(z g z⁻¹) = x_c(g)` for all `g`.
- `filtration_le_sharpFixer`: `U_{b,x,0} ≤ G(k)^♯_x`.
- `filtration_neg_mul_filtration_subset`: the exchange inclusion above, with
  `-a ∈ Φ` as an explicit hypothesis.
- `neg_mem_relativeRoots_of_rankOne`: with opposite factor pairs, `a ∈ Φ`
  implies `-a ∈ Φ`.

## Proof

*Rank-one factorization.* Let `(p₁, p₂)` be the opposite pair of `v′`, so
`m = p₁ v′ p₂ ∈ N(k)` and, by V 5, `x_c(p₁) = -t′`. Then `w = v p₁⁻¹ ∈ U_c(k)`
has `x_c(w) = -t′ < t = x_c(v)`, so `w ≠ 1`. Let `(q₁, q₂)` be its opposite
pair, `n = q₁ w q₂`. Put `x′ = q₁⁻¹`, `z = n m` and
`y = m⁻¹ q₂⁻¹ m p₂⁻¹`; then `v v′ = x′ z y` is a group identity. Both `m` and
`n` negate their roots (`IsOppositeFactorPair.weylAction_eq_neg`), so
`y ∈ U_c(k)`. Their coroots agree up to sign by `coroot_eq_of_weylAction`
(this is where finiteness and spanning are used), so `z` acts trivially on
characters and lies in `Z(k)` (`IsSplitTorus.weylAction_eq_one_iff`). V 5 for
`w` gives `x_{-c}(x′) = t′`. For the depth of `y`, if `y ≠ 1` with opposite
pair `(s₁, s₂)`, then `(z s₁ z⁻¹ x′⁻¹, v′ s₂)` is an opposite pair of `v`;
V 5 for `v` and for `y` and the ultrametric inequality for `v′ s₂` give
`x_c(y) ≥ t` (`le_val_of_mul_eq`). Finally, `eval_translation_eq_of_factor`
gives translation parts with `⟨-c, w_m⟩ = -2t′` and `⟨c, w_n⟩ = 2t′`; since
`n` negates `c`, the translation part `n·w_m + w_n` of `z` vanishes on `c`,
and `val_conj_eq_of_eval_eq_zero` gives the last property. The proof uses V 1
and V 5 but not AS 1.

*Exchange.* Let `v ∈ U_{-a,x,0}`, `v′ ∈ U_{a,x,0}`; the cases `v = 1` or
`v′ = 1` are immediate. Since `x` lies in a chamber, AS 4 gives
`U_{b,x,0} = U_{b,x,0+}` (`filtration_eq_filtrationPlus_of_mem_chamber`), so
both valuations are positive. The rank-one factorization with `c = -a`
writes `v v′ = x′ z y` with `x′ ∈ U_{a,x,0}`, `y ∈ U_{-a,x,0}`, and `z`
preserving `x_{-a}`. Then `v v′ = x′ (z y z⁻¹) z`, where `z y z⁻¹` lies in
`U_{-a}(k)` (since `z ∈ Z(k)`) with the same valuation as `y`, so
`z y z⁻¹ ∈ U_{-a,x,0}`. Also `z = x′⁻¹ (v v′) y⁻¹` is a product of elements of
root filtration groups at `x`, hence lies in `G(k)^♯_x`, so
`z ∈ Z(k)^♯_x`. For `chamberRankOneExchange`, `-a ∈ Φ` follows from
`neg_mem_relativeRoots_of_rankOne`: V 0 gives a nonidentity `u ∈ U_a(k)`,
whose opposite pair negates `a`, and normalizer points preserve `Φ`.

## Provenance

The factorization follows the construction in the proof of Kaletha–Prasad
Proposition 7.1.1(1) (printed pp. 237–239, PDF pp. 268–270), with the
reflection property of `z` replaced by the vanishing of its translation part
on the root, which is all the exchange needs. The exchange is the rank-one
step of the proof of Kaletha–Prasad Proposition 7.3.12. The Lean arguments are
internal; opposite factor pairs (KP Proposition 2.11.17) remain a hypothesis.
