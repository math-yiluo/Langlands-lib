# Exchange condition and parabolic lattice of a Tits system

This module works with a supplied abstract Tits system
`h : IsTitsSystem B N π S`. The group `G` and the Weyl group `W` have
independent universes. `length S` is the existing word length with respect
to `S`, and `cell B π w` is the existing Bruhat cell `B w B`. No finiteness of
`S`, saturation or Coxeter presentation is assumed. All results are internal
deductions from the Tits axioms and the Library's Bruhat-decomposition API
(`TitsSystemBruhat`, `TitsParabolicRigidity`, `TitsApartmentComparison`). They
implement the classical facts of Bourbaki, *Lie* IV §1.6–1.8 and §2.4–2.5,
which KP §1.4 recalls as Proposition 1.4.5 and uses in Lemma 1.4.9 and
Proposition 1.4.10. The route below is the one implemented; it does not use
Bourbaki's theorem that `(W, S)` is a Coxeter system.

## Lengths

`length_le_length_mul_left_add_one` is the lower bound
`ℓ(w) ≤ ℓ(sw) + 1`, obtained from the existing upper bound applied to `sw`.

`length_mul_left_ne` proves `ℓ(sw) ≠ ℓ(w)` for `s ∈ S`. Suppose they are
equal. Choose a representative `n` of `s`, and use axiom TS 4
(`conj_not_le`) to choose `b ∈ B` with `n b n⁻¹ ∉ B`; the existing
`conj_mem_cell` puts `n b n⁻¹` in `C(s)`. The existing lemma
`mul_mem_cell_of_length_le` (`C(s) C(v) ⊆ C(sv)` when `ℓ(v) ≤ ℓ(sv)`) applies
to both `v = w` and `v = sw`. For a representative `m` of `w`, it puts
`(n b n⁻¹) m` in `C(sw)`, and also puts `(n b)(n⁻¹ m)` in `C(s · sw) = C(w)`.
These are the same element, so Bruhat disjointness gives `sw = w`, hence
`s = 1`, contradicting axiom `ne_one`.

`length_mul_left_cases` combines the two bounds with this inequality:
`ℓ(sw) = ℓ(w) ± 1`. `length_eq_one` gives `ℓ(s) = 1` for `s ∈ S`, and
`length_one` gives `ℓ(1) = 0`.

## Condition (F) and exchange

`exists_mul_mem_cell_self_of_length_lt`: if `ℓ(sv) < ℓ(v)`, some point of
`C(s)` times some point of `C(v)` lies in `C(v)`. With `n`, `b` as above and a
representative `u` of `sv`, both `n u` and `(n b n⁻¹)(n u) = (n b) u` lie in
`C(s · sv) = C(v)`.

`mul_mul_eq_of_length` is condition (F) of Bourbaki IV §1.7: for
`s, s' ∈ S`, `ℓ(sws') = ℓ(w)` and `ℓ(sw) = ℓ(ws')` imply `sws' = w`.
In the auxiliary case `ℓ(w) < ℓ(sw)`, put `v = ws'`; then `ℓ(sv) < ℓ(v)`.
The previous lemma supplies `x ∈ C(s)`, `y ∈ C(v)` with `xy ∈ C(v)`. Split
`y = y₁ y₂` with `y₁ ∈ C(w)`, `y₂ ∈ C(s')`. Then `x y₁ ∈ C(sw)`, and the
right-handed TS 3 puts `x y₁ y₂` in `C(sw)` or `C(sws')`. Bruhat
disjointness gives `ws' = sw`, which is the claim, or `ws' = sws'`, which
forces `s = 1`. The remaining case `ℓ(sw) < ℓ(w)` applies the auxiliary case
to `s`, `sw`, `s'`; equal lengths are excluded by `length_mul_left_ne`.

`exists_eraseIdx_of_length_mul_lt` is the exchange condition. If `l` is a
word in `S` with `ℓ(l.prod) = l.length`, `s ∈ S`, and
`ℓ(s · l.prod) < l.length`, then `s · l.prod = (l.eraseIdx i).prod` for some
`i < l.length`. The proof is by induction on `l = l' ++ [t]`. The prefix
`l'` is reduced. If `ℓ(s · l'.prod) < l'.length`, the induction hypothesis
deletes a letter of `l'`. Otherwise the length dichotomy gives
`ℓ(s · l'.prod) = ℓ(l'.prod · t)` and `ℓ(s · l'.prod · t) = ℓ(l'.prod)`.
Condition (F) then gives `s · l'.prod · t = l'.prod`, which deletes the
last letter.

`exists_sublist_reduced` is the deletion condition: every word in `S` has a
sublist with the same product whose length is the length of the product. The
proof is induction on the word. A new first letter `t` is either kept, when
it increases the length, or the exchange condition removes one letter of the
reduced word already obtained.

## Parabolic subgroups of `W`

`exists_reduced_word_of_mem_closure`: for `X ⊆ S`, each `w ∈ ⟨X⟩` has an
`S`-reduced word all of whose letters lie in `X`. It reduces an `X`-word by
taking a sublist.

`mem_of_mem_closure` is `⟨X⟩ ∩ S = X` (Bourbaki IV §1.8, Corollary 1). A
reduced `X`-word of `s ∈ S` has length `ℓ(s) = 1`, so it is `[s]`.

`forall_mem_of_reduced_of_mem_closure` (Bourbaki IV §1.8, Proposition 7):
if `m` is any `S`-reduced word whose product lies in `⟨X⟩`, then all letters
of `m` lie in `X`. For `m = t :: m'`, exchange applied to a reduced
`X`-word of `w = m.prod` shows that `tw = m'.prod` lies in `⟨X⟩`. Hence
`t = m'.prod · w⁻¹ ∈ ⟨X⟩ ∩ S = X`, and induction treats `m'`.

`iInf_closure` proves `⋂ᵢ ⟨Xᵢ⟩ = ⟨⋂ᵢ Xᵢ⟩` for any family of subsets of
`S`, including the empty family. It checks the letters of one fixed
`S`-reduced word of `w` against every `Xᵢ`. `closure_inf_closure` is the
binary case `⟨X⟩ ∩ ⟨Y⟩ = ⟨X ∩ Y⟩` (Bourbaki IV §1.8, Theorem 2).

## Standard parabolic subgroups of `G`

`mem_standardParabolic_iff_of_mem_cell`: for `g ∈ C(w)`,
`g ∈ B ⟨X⟩ B` if and only if `w ∈ ⟨X⟩`, by Bruhat disjointness.

`standardParabolicSubgroup_le_iff` proves `G_X ≤ G_Y ↔ X ⊆ Y` for
`X, Y ⊆ S`. A representative of `s ∈ X` lies in `G_X ≤ G_Y`, so `s ∈ ⟨Y⟩`,
and `⟨Y⟩ ∩ S = Y`. `standardParabolicSubgroup_injective` follows.

`iInf_standardParabolicSubgroup` proves `⋂ᵢ G_{Xᵢ} = G_{⋂ᵢ Xᵢ}` whenever
`⋂ᵢ Xᵢ ⊆ S`; `standardParabolicSubgroup_inf` is the binary case
`G_X ∩ G_Y = G_{X ∩ Y}`. Both locate the Bruhat cell of an element of the
intersection and apply the corresponding statement in `W`.

The definition `standardParabolicOrderIso` packages Bourbaki IV §2.5,
Theorem 3. It is the order isomorphism from `{X // X ⊆ S}` (ordered by
inclusion) onto `{P : Subgroup G // B ≤ P}` (ordered by inclusion) sending
`X` to `G_X`. Its inverse chooses the type produced by the existing
`exists_eq_standardParabolic`. Injectivity makes this choice inverse, and
`standardParabolicSubgroup_le_iff` gives the order condition.

`eq_of_conjugateSubgroup_eq` shows that parabolic types are well defined (KP
Proposition 1.4.5(2) and Definition 1.4.6). If `g G_X g⁻¹ = k G_Y k⁻¹`, then
`G_Y` is the conjugate of `G_X` by `k⁻¹g`. The existing rigidity lemma
`mem_of_eq_conjugate` puts `k⁻¹g` in `G_Y`, so `G_X = G_Y` and `X = Y`.

## Scope

These are statements about an arbitrary supplied Tits system. They do not
decompose `S` into irreducible components or construct the projections and
product bijection of KP Lemma 1.4.9 and Proposition 1.4.10. They also do not
give the polysimplicial structure of KP Proposition 1.5.18, a realization of
the valuation quotient, or any of the five witnesses of
`RootValuationBuildingConstructionStatement`.
