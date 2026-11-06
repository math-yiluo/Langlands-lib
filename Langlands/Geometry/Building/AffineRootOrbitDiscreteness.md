# Discreteness of orbits of root-permuting affine automorphisms

Setting: a finite-dimensional real normed affine space `P` and a set `Ψ` of
affine functionals on `P` with
`AffineRootSystem.IsLocallyFiniteReflectionArrangement Ψ`. Of that predicate the
proof uses only three fields: the derivatives span `V*`, there are finitely many
of them, and `finite_bounded_at` (local finiteness).

`AffineRootSystem.exists_forall_dist_lt_imp_eq hΨ a` states: there is `ε > 0`
such that every `e ∈ rootStabilizer Ψ` (an affine automorphism `e` of `P` with
`η ∘ e ∈ Ψ ↔ η ∈ Ψ` for every affine functional `η`) with
`dist (e a) a < ε` fixes `a`. So every orbit of `rootStabilizer Ψ` is discrete.

Proof as implemented. For each derivative `φ`, choose `ψ_φ ∈ Ψ` with
derivative `φ`. Let `C` bound the finitely many values `|ψ_φ a|`. The set
`S = {ψ ∈ Ψ | |ψ a| ≤ C}` and the set of values
`T = {η a | η ∈ Ψ, |η a| ≤ C + 1}` are finite by local finiteness. Since the
`ψ ∈ S` are continuous, there is `ε > 0` such that each point `x` with
`dist x a < ε` satisfies `|ψ x - ψ a| < 1` for every `ψ ∈ S`. Such a point also
satisfies `ψ x ≠ t` for each `ψ ∈ S` and each `t ∈ T` different from `ψ a`.
If `e` permutes `Ψ` and `dist (e a) a < ε`, then for `ψ ∈ S` the functional
`η = ψ ∘ e` lies in `Ψ` and `|η a| = |ψ (e a)| ≤ C + 1`. So `ψ (e a) ∈ T`, hence
`ψ (e a) = ψ a`. Thus every derivative vanishes on `e a -ᵥ a`. These
derivatives span `V*`, so `e a -ᵥ a = 0`.

This is the apartment step of the proof of Kaletha–Prasad (2023),
Lemma 4.2.11, printed pp.171–172 / PDF pp.202–203. The source uses the
uniform separation of parallel walls (Axiom 4.1.6, Proposition 1.3.12) to find
a ball meeting only walls through `x`. The source then uses facet stabilizers in
`G(k)^0`. Here, instead, the full root stabilizer is shown to have discrete
orbits on the apartment. This group contains the image of the whole normalizer
(by the field `range_le_extendedAffineWeylGroup` of the Library's apartment
axioms, AS 5, and `AffineRootSystem.extendedAffineWeylGroup_le_rootStabilizer`).
The formulation is derived, and no building is involved.

Author: Worker 1221.
