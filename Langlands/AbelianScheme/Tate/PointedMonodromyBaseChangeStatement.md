# Pointed base change and Tate monodromy

This file states equivariance of the existing actual Tate base-change comparisons under the homomorphism of fundamental groups induced by a map of pointed bases. It contains proposition definitions only. The conjunction `Langlands.AbelianScheme.Tate.PointedMonodromyBaseChange` is the target for a separate proof.

## Source and derived provenance

The geometric input is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter X, (10.30), printed p.151 / PDF p.155. Pullback of finite étale covers identifies the fibre functor at a point of the old base with the composite fibre functor over the new base. This induces the homomorphism on automorphism groups. Its composition law begins on printed p.152 / PDF p.156. The registered source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The statements here are derived specializations of this mechanism to the published abelian torsion kernels, their selected inverse limits, and their rationalizations. The source does not state this three-part Lean conjunction. The actual constructions are imported from `FiniteEtale.Pullback`, `Tate.IntegralBaseChange`, `Tate.RationalBaseChange`, `Tate.FiniteMonodromy`, `Tate.IntegralMonodromy`, and `Tate.RationalMonodromy`. No replacement group, Tate carrier, or arbitrary action is introduced.

## Hypotheses and direction

Fix schemes `S` and `S'`, a map `b : S' ⟶ S`, a field `Ω`, and `t : Spec Ω ⟶ S'`. The old pointed base is `(S, t ≫ b)`. The hypotheses `ht` and `hs` explicitly assert finiteness of every finite étale cover's fibre at these two points. In Lean, `FundamentalGroup` is the automorphism group of the actual finite fibre functor. Algebraic closedness, connectedness and local noetherianness are not needed for these formal equivariance statements once the fibre finiteness hypotheses are supplied. They remain relevant to the usual geometric interpretation and are not deduced here.

Write `b_*` for `fundamentalGroupMap b t (t ≫ b) rfl ht hs`. Its direction is from the group at `t` on `S'` to the group at `t ≫ b` on `S`. If `A` is an abelian scheme over `S`, write `A'` for its actual pullback `(AbelianScheme.baseChange b).obj A`. Each existing base-change comparison `B` has direction from the Tate carrier of `A'` at `t` to that of `A` at `t ≫ b`. All three statements express

`B (ρ_A'(g) x) = ρ_A(b_* g) (B x)`.

The torsion finite-étaleness statement `htor : TorsionFiniteEtaleStatement` is an explicit hypothesis. It is applied to both actual abelian schemes; no proof of that geometric theorem is supplied by this file.

## The three propositions

- `LevelMonodromyBaseChange` quantifies over a positive integer `n`, proofs that `n` is a unit in the global sections of both bases, a group element `g`, and an actual `n`-torsion point `x`. It uses `GroupScheme.Tate.levelBaseChange` and `levelMonodromy`. The comparison comes from the torsion-point pullback adjunction, whose compatibility with the scheme kernel is already expressed by `GroupScheme.torsionBaseChangeIso_points`.
- `IntegralMonodromyBaseChange` quantifies over any selection predicate `P : ℕ → Prop`. Its index type retains positive integers satisfying `P`. It requires invertibility of each retained order on both bases. Its equality uses the actual coordinatewise comparison `integralBaseChange` and actual inverse-limit automorphisms `integralMonodromy`.
- `RationalMonodromyBaseChange` has the same selection and invertibility hypotheses, and uses `rationalBaseChange` and `rationalMonodromy` on the existing carrier `ℚ ⊗[ℤ] Integral`.

`PointedMonodromyBaseChange` is the conjunction of these three universally quantified propositions, in that order. The two families of invertibility witnesses are supplied independently; the statement does not claim their independent necessity or construct one from the other.

The selections `P n := True` and `P n := Nat.Coprime n m` recover the full and prime-to-modulus systems. In the second case the restriction of orders precedes rationalization. This file does not introduce a separate prime-adic comparison or identify these carriers with a product of local rational Tate modules.

## Scope

These are algebraic equivariance statements. They do not assert rational topological properties, preservation of a Weil pairing, a trivialization of the Tate twist, or independence of scalar-comparison witnesses. The underlying maps and actions already have their published scalar structures, but no new adelic scalar comparison is asserted here.

In particular, equivariance is with respect to `b_*`; it does not assert that `b_*` is surjective. Consequently the inverse underlying base-change comparison can be used in later work to pull a monodromy-fixed orbit from `S` to `S'`, but a bijection between their fixed-orbit sets is not claimed. That construction and its coherence laws are separate from this statement unit.
