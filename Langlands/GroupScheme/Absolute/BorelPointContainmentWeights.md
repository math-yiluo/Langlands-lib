# Weight decomposition under a generic point of a cocharacter

Author: Worker 1095.

This helper module of the proof of `BorelPointContainmentStatement` checks
the hypothesis of Lemma B (`BorelPointContainmentTangent`) for the dynamic
centralizer of a cocharacter. The namespace is
`Langlands.GroupScheme.BorelPointContainment`. The field `k` is arbitrary
except where `[Infinite k]` is stated. `G` is a group scheme over `Spec k`
with `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, and
`χ : (Gm (Spec k)).toGrp ⟶ G` is a cocharacter.

## A unit avoiding finitely many roots of unity

`exists_unit_zpow_ne_one`: over an infinite field, for every finite set
`S ⊆ ℤ` there is `c₀ : kˣ` with `c₀ ^ n ≠ 1` for all nonzero `n ∈ S`.

Proof. Choose `x` outside the finite set consisting of `0` and the roots of
`X^|n| − 1` for `n ∈ S` (`Infinite.exists_notMem_finset`,
`Polynomial.nthRoots`). If `c₀ = x` had `c₀ ^ n = 1` with `n ≠ 0`, then
`x ^ |n| = 1`, a contradiction.

## A generic point of 𝔾_m

`exists_generic_affinePoint` (`[Infinite k]`): there is a `k`-point `u` of
`𝔾_m` (a term of `Lie.AffinePoints (Gm (Spec k)).toGrp k`) such that
`Lie.characterValue (Gm.powerHom _ n) u ≠ 1` for every `n ≠ 0` whose weight
space `weightSpace χ (Gm.powerHom _ n)` is nonzero.

Proof. The set of `n` with nonzero weight space is finite: the Library
theorem `IsSplitTorus.finite_weightSupport` (`𝔾_m` is split) bounds the
characters with nonzero weight space, and `Gm.powerHom` is injective. Take
`c₀` from `exists_unit_zpow_ne_one` and let `u` correspond to `c₀` under
`Gm.affinePointsEquiv`. By `characterValue_powerHom`, the value of the
character `t ↦ t^n` at `u` is `c₀ ^ n`.

## The weight decomposition

`exists_adjoint_sub_add_eq`: let `iZ : Z ⟶ G` with `IsAffineHom Z.X.hom`
represent the dynamic centralizer, `(Dynamic.centralizer χ).IsRepresentedBy iZ`,
and let `u` be as in `exists_generic_affinePoint`. Then every vector `W` of
the additive Lie algebra `Additive (lieKernel G k)` has the form

    adjoint G k (u ≫ χ.hom.hom) X − X + Lie.targetMapLinear iZ k ξ = W

for some `X` in the Lie algebra of `G` and `ξ` in the Lie algebra of `Z`.
Here `adjoint G k g` is the Library's adjoint action of a `k`-point and
`Lie.targetMapLinear iZ k` is the differential of `iZ`.

Proof. The Library's weight coefficients
`DynamicLie.weightCoeffs k G χ W`, a finitely supported family indexed by
exponents `m`, sum to `W` (`weightCoeffs_sum`). The coefficient `w_m` lies in
the weight space of `t ↦ t^m` (`weightCoeffs_mem`). On that weight space the
adjoint action of `χ(u)` is multiplication by the scalar
`c_m = Lie.characterValue (Gm.powerHom _ m) u`. This follows from
`mem_weightSpace` and `lieKernelMap_id`. Put

    X = Σ_{m ≠ 0} (c_m − 1)⁻¹ • w_m.

For `m ≠ 0` with `w_m ≠ 0` the weight space is nonzero, so `c_m ≠ 1` by
the choice of `u`. Hence `Ad(χ(u))((c_m − 1)⁻¹ w_m) − (c_m − 1)⁻¹ w_m = w_m`,
and `Ad(χ(u))X − X = Σ_{m ≠ 0} w_m`. The coefficient `w_0` lies in the weight
space of weight `0`. By part 1 of the Library theorem `dynamicLie`
(`DynamicLieStatement`), it is therefore a point of `Dynamic.centralizer χ`.
Since `iZ` represents the centralizer, `w_0 = x ≫ iZ` for a `k[ε]`-point `x`
of `Z`. This `x` lies in `lieKernel Z k` by `Lie.mem_lieKernel_comp_hom_iff`
(`iZ` is a monomorphism, from the representability hypothesis). With
`ξ = x`, the sum is `Σ_{m ≠ 0} w_m + w_0 = W`.

## Provenance

This is the standard eigenspace computation `Lie(G) = ⊕_m g_m` with
`Lie(Z_G(χ)) = g_0`. The second fact is the Library theorem `dynamicLie`,
whose statement Markdown (`Dynamic/LieStatement.md`) cites
Conrad–Gabber–Prasad, Proposition 2.1.8(1). The lemmas of this module are
internal to this proof. Milne's proof of Corollary 17.34 instead uses the centralizer of a
maximal torus (Theorem 17.33(a)).
