# The essential pair input from the uniform rank-one statement

Module `Langlands.Representation.RankinSelberg.HighlyRamified.EssentialPairInputProof`.

This module proves the essential-vector input `EssentialPairInput n` of the adjacent-rank
step of Jacquet and Shalika, A Lemma on Highly Ramified ε-Factors, Math. Ann. 271 (1985),
§4.4, first paragraph (printed p. 327). The definition is in the Library module
`HighlyRamified.EssentialInput`. The Library also derives it there (`essentialPairInput`)
from two hypotheses: `Conductor.EssentialVectorLevelStatement` (JPSS 1981, Theorem
(5.1)(ii)) and `UniformRankOneTwistStatement`. The version here needs only the uniform
rank-one statement. The essential-vector level is proved directly for the representations
that occur, which are highly ramified twists, through the modules `UnitaryGamma` and
`EssentialLevel`. The result is internal to this project; it is not quoted from the
literature.

## Statement

`essentialPairInput_of_uniformRankOne h3 n : EssentialPairInput.{uF, uV} n` for
`h3 : UniformRankOneTwistStatement.{uF, uV}`. Unfolded: let `F` be a p-adic field with
its canonical topology and `ψ` an additive character with `additiveConductor ψ = 0`. For
every level `m` there are a quasicharacter `ξ` and a level `f > 0` with the following
property. Let `π₁, π₂` be generic representations of `GL_(n+3)(F)` on complex vector spaces
in universe `uV`, each with a nonzero vector fixed by `1 + ϖ^m M(O)`. Then there are
nonzero Whittaker functionals `ℓ_i` of `π_i ⊗ ξ ∘ det` and vectors `w_i` of their
Whittaker models such that

- each `w_i` is fixed by `K_1(f) = Conductor.levelSubgroup F (n + 2) f`;
- `w₁` and `w₂` agree on the mirabolic subgroup;
- `w₁(1) = w₂(1) = 1`;
- every central character of `π_i ⊗ ξ ∘ det` is trivial on `1 + 𝔭^f`.

## Proof

1. Choose a self-dual Haar measure `ν` (`nonempty_selfDualHaar`). Let `B` be the bound
   of `exists_bound_principalSeriesGamma` (module `UnitaryGamma`) at rank `n + 3` and
   level `m`. Choose `ξ` with conductor `a(ξ) ≥ max B 1`
   (`padicQuasicharacterUnboundedConductor`) and set `f = (n + 3) a(ξ) > 0`.
2. For each `π_i`, `exists_bound_principalSeriesGamma` gives `c_i ∈ ℂˣ` such that for
   every `z ∈ (ℂˣ)^(n+2)` the symmetric gamma factor of `(π_i ⊗ ξ ∘ det, I(z))` is the
   monomial `c_i^(n+2) (∏ z_j)^f X^((n+2) f)`. Here `I(z)` is the unramified principal
   series `Unramified.principalSeriesOfTuple F z`.
3. `π_i ⊗ ξ ∘ det` is generic (`isGeneric_quasicharacter_twist`), and `ψ` has integer
   conductor (`hasIntegerConductor_of_additiveConductor_eq_zero`). The theorem
   `exists_levelFixed_zeroCellLift_of_unit_gamma` (module `EssentialLevel`), applied with
   the monomials of step 2 restricted to norm-one `z`, gives `ℓ_i ≠ 0` and `w_i` fixed by
   `K_1(f)`. Each `w_i` agrees on the mirabolic subgroup with the same zero-cell function
   for `ψ` and the canonical uniformizer.
4. The identity lies in the mirabolic subgroup, and the zero-cell function is `1` there
   (`zeroCellWhittaker_one`), so `w_i(1) = 1`. Both `w_i` agree with the same function on
   the mirabolic subgroup, so they agree with each other there.
5. The Library lemma `trivialOnPrincipalUnits_of_levelFixed` turns `K_1(f)`-invariance
   and `w_i(1) = 1` into triviality of the central characters on `1 + 𝔭^f`.

Steps 1, 4 and 5 follow the Library proof `essentialPairInput`. Step 3 replaces its use of
`Conductor.EssentialVectorLevelStatement`.
