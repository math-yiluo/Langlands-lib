# Dynamic parabolics of regular cocharacters (conditional on structure inputs)

Module `Langlands.GroupScheme.Absolute.RegularCocharacterParabolic`. It is derived
infrastructure for clause 2 of `Langlands.GroupScheme.RegularCocharacterBorelStatement`
(task `618cd683-cfcd-43a3-b4bf-6c8abd208b1f`).

Let `G` be a smooth connected affine group over a field `k`, let `j : T ⟶ G` be a
homomorphism from a split torus, and let `ν, ν'` be regular cocharacters of `j`. The module
proves that the dynamic parabolics `P(ν ≫ j)` and `P(ν' ≫ j)` are equal exactly when every
root `α` of `j` is positive on `ν` iff it is positive on `ν'`. This is Milne's
Proposition 21.31, but the module proves it only conditionally on four published statements
taken as hypotheses (listed below). Subgroup-functor equality holds on every test scheme.

## Structural inputs

Both theorems take the following published statements as explicit hypotheses and do not prove
them. A final proof of the target applies these theorems to the Library proofs of the four
statements once those proofs are published.

- `hLie : DynamicLieStatement` (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), Proposition 2.1.8(1), printed p.53).
- `hSm : DynamicSmoothStatement` and `hCo : DynamicConnectedStatement` (CGP 2.1.8(3), (4)).
- `hEq : LieSubgroupEqualityStatement` (Milne, *Algebraic Groups* (2017), Proposition 10.15,
  printed p.190).

These hypotheses appear only on the two theorems below. They are not premises of any target
statement.

## Contents

- `parabolic_comp_eq_iff_of_isRegular`. Assume `G` smooth, affine and connected, `T` split,
  `j : T ⟶ G` any homomorphism and `ν, ν'` regular cocharacters of `j`
  (`IsRegularCocharacter j`: no root of `j` pairs to zero). Then
  `Dynamic.parabolic (groupHom ν ≫ j) = Dynamic.parabolic (groupHom ν' ≫ j)` iff
  `∀ α ∈ roots j, (0 < ⟨α, ν⟩ ↔ 0 < ⟨α, ν'⟩)`, where `⟨α, ν⟩ = latticePairing T α ν`.
  The proof composes two equivalences:
  1. `parabolic_comp_eq_iff_iSup_weightSpace_eq` (module
     `Langlands.GroupScheme.Dynamic.ParabolicLieCriterion`, using `hLie`, `hSm`, `hCo`,
     `hEq`): the two parabolics are equal iff
     `⨆ n : ℕ, weightSpace (ν ≫ j) (Gm.powerHom _ n)` and the same sum for `ν'` agree. These
     sums are the Lie algebras of the two parabolics, by `hLie`.
  2. `iSup_nat_weightSpace_cocharacter_eq_iff` (Worker 303's module
     `Langlands.GroupScheme.Absolute.RegularCocharacterWeights`, which uses only the published
     split-torus weight decomposition): for split `T` and regular `ν, ν'`, these two sums
     agree iff every root has the same sign on `ν` and on `ν'`.
- `regularCocharacterBorel_parabolic_eq_iff`: the same conclusion for a connected reductive
  `G` (`IsConnectedReductive G`) and any homomorphism `j : T ⟶ G` from a split torus. Its
  conclusion is exactly clause 2 of `RegularCocharacterBorelStatement`, including the
  `haveI := hG.isAffineHom` binder. The proof obtains smoothness, affineness and connectedness
  from `hG` and applies `parabolic_comp_eq_iff_of_isRegular`. Maximality of the torus is not
  needed; the target's hypothesis `IsMaximalTorus j` is simply not used in this clause.

## Provenance

The statement is Milne, *Algebraic Groups* (2017), Proposition 21.31 (printed p.434, PDF
p.450): for regular cocharacters `ν, ν'` of a split maximal torus, `P(ν) = P(ν')` iff `ν`
and `ν'` lie in the same Weyl chamber. Milne's proof is the chain "same Weyl chamber" ⟺
`{α ∈ Φ | ⟨α,ν⟩ > 0} = {α ∈ Φ | ⟨α,ν'⟩ > 0}` ⟺ `Lie P(ν) = Lie P(ν')` ⟺ `P(ν) = P(ν')`.
The Lean statement uses the sign condition on roots in place of Weyl chambers, as in the
target.

The Lean proof follows the same chain with different inputs. Milne gets
`Lie P(ν) = 𝔱 ⊕ ⨁_{⟨α,ν⟩>0} 𝔤_α` from Proposition 21.29, which uses `Z(ν) = T`, and gets the
last equivalence from Borel-subgroup theory. Here the Lie algebra of `P(ν ≫ j)` comes from
CGP 2.1.8(1) (`hLie`), with trivial-weight part `weightSpace j 0` instead of `Lie T`, so no
centralizer computation is needed. The last equivalence comes from CGP 2.1.8(3),(4) and
Milne 10.15, through the criterion in `ParabolicLieCriterion`. Consequently the theorems
hold for any homomorphism from a split torus into a smooth connected affine group, not only
for maximal tori of reductive groups.
