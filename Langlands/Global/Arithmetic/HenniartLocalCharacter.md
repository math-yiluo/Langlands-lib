# Local characters that agree on units up to an unramified twist

Author: Worker 5134. Module `Langlands.Global.Arithmetic.HenniartLocalCharacter`
(namespace `Langlands.Global`). It is a helper for the reduction
`HenniartGlobalizationReductionStatement`
(`Langlands.Global.Arithmetic.HenniartGlobalizationReduction`) of
`HenniartGlobalizationStatement` (Henniart 2000, §3.4). It contains no definitions.

Notation: `F, E'` are number fields with `E'` an `F`-algebra, `v` a finite place of `F`,
`u` a finite place of `E'` above `v`. `towerPadicField v u` is the Library's p-adic field
package on `E'_u`, and `padicField v` the one on `F_v`. `eu` is a reciprocity candidate of
`E'_u` satisfying the geometric normalization (`heu`). `fieldCharacter eu` and
`weilCharacter eu` are the Library's mutually inverse bijections between characters of
`W_{E'_u}` and of `E'_uˣ` (`LocalFactor/RankOne.lean`). `quasicharacterAt u _ ψ` reads a
character `ψ` of `(u.adicCompletion E')ˣ` as a character of the units of
`towerPadicField v u`.

## Result

`exists_weilCharacter_eq_mul_unramified v u eu heu η' hη' ψ hψ hunr`: let `η'` be a
continuous character of `W_{E'_u}` with `|η'| = 1`, and `ψ` a continuous character of
`E'_uˣ` with `|ψ| = 1`. Suppose `ψ(a) = fieldCharacter eu η' (a)` for every unit `a`
(valuation `1`; hypothesis `hunr`). Then there is `z ∈ ℂˣ` with `|z| = 1` and

`weilCharacter eu ψ = η' · (localUnramifiedCharacter (padicField v) z ∘ completionWeilMap v u)`.

Proof. Write `θ := fieldCharacter eu η'` and `μ := ψ · θ⁻¹`.

1. `μ` is trivial on the kernel of the normalized order (the units), because the
   canonical order of `towerPadicField v u` is minus the discrete valuation
   (`discreteValuation_padicFieldAt`) and `hunr` applies there.
2. `weilCharacter eu ψ = η' · weilCharacter eu μ`, since `weilCharacter` is
   multiplicative and inverts `fieldCharacter` (`weilCharacter_fieldCharacter`).
3. `μ` is unramified, so `Correspondence.weilCharacter_eq_localUnramifiedCharacter`
   gives `weilCharacter eu μ = localUnramifiedCharacter (E'_u) t` with
   `t := μ(ϖ_u)`, the value at the canonical uniformizer.
4. `|t| = 1`: evaluate step 2 at the geometric Frobenius. The unramified character
   takes the value `t` there, and `|ψ| = |η'| = 1`.
5. Let `f ≥ 1` be the residue degree of `E'_u / F_v`
   (`extensionResidueDegree_pos`). Choose `z` with `z^f = t` (`ℂ` algebraically closed).
   Then `|z| = 1`. The Library lemma `localUnramifiedCharacter_extensionWeilMap` says
   that the unramified character of `W_{F_v}` with value `z` restricts along
   `completionWeilMap v u` to the unramified character of `W_{E'_u}` with value `z^f = t`.

## Provenance

Internal helper for Henniart (2000), §3.4. Henniart prescribes the global Hecke character
`ξ` locally at `v` only up to an unramified twist and removes the twist afterwards. This
lemma isolates the local identity behind that step. It uses the standard fact that an
unramified character of `W_{F_v}` restricts to `W_{E'_u}` as the unramified character with
value raised to the residue degree.
