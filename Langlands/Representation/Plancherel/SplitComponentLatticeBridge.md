# Uniformizer realization and finite index of the split-component valuation image

Author: Worker 1503.

This module proves the valuation bijection conjunct of
`Langlands.Plancherel.RenardCartan.SplitComponentLatticeStatement`
unconditionally. It proves the finite-index conjunct from injectivity of
restriction of rational characters to the split component. It then reduces the
whole statement to either of two published, still unproved, Library
propositions: `Langlands.GroupScheme.CentralSplitTorusCharacterStatement` and
`Langlands.GroupScheme.CharacterRestrictionStatement`. It does not prove
`SplitComponentLatticeStatement` itself.

## Provenance

The content is internal. It serves the setting of Renard's V.3.23 recorded in
`Langlands.Plancherel.RenardCartan` (`C0`, `splitValuationImage`). All arguments
are deductions from published Library definitions and theorems:

- `Langlands.GroupScheme.IsSplitComponent.finiteIndex_range_characterRestrict`
  (finite index of the range of restriction `X^*(Z)_F → X^*(A)`);
- the split-torus uniformizer section results in
  `Langlands.Geometry.Building.CocharacterUniformizerProof`
  (`rationalCharacterValuation_latticeSection`,
  `mem_normKernel_mul_section_inv_iff`, `isUniformizerLatticeSection`,
  `latticePairing_isPerfPair`);
- `Langlands.GroupScheme.rationalCharacterValuation_characterRestrict`, which
  says the valuation of `s(t)` on `χ` is the valuation of `t` on `χ ∘ s`;
- `Langlands.GroupScheme.CharacterRestrictionFiniteIndex.finiteIndex_of_nsmul_mem`
  together with `rationalImage_moduleFinite` and the published
  `rationalCharacterLattice`;
- `Langlands.GroupScheme.characterRestrict_injective_of_centralSplitTorusCharacter`.

## Setting

`F : Type u` is a nonarchimedean local field of any characteristic. `T` is a
commutative group scheme over `Spec F`, `Z` a group scheme over `Spec F` and
`s : T.toGrp ⟶ Z` a homomorphism. `C0 T s` is the image of
`rationalPoints.map s ∘ uniformizerSection T`. `splitValuationImage s` is the
range of `t ↦ H_Z(s(t))` inside `rationalCharacterValuationImage Z`.

## Declarations

`rationalCharacterValuation_map_uniformizerSection s c χ`: the valuation of
`s(ϖ^c)` on a rational character `χ` of `Z` equals
`⟨r(χ), c⟩`, where `r(χ)` is the restriction `characterRestrict s χ`, viewed in
`characterLattice T`. Proof: rewrite with the valuation compatibility of
restriction, then apply `rationalCharacterValuation_latticeSection`.

`exists_rationalCharacterValuation_map_eq s hT t`: if `T` is a split torus, every
`t ∈ T(F)` has a cocharacter `c` with `H_Z(s(ϖ^c)) = H_Z(s(t))`. Proof:
`isUniformizerLatticeSection` gives `c` with `t (ϖ^c)⁻¹` in the norm kernel of
`T`. Then `mem_normKernel_mul_section_inv_iff` gives equal valuations on every
character of `T`. Apply this to each restricted character.

`cocharacter_eq_of_rationalCharacterValuation_eq s hT hindex h`: if `T` is a
split torus and the range of restriction has finite index `N`, equal ambient
valuations of `s(ϖ^c)` and `s(ϖ^d)` force `c = d`. Proof: by the perfect
pairing, it suffices that `⟨α, c⟩ = ⟨α, d⟩` for every `α ∈ X^*(T)`. Since `N • α`
is a restriction `r(χ)`, the hypothesis gives `N⟨α, c⟩ = N⟨α, d⟩`. Cancel
`N ≠ 0` in `ℤ`.

`bijOn_C0_splitValuationImage s hT hindex`: with the same hypotheses, the
restricted valuation `(rationalCharacterValuation Z).rangeRestrict` is a
bijection from `C0 T s` onto `splitValuationImage s`. Maps-to is immediate.
Injectivity on `C0` follows from the previous lemma. Surjectivity onto the
image follows from `exists_rationalCharacterValuation_map_eq`.

`pow_index_mem_splitValuationImage s hT hinj y`: if `T` is a split torus and
restriction is injective, then for `N` the index of its range,
`y ^ N ∈ splitValuationImage s` for every `y` in the actual valuation image. Proof:
let `e : X^*(Z)_F ≃ range r` be the inverse of the injective restriction
(`AddMonoidHom.ofInjective`). Define the integer functional
`ν(α) = y(e⁻¹(N • α))` on `X^*(T)`; `N • α` lies in the range by
`AddSubgroup.nsmul_index_mem`. The perfect pairing gives a cocharacter `c` with
`⟨α, c⟩ = ν(α)`. For each `χ`, `e⁻¹(N • r(χ)) = N • χ`. Hence the valuation of
`s(ϖ^c)` on `χ` is `y(N • χ) = (y ^ N)(χ)`. If `N = 0` the statement is trivial
and the proof covers it uniformly.

`finiteIndex_splitValuationImage_of_injective hZ s hs hinj`: for connected
reductive `Z`, a split component `s`, and injective restriction,
`splitValuationImage s` has finite index. Proof: the actual image is a finitely
generated `ℤ`-module (`rationalImage_moduleFinite`, using finite generation of
`X^*(Z)_F` from `rationalCharacterLattice`). The previous lemma puts `N • y` in
the additive subgroup for every `y`, with `N ≠ 0` by the published finite index
of restriction. Then apply `finiteIndex_of_nsmul_mem`.

`splitComponentLattice_of_injective hZ s hs hinj`: the two conjuncts of
`SplitComponentLatticeStatement` for one split component, assuming injective
restriction. The bijection uses only `hs.1.1.1 : IsSplitTorus T.toGrp` and the
published finite index of restriction.

`splitComponentLatticeStatement_of_centralSplitTorusCharacter hS`: the
`SplitComponentLatticeStatement.{u}` follows from
`CentralSplitTorusCharacterStatement.{u}`. Injectivity comes from
`characterRestrict_injective_of_centralSplitTorusCharacter`.

`splitComponentLatticeStatement_of_characterRestriction hR`: the
`SplitComponentLatticeStatement.{u}` follows from the first conjunct of
`CharacterRestrictionStatement.{u}`.

## Scope

The bijection conjunct holds unconditionally for every split component. The
finite-index conjunct here is conditional on injective restriction. Informal
remark, not formalized here: every element of `splitValuationImage s` vanishes
on the kernel of restriction. So finite index forces every element of the
actual image to vanish there. This is why the conjunct is derived from the
injectivity input that the two named propositions supply. No assumption of
integral image realization, finite index, or rational-point surjectivity of an
isogeny is made.
