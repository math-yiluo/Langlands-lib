# The Čech differential of a presheaf of modules squares to zero (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_comp_d`. Its declarations live
in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R`, `F` a presheaf of modules over `π`
(`OModulePresheaf π`) and `K` an ordered affine cover of `V`. Then for every `i`,
`F.d K (i + 1) ∘ F.d K i = 0`: the Čech differential squares to zero. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` states this as
`AlgebraicGeometry.OModulePresheaf.d_comp_d` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.DCompD`.

1. `succAbove_comp_succAbove`: for `i ≤ j` in `Fin (n + 2)`,
   `succAbove j.succ ∘ succAbove i = succAbove i.castSucc ∘ succAbove j`, by a case analysis on the
   values.
2. `res_at_eq`: restricting the values of a cochain at equal indices gives equal results.
3. `d_comp_d`: evaluate `d (d c)` at an index `s`. It is a double sum over `(a, b)` of
   `(−1)^{a+b}` times the restriction of `c` at the double face `face (face s a) b`, after merging the
   two restrictions with `res_comp`. Split the index pairs into `S = {a ≤ b}` and its complement. The
   map `(a, b) ↦ (b + 1, a)` is a bijection from `S` onto the complement. Paired terms have the same
   double face (step 1) and opposite signs, so the two partial sums cancel.

`solution` applies `d_comp_d`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_d_comp_d.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. `p2m_open "AlgebraicGeometry P2MW.S_….AlgebraicGeometry CategoryTheory"`
  becomes `open AlgebraicGeometry CategoryTheory`, dropping the `P2MW`-prefixed namespace, which does not
  exist at that point. The two `p2m_export` commands become `export _root_.AlgebraicGeometry (…)` and
  `export _root_.AlgebraicGeometry.OModulePresheaf (…)` with the same names. The second `p2m_open`
  becomes `open _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry`. No declaration,
  statement or proof step changed.
