# Finite Čech cohomology from the graded pieces of the vanishing-ideal filtration (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` separated with `V` locally noetherian, `K` an
ordered affine cover of `V`, `Y` a closed subset, and `F` a coherent, quasi-coherent presheaf of modules over
`π` supported in `Y`. If every graded piece `I_Y^k F / I_Y^{k+1} F` (`idealPowQuot`) of the filtration by
powers of the vanishing ideal `I_Y` has finitely generated Čech cohomology for `K`, then so does `F`. The
theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot`
states this as `AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot` and proves it
from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.G4T`.

1. `cechFinite_of_affSES_mid'` and `cechFinite_of_affSES_right'` restate the FLT theorems
   `OModulePresheaf.cechFinite_of_affSES_mid` and `…_right`. `cechFinite_zero`: the zero presheaf has finite
   Čech cohomology.
2. `cechFinite_idealPow_of_forall_subsingleton`: if `I^N F` vanishes on every intersection `K.inter s`, all
   cochains of `I^N F` are zero, so its Čech cohomology is finite.
3. `exists_cechFinite_idealPow`: by the FLT theorem `OModulePresheaf.exists_idealPowSub_eq_bot`, each affine
   intersection `K.inter s` (there are finitely many with nonempty index sets) has some `N_s` with
   `I^{N_s} F = 0` there. Take `N` the maximum, using that the filtration decreases
   (`idealPowSub_antitone`). Intersections indexed by tuples longer than the cover are empty index sets.
4. `cechFinite_of_forall_cechFinite_idealPowQuot`: descending induction from `I^N F` along the short exact
   sequences `0 → I^{k+1} F → I^k F → I^k F / I^{k+1} F → 0` (`idealPowSES`) gives finiteness for
   `I^{N−j} F` for all `j`, in particular for `I⁰ F`. The sequence `0 → 0 → I⁰ F → F → 0`
   (`idealPowZeroSES`) then gives it for `F`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid` and `…_right` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
