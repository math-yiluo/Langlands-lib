# Multiplication by `n` and its kernel for a relative group law

Module `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel`, in namespace
`GoodReductionJacobian.RelativeGroupLaw`. Schemes and rings live in a fixed universe `u`;
`G : RelativeGroupLaw R f` is a group law on the points of `f : A ⟶ Spec R`
(`Def_AlgebraicGeometry_RelativeGroupLaw`).

## Definitions and results

**Multiples on points.**

- `G.nsmul t n x` is the `n`-th power of the `T`-point `x` in the group law, defined by
  `nsmul 0 x = 1` and `nsmul (n+1) x = nsmul n x * x` (`nsmul_zero`, `nsmul_succ`). Then
  `nsmul 1 x = x` (`nsmul_one_apply`), `nsmul n 1 = 1` (`nsmul_unit`), and `nsmul` is natural in `T`
  (`nsmul_natural`).

**Torsion points.**

- `G.IsTorsionPoint t n x` means `nsmul n x = 1` (`isTorsionPoint_def`), and `G.torsionSubset t n` is the
  set of such `T`-points (`mem_torsionSubset`), the `T`-points of `A[n]`.
- The unit is `n`-torsion (`isTorsionPoint_unit`), the `1`-torsion points are the unit only
  (`isTorsionPoint_one_iff`), and torsion is preserved by base change along `T' ⟶ T`
  (`isTorsionPoint_schemeHomOverComp`, `mapsTo_torsionSubset_schemeHomOverComp`).

**Multiplication by `n` as a morphism, and its kernel.**

- `idPoint` is the tautological `A`-point `𝟙 A` of `A`.
- `G.schemeNsmul n : A ⟶ A` is the morphism `[n]` given by `nsmul n` applied to `idPoint`; it lies over
  `Spec R` (`schemeNsmul_over`).
- `G.schemeKer n` is the scheme `A[n] = A ×_{[n], A, e} Spec R`, the fibre product of `[n]` and the unit
  section `e : Spec R ⟶ A`, and `G.schemeKerStr n : A[n] ⟶ Spec R` is its structure morphism (the second
  projection).

## Provenance and licence

This file is a port of `Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
