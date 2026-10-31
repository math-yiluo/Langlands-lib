# Čech complexes for covers by two charts, and comparison maps of complexes

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech`, in namespace
`TwoChartCech`.

## Definitions

Let `R` be a commutative ring.

**Two-chart covers and sections.**

- A `Cover R` is an algebraic model of a cover by two affine charts: three commutative `R`-algebras
  `A0`, `A1`, `A01` with `R`-algebra maps `ρ0 : A0 → A01` and `ρ1 : A1 → A01` (the restrictions to
  the overlap).
- For a cover `𝒰`, a `Sections 𝒰` consists of an `A0`-module `M0`, an `A1`-module `M1` and an
  `A01`-module `M01`, each also an `R`-module compatibly with the algebra structure, together with
  `R`-linear maps `r0 : M0 → M01` and `r1 : M1 → M01` that are semilinear over `ρ0` and `ρ1`
  (`r0 (a • m) = ρ0 a • r0 m`, and likewise for `r1`). This models the sections of a sheaf of modules on
  the two charts and on their overlap.
- For `S : Sections 𝒰`, the Čech differential `S.cechDiff : M0 × M1 → M01` is
  `(m0, m1) ↦ r1 m1 − r0 m0` (lemma `cechDiff_apply`); `S.H0` is its kernel, the pairs that agree on the
  overlap (`mem_H0_iff`), and `S.H1` is its cokernel `M01 / image`.
- `𝒰.lineBundle t`, for a unit `t` of `A01`, is the sections datum with `M0 = A0`, `M1 = A1`,
  `M01 = A01`, `r0 = ρ0` and `r1 = t · ρ1`: the line bundle with transition function `t`. A pair
  `(p0, p1)` lies in its `H0` exactly when `ρ0 p0 = t · ρ1 p1` (`mem_H0_lineBundle_iff`).
  `𝒰.structureSheaf` is `𝒰.lineBundle 1`, whose `H0` consists of the pairs with `ρ0 p0 = ρ1 p1`
  (`mem_H0_structureSheaf_iff`).
- `Cover.trivial R` is the cover with `A0 = A1 = A01 = R` and identity maps.
  `Sections.ofSubmodules N0 N1 N01 h0 h1`, for submodules `N0, N1 ≤ N01` of an `R`-module, is the
  sections datum over the trivial cover given by the two inclusions. Its `H0` consists of the pairs with
  equal images (`mem_H0_ofSubmodules_iff`).

**Maps of two-term complexes and base change.** Let `d : C0 → C1` be `R`-linear.

- `kerBaseChangeHom d A : A ⊗ ker d → ker (d ⊗ A)` is the natural `A`-linear map, for an `R`-algebra
  `A` (`kerBaseChangeHom_apply_coe` gives its value).
- Given a second map `dK : K0 → K1` and `R`-linear maps `ι0 : K0 → C0`, `ι1 : K1 → C1` with
  `d ∘ ι0 = ι1 ∘ dK`, `kerMap` and `cokerMap` are the induced maps `ker dK → ker d` and
  `K1 / im dK → C1 / im d`. `kerMapBaseChange` and `cokerMapBaseChange` are the same maps after
  base change to an `R`-algebra `A`, defined on the kernels and cokernels of `dK ⊗ A` and `d ⊗ A`.
- A `GrothendieckComplex d` is a two-term complex `G` of finite free `R`-modules
  (`CoherentBaseChange.TwoTermComplex`), with maps `ι0`, `ι1` as above from `G.d` to `d`, such that for
  every `R`-algebra `A` in universe `u` the induced maps on kernels and on cokernels after base change to
  `A` are bijective. So `G` computes the kernel and cokernel of `d` universally, as in Grothendieck's
  theorem on cohomology and base change.

The section `Gates` contains four `example`s that sanity-check these definitions over `R` and `ℤ`. They
declare nothing.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_TwoChartCech.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_CoherentBaseChange` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
