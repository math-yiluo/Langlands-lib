# Bounded first-quadrant double complexes, their total cohomology and `E₂` pages

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_DoubleComplex`, in namespace
`DoubleComplex`. All modules live in a fixed universe `u`; `R` is a commutative ring.

## Definitions and results

**Bounded double complexes.** A `Bounded R` is a family of `R`-modules `C p q` for `p, q ∈ ℕ`, with
horizontal differentials `dH p q : C p q → C (p+1) q` and vertical differentials
`dV p q : C p q → C p (q+1)` such that `dH ∘ dH = 0`, `dV ∘ dV = 0` and `dV ∘ dH = dH ∘ dV`
(the squares commute), together with a bound `N` such that `C p q` is trivial whenever `p ≥ N` or
`q ≥ N`.

**Total complex.** For `D : Bounded R`:

- `Diag n` is the set of pairs `(p, q)` with `p + q = n`, and `Tot D n` is the product of the `C p q`
  over `Diag n`;
- `dTot D n : Tot D n → Tot D (n+1)` is the total differential: its `(p, q)` component is
  `dH` of the `(p−1, q)` component plus `(−1)ᵖ · dV` of the `(p, q−1)` component (terms with negative
  indices omitted; helper maps `dTotH`, `dTotV`). The lemmas `dTot_apply_zero_succ`,
  `dTot_apply_succ_zero` and `dTot_apply_succ_succ` give these components, and `dTot_comp_dTot`
  (theorem) proves `dTot ∘ dTot = 0`;
- `HTot D n` is the total cohomology: cocycles of `dTot D n` modulo the coboundaries `HTotB D n`
  (zero for `n = 0`).

**The `E₂` pages.**

- `colH D p q` is the vertical cohomology at `(p, q)`: cocycles of `dV p q` modulo the image of
  `dV p (q−1)` (`colB`, zero for `q = 0`).
- `colHdH D p q : colH D p q → colH D (p+1) q` is the map induced by `dH`.
- `E₂I D p q` is the cohomology of the complexes `colHdH` at `(p, q)` (`E₂IB` gives the
  coboundaries, zero for `p = 0`): the `E₂` page of the spectral sequence that takes vertical
  cohomology first.
- `transpose D` swaps the two directions, and `E₂II D p q` is `E₂I (transpose D) q p`, the `E₂` page
  that takes horizontal cohomology first. The file provides the module instances on `E₂I` and `E₂II`.

**Convergence data.** `SubQuot R M` is a pair of submodules `B ≤ Z` of `M`, with `carrier` the quotient
`Z / B`. For a family of modules `E₂ p q`, a family `H n` and a bound `N`, a `Convergence R E₂ H N`
consists of:

- for each `(p, q)` a subquotient `Einf p q` of `E₂ p q` (the `E∞` term), with `Z = ⊤` on the row
  `q = 0` (`hZ0`);
- for each `p` an increasing filtration `Bfilt p 0 ≤ ⋯ ≤ Bfilt p N` of `E₂ p 0`, from `⊥` to the
  submodule `B` of `Einf p 0`, whose successive quotients are each isomorphic to a subquotient of some
  `E₂ p' q'` with `q' ≥ 1`;
- for each `n` an increasing filtration `Hfilt n 0 ≤ ⋯ ≤ Hfilt n (N+1)` of `H n` from `⊥` to `⊤`,
  such that for each `p ≤ N` the quotient `Hfilt p (p+1) / Hfilt p p` is isomorphic to the carrier of
  `Einf p 0`.

`BoundedSpectralSequence` is the proposition that for every commutative ring `R` in universe `u` and
every `D : Bounded R` there is a `Convergence R (E₂I D) (HTot D) D.N`. It records the part of the
spectral sequence of a bounded double complex that later files use. The file states it and does not
prove it.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_DoubleComplex.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

The file imports only Mathlib, so its imports are unchanged.
