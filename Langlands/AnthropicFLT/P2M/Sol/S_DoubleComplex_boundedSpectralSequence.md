# The edge part of the spectral sequence of a bounded double complex (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_DoubleComplex_boundedSpectralSequence`. Its declarations live in the
namespace `P2MW.S_DoubleComplex_boundedSpectralSequence`.

## Statement

`solution : DoubleComplex.BoundedSpectralSequence.{u}`. That is, for every commutative ring `R` in universe
`u` and every bounded double complex `D : DoubleComplex.Bounded R` there is convergence data
`DoubleComplex.Convergence R (E₂I D) (HTot D) D.N` (`Def_AlgebraicGeometry_DoubleComplex`) relating the `E₂`
page `E₂I D` (vertical cohomology first) to the cohomology `HTot D` of the total complex. The data records the
bottom row: each `E₂ p 0` carries a filtration whose graded pieces are subquotients of terms `E₂ p' q'` with
`q' ≥ 1` (the images of the differentials into the bottom row), and the resulting quotient `E∞ p 0` is a
graded piece of a filtration of `H p`. The theorem module `Theorems.Thm_DoubleComplex_boundedSpectralSequence`
states this as `DoubleComplex.boundedSpectralSequence` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…DoubleComplex`. It constructs the needed part of the spectral sequence by
hand, using zigzags in the total complex. Fix `D` with differentials `dH`, `dV` and total complex `Tot D`
(entries at `(a, q)` with `a + q = n`).

1. **Column filtration** (section `FilTot`). `FilTot p n` is the set of total `n`-cochains that vanish in all
   columns `a < p` (`mem_FilTot`). It is antitone in `p` (`FilTot_antitone`), equals `⊤` for `p = 0` and `⊥`
   for `p = n + 1` or `p = D.N` (`FilTot_zero`, `FilTot_top`, `FilTot_N`), and `dTot` preserves it
   (`dTot_FilTot_le`). `leOfSubsingleton` is the equivalence between two trivial modules.
2. **Edge slot** (section `Edge`). In degree `p`, `FilTot p p` consists of the cochains concentrated at
   `(p, 0)` (`edgeSlot`, `edgeSingle`, `edgeProj`). Such a cochain is a total cocycle iff its entry is killed
   by `dH` and `dV` (`edge_ker_fwd`, `edge_ker_rev`).
3. **Edge cocycles and `E₂`** (section `KerHV`). `KerHV p = ker dH ∩ ker dV` in `C p 0`, and `FilH p n` is the
   image in `HTot D n` of the total cocycles in `FilTot p n` (`FilH_zero`, `FilH_top`). `toE₂ p` sends
   `KerHV p` onto `E₂I D p 0` (`toE₂_surjective`).
4. **Zigzags** (section `ZigZag`). `zigTarget p` is the set of total `p`-cochains `b` whose coboundary is
   concentrated at `(p + 1, 0)`. Its entry there, `zigOut b`, lies in `KerHV (p + 1)` (`zigOut_apply`,
   `dTot_eq_edgeSingle_zigOut`, `zigOut_mem_KerHV`). `A r p` is the set of such zigzags that vanish in columns
   `< p + 1 − r`, and `B r p` is the image of `zigOut` on `A r p` in `E₂I D (p + 1) 0`. The submodules `B r p`
   increase with `r` (`B_mono`), and `B 0 p = B 1 p = ⊥` (`B_zero`, `B_one`). They play the role of the images
   of the differentials `d₂, …, d_r`.
5. **Graded pieces of `B`** (`B_gr_subquot`). Let `a + q' + 1 = p`. For a zigzag in `FilTot a p`, its entry at
   `(a, q' + 1)` is a vertical cocycle whose class is a horizontal cocycle (`θ_mem_ker_dV`, `θ_dH_mem_colB`).
   This defines `ψ` into `E₂I D a (q' + 1)`. If `ψ b = 0`, subtracting a suitable total coboundary pushes the
   zigzag one column to the right without changing `zigOut` (`sub_dTot_mem_zigTarget`, `zigOut_sub_dTot`,
   `mem_FilTot_succ_iff`, `core_mem_B_pred`), so the class already lies in `B (q' + 1) p`. Hence `φ` (into
   `B (q' + 2) p / B (q' + 1) p`) factors through the range of `ψ`, and this graded piece is a subquotient of
   `E₂I D a (q' + 1)`.
6. **The filtration of `E₂ p 0`** (section `Bfilt`). `Bfilt (p + 1) i = B (i + 1) p` and `Bfilt 0 = ⊥`.
   `Bfilt_gr` uses step 5, or triviality once `i + 1 > p`.
7. **`E∞` and the edge isomorphism** (section `Hfilt`). `Einf p 0` is `E₂I D p 0` modulo the top of `Bfilt p`,
   and `Einf p (q + 1)` is trivial. The maps `τ : KerHV p → FilH p p` and `σ : KerHV p → Einf p 0` are
   surjective and have the same kernel: an edge cocycle is a total coboundary iff its `E₂` class is hit by a
   zigzag (`dTot_edgeSingle_of_ker_dV`). This gives `FilH_edge_iso : FilH p p ≅ Einf p 0`.
8. **The filtration of `H n`.** `Hfilt n` is `⊥`, then `FilH n n` at step `n + 1`, then `⊤` (all of it trivial
   bookkeeping when `n ≥ D.N`). `Hfilt_gr` identifies the step-`p + 1` piece with `Einf p 0` by
   `FilH_edge_iso`, and both sides are trivial when `p = D.N` (`D.hBound`).
9. `boundedSpectralSequence` assembles these fields into a `Convergence`, and `solution` is that theorem.

## Provenance and licence

This file is a port of `P2M/Sol/S_DoubleComplex_boundedSpectralSequence.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_DoubleComplex` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_DoubleComplex`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed. These
  replacements change no declaration, statement or proof step.
