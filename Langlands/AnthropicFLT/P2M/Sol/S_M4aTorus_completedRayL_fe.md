# Analytic continuation and functional equation of completed ray class L-functions: proof

This module proves `solution`, the statement of `M4aTorus.completedRayL_fe` (see that wrapper module), by Hecke's theta-function method. Its 12,126 source lines are in the namespace `P2MW.S_M4aTorus_completedRayL_fe`. They contain the following steps.
- Finite-dimensional Poisson summation with the actual lattice covolumes and trace-dual lattices. The dual of the Euclidean ideal lattice is identified with the trace dual of the ideal.
- Fourier transforms of Gaussians weighted by odd polynomials, and weighted Poisson summation on cosets.
- Invariance of the finite character under congruences, independence of the Gauss sum from the Gauss datum, and orthogonality of finite characters.
- Placewise scaling, unit-domain tiling and unfolding of the Mellin integral to integral ideals, with the torsion multiplicity, the regulator and the gamma factors Γ_ℝ(s), Γ_ℝ(s + 1) and Γ_ℂ(s)/2.
- Integrability, Gaussian tail bounds and dominated differentiation of the high and dual halves.
- General inversion and polar cancellation for nontrivial χ, by odd parity, by orthogonality, or by descent to a nontrivial ordinary class-group character through the moving lemma. The cases 𝔣 = (1) and 𝔣 = 0 are treated separately.
- For primitive characters, the functional equation: first for Re s > 1 from the inversion formula, then on ℂ ∖ {0, 1} by the identity theorem.

Declaration names containing `Holes`, `hole_` or `SKELETON` are fully implemented ingredients, not assumptions.

Source: `P2M/Sol/S_M4aTorus_completedRayL_fe.lean` (entire file, 12126 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `077de9ef939c439d879313fb8fb68ce64f5bc61d8dca25813adc70d269d3d108`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 98 `p2m_open` commands by `open _root_.…`, 196 `p2m_reactivate` commands by `open scoped _root_.…`, 87 `p2m_export` commands by `export _root_.… (…)`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Compatibility with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (the source pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`): four applications of `Finset.prod_le_prod` (in `norm_polyS_le`, `raySummand_summable`, `exists_expMapBasis_lower` and `tail_bound_highHalf`) now use `Finset.prod_le_prod₀`; in `measurable_inv_realSpace`, `measurable_pi_lambda _ fun w => …` became `measurable_pi_iff.mpr fun w => …`; in `summable_setIntegral_foldDomain_rayOrbitKernel`, the finiteness bound `ne_top_of_le_ne_top hfin' (ENNReal.le_tsum p)` became `(ENNReal.lt_top_of_tsum_ne_top hfin' p).ne`.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binders of `E`, `M`, `d`, `α`, `ι`, `σ` (originally `Type`) are `Type*`; the 2 existential index types `ι` of the class-group assembly (originally `Type`) are `Type u`, the universe of K, since their witnesses are built from the class group of K. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
