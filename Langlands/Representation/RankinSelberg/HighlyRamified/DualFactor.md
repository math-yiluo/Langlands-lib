# Level membership of dual matrices and the lower-block factorization

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, the step from formula (5) to formula (9) using
condition (8), printed page 328).

- `rankInclusion_entry_mem_integer`: `diag(u,1)` is integral when `u` is.
- `dualConj_mem_levelSubgroup`: `M(u) = w ᵗdiag(u,1)⁻¹ w` lies in the published level
  subgroup `Conductor.levelSubgroup F (n+1) f` when `u` and `u⁻¹` are integral and the first
  column of `u⁻¹` is `e_0` modulo `𝔭^f`. The proof checks the entry conditions of the
  published criterion `mem_levelSubgroup_of_entries` through `dualConj_entry` and
  `dualConj_inv_entry`; the last row of `M(u)` is the reversed first column of `u⁻¹`.
- `natAdd_zero_eq_last`: index bookkeeping for one final row.
- `lowerBlockPair_eq_rankInclusion_mul`: the published lower-block representative
  `[[g,0],[x,h]]` (with one final row) equals `diag(g,1) · [[I,0],[x,h]]`.
- `dualConj_lowerBlockPair_one_mem`: `M([[I,0],[x,h]])` lies in the level-`f` subgroup when
  `x` is integral with `x_(0,0) ∈ 𝔭^f` and `h ∈ GL_1` is an integral unit. This is the
  source's condition (8): on the support of the weight, the lower unipotent part is absorbed
  by the invariance of the Whittaker function.
