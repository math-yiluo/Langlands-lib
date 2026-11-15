# The transpose-inverse twist by the long Weyl element

Internal helper module for the dual half of `UnequalUnfoldingReduction.md`.
Provenance: internal.

## Matrices

`dualConjGL n R g = w ᵗg⁻¹ w` with `w = weylLong` (`w⁻¹ = w`).
`dualConjGL_entry`: its `(i, j)` entry is `(g⁻¹)_{rev j, rev i}`.
`dualConjGL_dualConjGL` (involutive), `dualConjGL_map` (commutes with
entrywise ring homomorphisms), `isUnitriangular_dualConjGL`,
`sum_superdiag_dualConjGL` (the superdiagonal sum of the twist of a
unitriangular matrix is minus that of the matrix).

## Adelic points

`dualConj` is the twist on `GL_n(𝔸)`, `dualPoint g = w ᵗg⁻¹`, so that
the Library's `dualFunction F n f = f ∘ dualPoint` (`dualFunction_eq`)
and `dualPoint (x y) = dualConj x · dualPoint y` (`dualPoint_mul`).
Continuity: `continuous_dualConj`, `continuous_dualPoint`.
`dualConjUnipotent` is the induced automorphism of `N_n(𝔸)`, with
`genericCharacter_dualConjUnipotent`: `ψ_N(dualConj u) = ψ_N(u)⁻¹`.
`dualConj_rational`, `dualConj_mem_rationalSubgroup`: rational points
go to rational points. `mem_unipotentRationalImage_iff_mem_inf`:
`N_n(F) = GL_n(F) ∩ N_n(𝔸)`; hence `dualConjUnipotent_mem_rationalSubgroup`.

## Measure

`measurePreserving_dualConjUnipotent`: the twist preserves Haar
measure on `N_n(𝔸)`. The image of Haar is a multiple of Haar; the
twist maps the chosen fundamental domain of `N_n(F)` to another strict
fundamental domain (`existsUnique_mem_preimage_dualConjUnipotent`) of
the same finite positive mass, so the multiple is one.
`setIntegral_comp_dualConjUnipotent`: integrals of left
`N_n(F)`-invariant functions over the fundamental domain are unchanged
by the twist.

## Rectangular points

`lowerBlockPair_mul_left`, `reindex_rankInclusion_rankInclusion` and
`rectangularPoint_mul_left`: for the Library's
`rectangularPoint F h g x = [[g,0,0],[x,I,0],[0,0,1]]`,
`rect(n g, x) = diag(n, I) · rect(g, x)`.
