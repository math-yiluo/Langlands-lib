# Joint admissibility of unitary cuspidal realizations

Module: `Langlands.Automorphic.CuspidalAdmissible.JointAdmissibility`. Provenance: internal;
the final assembly of the joint admissibility proof and of contragredient existence.

- `isJointlyAdmissible_of_siegelFiniteness hSF T hT`: given Siegel finiteness for the adelic
  `GL_n` Siegel sets (`SiegelSetGLFinitenessStatement`), every actual cuspidal realization `T`
  (rank `r + 1`) over a number field with compact adele quotient and with unitary central
  character is jointly admissible. Proof: with the Borel structure on `GL_{r+1}(𝔸)`, the
  Library's band cover (`exists_band_cover`, `memLp_band_of_cover`) shows that realized vectors
  are square integrable over the band, so the band unitary form `unitaryForm` is defined; its
  square norm is the band integral (`bandNorm_eq_ofReal_inner`), so `separating_of_bandNorm`
  gives the separation property, and `isJointlyAdmissible_of_separating` (module
  `AdmissibilityReduction`, using irreducibility of `T`) concludes.
- `contragredientExistence_of_siegelFiniteness hSF`: given Siegel finiteness,
  `CuspidalUnitaryContragredientExistenceStatement` holds, by
  `contragredientExistence_of_isJointlyAdmissible` (module `ContragredientAssembly`).
