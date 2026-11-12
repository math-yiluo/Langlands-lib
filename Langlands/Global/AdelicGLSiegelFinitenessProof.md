# Siegel finiteness for the adelic `GL_n` Siegel sets

Module: `Langlands.Global.AdelicGLSiegelFinitenessProof`. Declaration:
`Langlands.Global.PrimitiveAdelicHeight.siegelSetGLFiniteness :
SiegelSetGLFinitenessStatement.{u}`.

This proves the Library statement `SiegelSetGLFinitenessStatement`
(module `Langlands.Global.AdelicGLSiegelFinitenessStatement`): for every number field `F`,
every `n`, every compact set `Ω_N` of upper unitriangular adelic matrices, every compact set
`C` of norm-one ideles and every `c > 0`, the set of rational `γ` with
`γ · siegelSetGL F n Ω_N C c ∩ siegelSetGL F n Ω_N C c ≠ ∅` is finite. The statement's
Markdown cites Godement (Séminaire Bourbaki 257, §10, Théorème 9, after Borel); the implemented
proof is an elementary `GL_n` argument with heights, not Godement's.

## Implemented proof

- `n = 0`: `GL_0(F)` has one element.
- `n > 0`: `exists_siegel_data` (module `Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry`) writes every Siegel point as `N diag(ω) A_x κ` with `x` in a
  chamber and `A_x⁻¹ h` in a compact set `Q₁`; `exists_key_bound` gives `β₀` for `Q₁`, and
  `β = max β₀ 0`. With `Λ` as in `entries_mem`, every rational `γ` with `γ h = h'` for Siegel
  points `h, h'` has all entries in the compact set `E = entrySet F n Ω_N C Λ`; applied to
  `γ⁻¹ h' = h`, so does `γ⁻¹`. Hence `rational γ` lies in the compact set
  `AdelicMatrixHeight.entryBox F n E` (entries of the matrix and its inverse in `E`,
  `isCompact_entryBox`), and `finite_rational_compact` (with the compact set `{1}`) shows that
  only finitely many rational matrices do.

The helper modules are `Langlands.Global.SiegelFiniteness.{Heights, BlockMatrices, Comparison,
CompactBlock, Finiteness, Entries}` and `Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry`.
