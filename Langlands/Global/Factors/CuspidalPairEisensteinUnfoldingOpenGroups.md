# The open cell as a semidirect product

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenGroups` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) writes the adelic upper unitriangular group
`N₀(𝔸)` of `GL_N`, `N = r + t + 2`, as the semidirect product `N₀ = N_(M') ⋉ U'`. Here `U'` is the
unipotent radical `{u'(Y) = [[I_(t+1), Y], [0, I_(r+1)]]}` of the upper parabolic with block sizes
`(t + 1, r + 1)`, and `N_(M') = N_(t+1) × N_(r+1)` is the upper unitriangular group of its Levi.
This is the two-block `GL_N` analogue of the splitting of `U` into `V` and the quotient `N^V` of `U`
by `V`, used for the open cell in Shahidi, *Functional equation satisfied by certain L-functions*,
Compositio Math. 37 (1978), proof of Lemma 2.1, paragraph after (2.10.3), p. 182. There Shahidi
works with split `G₂`, `U` is the unipotent radical of a fixed Borel subgroup, and `V = wPw⁻¹ ∩ U`.
For `GL_N` the counterpart of `U` is `N₀`. In the Library's left-quotient convention, obtained from
the source's right quotient `G_F/P_F` by inversion, the counterpart of `V` for the open class is
`N₀ ∩ w⁻¹ P w = N_(M')`.

## Block coordinates

- `swapBlocks r t : Fin (t + 1) ⊕ Fin (r + 1) ≃ Fin (r + t + 2)` puts the block of size `t + 1`
  first. `toSum` and `ofSum` reindex square matrices along it. They are multiplicative
  (`toSum_mul`, `toSum_one`), and `toSum_eq_fromBlocks` writes a matrix by its four blocks.
- Unitriangularity passes to and from the diagonal blocks (`isUnitriangular_toBlocks₁₁`,
  `isUnitriangular_toBlocks₂₂`, `isUnitriangular_ofSum`). The block maps are continuous
  (`continuous_toBlocks₁₁`, `continuous_toBlocks₁₂`, `continuous_toBlocks₂₂`).
- `toSum_openCellUnipotent`: in these coordinates `openCellUnipotent F r t Y` is
  `fromBlocks 1 Y 0 1`. It is unitriangular, with `u'(Y + Y') = u'(Y) u'(Y')` and `u'(0) = 1`
  (`openCellUnipotent_add`, `openCellUnipotent_zero`).

## The three homomorphisms

- `Radical F r t = Multiplicative (Matrix (Fin (t + 1)) (Fin (r + 1)) 𝔸)` and
  `LeviPart F r t = N_(t+1)(𝔸) × N_(r+1)(𝔸)`.
- `radicalHom : Radical →* N₀(𝔸)`, `Y ↦ u'(Y)` (`toMat_radicalHom`).
  `leviHom : LeviPart →* N₀(𝔸)`, `(A, B) ↦ diag(A, B)` in the swapped block coordinates
  (`toMat_leviHom`). `projHom : N₀(𝔸) →* LeviPart` takes the two diagonal blocks.
- `projHom_leviHom`: `projHom ∘ leviHom = id`. `projHom_radicalHom`: `projHom` kills `U'`.
  `exists_radicalHom_eq`: the kernel of `projHom` is the image of `radicalHom`. These are the
  hypotheses of the Library's split-extension constructions `LeftCosetSpace.Semidirect`.
- `continuous_radicalHom`, `isEmbedding_radicalHom`, `continuous_leviHom`,
  `continuous_projHom`.

## Rational points

- `mem_Γ₀_iff_entries`: a point lies in `N₀(F)` exactly when all entries of its matrix are
  rational. `isDiscrete_prod`: a product of discrete sets is discrete.
- `leviLattice F r t = N_(t+1)(F) × N_(r+1)(F)`, discrete (`isDiscrete_leviLattice`).
  `leviHom_mem_Γ₀` and `projHom_mem_leviLattice`: `leviHom` and `projHom` respect the rational
  points.
- `openLattice F r t = patternRational F N (openPivots r t)`, the stabilizer `Λ_(J₀)(F)` of
  the open cell. `leviHom_mem_openLattice`: it contains `leviHom (leviLattice)`.
  `radicalHom_mem_pattern_iff`: `u'(Y)` lies in the pattern group of `J₀` only for `Y = 0`.
  `comap_radicalHom_openLattice`: the preimage of `Λ_(J₀)(F)` in the radical is trivial.
  These two facts give the product fundamental domain of `Λ_(J₀)(F)` used in
  [CuspidalPairEisensteinUnfoldingOpen.md](CuspidalPairEisensteinUnfoldingOpen.md).
