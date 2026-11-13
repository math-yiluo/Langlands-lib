# Central characters of cuspidal realizations from the top Satake coefficient

Author: Worker 5137.

This module provides the automorphic half of the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement` (Task 5210).
The other half, from Worker 5151, constructs the Hecke character `δ` of `det S` and checks
the hypothesis below at almost every place. The result is the standard fact that the central
character of an irreducible automorphic representation is determined by its unramified
local components: at an unramified place `v`, the central character is `δ_v` exactly when
`ϖ_v` acts by `δ_v(ϖ_v)`, the product of the Satake parameters. The proof below avoids
Schur's lemma for the whole representation and the rigidity of Hecke characters. Instead
it uses irreducibility at one place at a time, together with weak approximation
(`Langlands.Global.IdeleDensity.eq_top_of_isClosed`).

`F` is a number field with `CompactSpace (AdeleQuotient F)`. `T : CuspidalOperatorRealization F r` is
an irreducible cuspidal realization of rank `r + 1`, `P` is a cuspidal spectral presentation
of `T`, and `δ : HeckeCharacter F`. For a finite place `v`, `ϖ_v` is the canonical uniformizer
`LocalFactor.PadicAbelian.uniformizerUnit (padicField v).canonicalTopologicalData`, and
`δ.finiteUniformizerValue v = δ_v(ϖ_v)`.

## Main theorem

`Langlands.Automorphic.CuspidalOperatorRealization.hasCentralCharacter_of_eventually_elementaryCoefficient`:
suppose that for all but finitely many finite places `v`
(`∀ᶠ v in Filter.cofinite`), `δ` is unramified at `v` (`δ.IsUnramifiedAt v`), `v` is not
exceptional for `P` (`hs : v ∉ P.spectralSystem.exceptional`), and
`δ_v(ϖ_v) = elementaryCoefficient (P.spectralSystem.eigenvalues v hs) (r + 1)`, the top
elementary symmetric function (the product) of the Satake parameters of `P` at `v`. Then
`T.HasCentralCharacter δ`.

Proof. By `hasCentralCharacter_of_centralCharacterSubgroup_eq_top` it suffices that the
subgroup `H = T.realization.centralCharacterSubgroup δ` of ideles whose scalar matrices act
by `δ` is everything. `H` is closed and contains the principal ideles
(`isClosed_centralCharacterSubgroup`, `diagonalUnits_mem_centralCharacterSubgroup`). Let
`S₀` be the finite set of places where the hypothesis fails. At every finite place outside
`S₀`, `finiteIdeleInclusion_mem_centralCharacterSubgroup` shows that `F_v^×` lies in `H`.
Hence `H = ⊤` by `IdeleDensity.eq_top_of_isClosed`.

## Local lemmas (namespace `CuspidalOperatorRealization`, section `Local`)

Each lemma fixes a finite place `v` with `v ∉ P.exceptional` (which is
`P.spectralSystem.exceptional` by definition). The section uses the canonical topology on
`GL_m(F_v)`, as `ContragredientSphericalSpectrum` does. By
`CuspidalSpectralPresentation.exists_spherical_ne_zero`, `T` has a nonzero vector `b` fixed
by `GL_(r+1)(𝒪_v)` for the local restriction at `v`.

- `finiteIdeleInclusion_units_mem_centralCharacterSubgroup`: if `δ` is unramified at `v`,
  every integral unit `u ∈ 𝒪_v^×` lies in `H` (through `finiteIdeleInclusion`). The scalar
  matrix of `u` lies in `GL_(r+1)(𝒪_v)`; this is checked entrywise for it and its inverse
  through `localIntegral_eq_sphericalSubgroup` and `mem_localIntegral`. So it fixes `b`.
  Also `δ_v(u) = 1` because `δ` is unramified. So the scalar matrix acts by `δ_v(u)` on `b`,
  hence on everything (`localScalar_eq_smul_of_ne_zero`). Then
  `finiteIdeleInclusion_mem_centralCharacterSubgroup_iff` applies.
- `finiteIdeleInclusion_uniformizer_mem_centralCharacterSubgroup`: if
  `δ_v(ϖ_v) = elementaryCoefficient (P.spectralSystem.eigenvalues v hv) (r + 1)`, then `ϖ_v`
  lies in `H`. On `b`, the scalar matrix of `ϖ_v` is the top standard diagonal
  (`standardDiagonal_last`). It therefore acts as the top standard Hecke operator
  (`standardHecke_cornerAction_last`), which acts on `b` by the standard Hecke scalar of the
  presented spectrum (`CuspidalSpectralPresentation.corner_eq_smul`). That scalar is the top
  elementary coefficient (`standardHeckeScalar_last`), which equals `δ_v(ϖ_v)` by
  hypothesis. Irreducibility and the membership criterion conclude as before.
- `finiteIdeleInclusion_mem_centralCharacterSubgroup`: under both hypotheses, every
  `a ∈ F_v^×` lies in `H`. The preimage of `H` in `F_v^×` contains the integral units and
  `ϖ_v`, so it is everything (`CompletionPadic.subgroup_eq_top_of_uniformizer_mem`).

Unlike `OperatorScalarCentralCharacter`, this file does not set
`backward.isDefEq.respectTransparency false`. With that option, elaborating the statements of
this section did not terminate.
