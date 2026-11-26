# The Fourier transform of distributions for an invariant pairing

The module `Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier` defines, for a
nonarchimedean local field `F`, a nontrivial continuous unitary character `ψ` of `F`, a
finite-dimensional `F`-vector space `V` with its module topology, a symmetric nondegenerate
bilinear form `B` on `V` and an additive Haar measure `μ` on `V`, the Fourier transform

`f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`

of Schwartz–Bruhat functions and the Fourier transform `T̂(f) = T(f̂)` of distributions. It also
defines invariant pairings on an `F`-algebra.

## Content

Universes: `F : Type u`, `V : Type v` (and the algebra `A : Type v`), independent.

- `pairingCharacter ψ B : V → V → ℂ`, `(Y, X) ↦ ψ(B(Y, X))`, with `ψ` a
  `UnitaryAdditiveCharacter F` (continuous, nontrivial, unit-circle valued) viewed in `ℂ`
  (`pairingCharacter_apply`).
- `isSelfDualBicharacter_pairingCharacter ψ hs hnd`: for `B` symmetric (`hs : B.IsSymm`) and
  nondegenerate (`hnd : B.Nondegenerate`, Mathlib's left- and right-separating form), the
  bicharacter is self-dual in the Library's sense (`IsSelfDualBicharacter`). This is the
  self-duality certificate the Fourier operator uses. Proof: the Library theorem
  `isSelfDualBicharacter_of_symm` with `ψ.continuous_complex`, `ψ.norm_complex`,
  `ψ.complex_ne_one`, the symmetry `hs.eq` and the right-separating half `hnd.2`.
- `pairingFourierSB ψ hs hnd μ : SchwartzBruhat V →ₗ[ℂ] SchwartzBruhat V`: the Library's
  `bicharacterFourierSB` for the measure `μ.measure` of an `AdditiveHaarMeasure V` and the
  certificate above (the topological additive group structure of `V` is
  `IsModuleTopology.isTopologicalAddGroup`). `pairingFourierSB_apply`:
  `f̂(Y) = ∫ X, ψ(B(Y, X)) * f(X) ∂μ`. That the transform of a Schwartz–Bruhat function is again
  one is the Library's `bicharacterFourier_mem`.
- `distributionFourier ψ hs hnd μ : Distribution V →ₗ[ℂ] Distribution V`: the transpose
  (`LinearMap.dualMap`) of `pairingFourierSB`, so that
  `distributionFourier ψ hs hnd μ T f = T (pairingFourierSB ψ hs hnd μ f)`
  (`distributionFourier_apply`).
- `IsInvariantPairing B` for a bilinear form `B` on an `F`-algebra `A`: `B.IsSymm`,
  `B.Nondegenerate` and `B(u X u⁻¹, u Y u⁻¹) = B(X, Y)` for every unit `u` and all `X, Y`
  (`conj_invariant`), that is, invariance under the adjoint action of `Aˣ` on its Lie algebra.

## Sources and conventions

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Introduction, printed p. 2 (PDF p. 17): "Fix a symmetric, nondegenerate, `G`-invariant bilinear
form `B` on `g` with values in `Ω` … Also fix a character `χ ≠ 1` of the additive group of `Ω`.
Let `dX` denote a Haar measure on the additive group of `g` and define
`f̂(Y) = ∫_g χ(B(Y, X)) f(X) dX` … For any distribution `T` on `g`, define the distribution `T̂`
by `T̂(f) = T(f̂)`." The transform here is this one, with `ψ` for `χ`, the plus sign, and any
additive Haar measure (no normalization is imposed; by the Library's
`exists_pos_bicharacterFourier_bicharacterFourier`, `f̂̂ = C f(-·)` with a constant `C > 0`,
equal to `1` exactly for the self-dual measure). Harish-Chandra's `χ` is a nontrivial
character of the additive group of `Ω`, tacitly continuous and unitary; the Library's
`UnitaryAdditiveCharacter` makes both conditions explicit.

Clozel, *Characters of non-connected, reductive p-adic groups*, Canad. J. Math. 39 (1987),
source ID `clozel-1987-nonconnected-characters` (PDF page = printed page − 148), §3.4, printed
p. 155 (PDF p. 7): with a nondegenerate invariant bilinear form `B` on `m` and a nontrivial
character `χ` of `k`, "the Fourier transform is defined by means of `χ(B(X, Y))`".

## Scope

The Fourier operator needs only symmetry and nondegeneracy of `B` and a finite-dimensional
`V`; conjugation invariance enters through `IsInvariantPairing` in the statements that use the
transform. The module constructs no invariant pairing. For a finite-dimensional semisimple
algebra `A` over a field of characteristic zero one is the trace form `(X, Y) ↦ Tr_{A/F}(XY)`
of the regular representation (Harish-Chandra, p. 2: "Since `G` is reductive, such a `B`
exists"); this module does not prove that.
