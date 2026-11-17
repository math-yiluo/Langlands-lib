# Transfer of spherical Hecke scalars through a contragredient pairing

Module `Langlands.Automorphic.ContragredientHeckeTransfer`. It imports
`Langlands.Automorphic.ContragredientSphericalSpectrum`.

Let `T` be an irreducible actual cuspidal realization. Let `Td` realize its
contragredient, and let `Pd` be a spectral presentation of `Td`. This module proves that
at every finite place `v` outside the exceptional set of `Pd`, **every** spherical vector
of `T` at `v` has the standard Hecke scalars of the inverse of the presented spectrum of
`Td` at `v`. No spectral presentation of `T` is used. The Library module
`ContragredientSphericalSpectrum` compares two presented spectra. Here only `Td` is
presented, and the conclusion is about the Hecke action on `T`.

## Main results

- `Langlands.Automorphic.CuspidalOperatorRealization.corner_eq_smul_of_contragredient_presentation`.
  Take `T Td : CuspidalOperatorRealization F r` with
  `Td.realization.IsContragredientOf T.realization`, a presentation
  `Pd : CuspidalSpectralPresentation Td` and `v ∉ Pd.exceptional`. For every
  `GL_(r+1)(𝒪_v)`-fixed vector `a` of the local restriction
  `T.realization.localRepresentation v` and every `i`, the corner action of the standard
  Hecke element `T_i` on `a` is `standardHeckeScalar ((eigenvalues of Pd at v).map (·⁻¹)) i • a`.
- `Langlands.Automorphic.OperatorRealization.corner_eq_smul_of_isContragredientOf`. The
  same for operator realizations `S` and `S'` of rank `r + 1` with
  `S'.IsContragredientOf S` and `S` irreducible. The hypotheses are that every spherical
  vector of `S'` at `v` has the standard Hecke scalars of a multiset `s`, and that `S'` has
  a nonzero spherical vector at `v`. The conclusion is that every spherical vector of `S`
  at `v` has the standard Hecke scalars of `s.map (·⁻¹)`.

## Auxiliary results

Local part, namespace `Langlands.Unramified.PairedHecke`, for smooth representations `ρ`
on `V` and `σ` on `W` of `GL_(r+1)(F)` over a canonical p-adic field and an invariant
pairing `B`, `B(ρ(g)x, σ(g)y) = B(x, y)`:

- `scalar_mul_pairing_eq` (adjointness). If the spherical vector `b` of `σ` satisfies
  `T_i ⋆ b = l'_i b` for all `i`, then for every spherical `a` of `ρ` and every `j`,
  `l'_j B(a, b) = l'_n B(T_(n-j) ⋆ a, b)`, with `n = r + 1` and `n - j = j.rev`. This is
  the computation of the Library's `PairedHecke.scalar_adjoint`. That lemma assumes that
  `a` is itself an eigenvector with `B(a, b) ≠ 0`. Here neither is assumed. The proof
  writes both sides as integrals (`functional_corner`), uses the inverse-transpose
  invariance of `sphericalHaar` and of the double cosets
  (`sphericalInverseTranspose_mem_doubleCoset_inv`), and translates by the central
  element `t_n`, which acts on `b` by `l'_n`.
- `standardHeckeScalar_map_inv_mul_last`:
  `λ_i(s⁻¹) λ_n(s) = λ_(n-i)(s)`. It compares the coefficients of the Euler polynomial
  of `s⁻¹` with those of the reversed Euler polynomial of `s`
  (`C_mul_eulerPolynomial_map_inv`).
- `corner_eq_smul_of_pairing`. Assume the left kernel of `B` is zero, every spherical
  vector of `σ` has the scalars `λ_i(s)`, and `a` is spherical for `ρ`. Then
  `T_i ⋆ a = λ_i(s⁻¹) a`. For `y ∈ W`, `B(T_i ⋆ a - λ_i(s⁻¹) a, y)` equals the same
  pairing with the spherical projection `b` of `y` (`pairing_sphericalProjection`). After
  multiplication by `λ_n(s) ≠ 0` it vanishes, by adjointness and the scalar identity. The
  left kernel is zero, so the difference is `0`.

Global part, namespace `Langlands.Automorphic.OperatorRealization`:

- `envelopingGenerator_mem_of_lieAction` and `envelopingAction_mem_of_lieAction`. A
  subspace stable under the real Lie algebra operators `lieAction X` is stable under the
  generators `ι(Y)`, `Y ∈ ℂ ⊗_ℝ 𝔤`, and hence under the whole enveloping algebra. The
  second lemma uses induction over the tensor algebra and surjectivity of the quotient map.
- `leftKernel B`, the subspace `{x | ∀ y, B x y = 0}`, and `mem_leftKernel`.
- `finiteRepresentation_mem_leftKernel`, `compactRepresentation_mem_leftKernel`,
  `lieAction_mem_leftKernel`. The left kernel of an invariant pairing is stable under the
  three families of operators.
- `eq_zero_of_isContragredientPairing`. Let `B` be a contragredient pairing of `S` with
  `T`, with `S` irreducible and `T` having a nonzero vector. Then the left kernel of `B` is
  zero. If not, it is a nonzero subspace stable under the generators, so it is everything
  (`eq_top_of_generatorStable`). Then `B.flip y₀ = 0` for a nonzero `y₀`, which
  contradicts injectivity of `B.flip`.

## Proof

`corner_eq_smul_of_isContragredientOf` takes the contragredient pairing `B` of `S` with
`S'`. Its invariance under the finite action restricts to invariance under the local
action at `v`. Its left kernel is zero by `eq_zero_of_isContragredientPairing`, since the
nonzero spherical vector `b` of `S'` makes `S'.Space` nonzero.
`PairedHecke.corner_eq_smul_of_pairing` then gives the claim.
`corner_eq_smul_of_contragredient_presentation` applies this to `S = T.realization` and
`S' = Td.realization`. The nonzero spherical vector of `Td` comes from
`CuspidalSpectralPresentation.exists_spherical_ne_zero`, the Hecke scalars of `Td` from
`CuspidalSpectralPresentation.corner_eq_smul`, and irreducibility from `T.irreducible`.

## Provenance

The fact that the unramified Satake parameters of `π̃_v` are the inverses of those of
`π_v` is standard. Henniart (2000), *A simple proof of the Langlands conjectures for GL(n)
over a p-adic field*, §2.2, uses it, as recorded in the Library modules
`PairedHeckeScalars` and `ContragredientSphericalSpectrum`. This module is an internal
derivation in the same style. It uses only Hecke adjointness under the invariant pairing
and irreducibility of `T`. It uses no Satake isomorphism, no multiplicity one and no
presentation of `T`. It serves the dual Whittaker splitting of
`Langlands.Global.RankinSelberg.ContragredientDualSplit`.
