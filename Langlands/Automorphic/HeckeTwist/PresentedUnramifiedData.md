# Unramified data after multiplication by any Hecke determinant character

Author: Worker 5136.

The Library's unramified data `D : P.UnramifiedData hS T` of a finite tensor
presentation `P` of a nonzero finite realization `S` of `GL_{r+1}` record, at
every finite place `v` outside a finite set `T`, that the local factor is
irreducible and admissible and that its local component has a spherical Hecke
spectrum with given Satake parameters. For an arbitrary Hecke character `χ`, this
internal module transports such data to the twisted presentation
`P.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.FiniteTensorTwist`).

- Private lemma `actualSpectrum_of_equiv`: a spherical Hecke spectrum of an
  irreducible admissible local realization passes to any equivalent local
  realization (the Library's `hasSphericalHeckeSpectrum_iff_of_equiv`).
- `FiniteTensorPresentation.UnramifiedData.heckeDeterminantTwist D χ`:
  unramified data of the twisted presentation outside
  `T ∪ χ.finiteHeckeDeterminantTail (r + 1)`. The twisted local factors are
  irreducible (the Library's `isIrreducible_twist_iff`) and admissible
  (`isAdmissible_twist_iff`, with the open kernel
  `finiteLocalHeckeDeterminant_isOpen_ker` of module `Admissibility`). The
  Satake parameters are scaled by `χ_v(ϖ_v)` (`Eigenvalues.scale`). The
  spectrum of the twisted component comes from
  `hasSphericalHeckeSpectrum_heckeDeterminantTwist_outside_tail` (module
  `LocalSphericalSpectrum`). It is moved to the component of the twisted
  presentation by `heckeDeterminantTwistPresentationLocalComponentEquiv`
  (module `FiniteTensorComponents`).
- `heckeDeterminantTwist_eigenvalues`, `_powerTrace`, `_eulerPolynomial`: at
  such `v`, the parameters are scaled, the `k`-th power trace is multiplied by
  `χ_v(ϖ_v)^k`, and the Euler polynomial `P_v(X)` becomes `P_v(χ_v(ϖ_v) X)`.
- `heckeDeterminantTwist_spectralSystem`: the new spectral system is the scaled
  system of `D` (`SpectralSystem.scale χ.finiteUniformizerValue`) restricted to
  the places outside the enlarged set.
- `samePowerTraces_heckeDeterminantTwist`,
  `sameEulerPolynomials_heckeDeterminantTwist`: the new system has the same
  power traces and Euler polynomials as the scaled system of `D` at almost every
  place.
- `heckeDeterminantTwist_samePowerTraces_scale_iff` and
  `heckeDeterminantTwist_sameEulerPolynomials_scale_iff`: for any spectral
  system `t`, the new system agrees almost everywhere with the scaling of `t`
  if and only if the system of `D` agrees almost everywhere with `t`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.PresentedDeterminantUnramifiedData` with the finite-order
hypothesis removed. The scaling of Satake parameters by `χ_v(ϖ_v)` is the
unramified case of the local twist `(χ_v ∘ det) ⊗ π_v` in Henniart (2000), §2.2.
No further correspondence with a particular passage of the literature is
claimed.
