# Ranges of homomorphisms from two different split tori

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. The Library's
`Langlands.GroupScheme.HomScheme.SplitTorusHopfPoint` compares the ranges of
two homomorphisms from the same Hopf spectrum (the same split torus
`D(ℤ^I)`) into an affine group `G` over `Spec R`. This module allows two
sources, `D(ℤ^I)` and `D(ℤ^{I'})`, which may have different ranks. The proofs
follow the Library's one-source versions (`range_transport_le_iff`,
`range_pointEquiv_symm_le_iff`, `range_pointEquiv_symm_le_iff_ker`,
`range_splitPointEquiv_symm_le_iff_ker` and
`range_splitPointEquiv_symm_eq_iff_ker`). The suffix `₂` marks the two-source
forms.

## Results

- `range_transport_le_iff₂`: let `eH : H₁ ≅ H`, `eH' : H₁' ≅ H'` and
  `eG : G ≅ G'`. Transport (the Library's `transport`) along these
  isomorphisms preserves and reflects inclusions of ranges of
  `i : RelativeHom H G T` and `i' : RelativeHom H' G T`. Conjugate a
  factorization by the underlying isomorphisms.
- `range_pointEquiv_symm_le_iff₂`: for Hopf points
  `f : A → C ⊗ P` and `f' : A → C ⊗ P'` (`FiniteSource.pointEquiv`), the range
  of the homomorphism of `f'` lies in the range of that of `f` exactly when
  some ring map `ψ : C ⊗ P → C ⊗ P'` satisfies `ψ ∘ f̃ = f̃'`. Here `f̃`
  denotes the linear extension `AlgHom.liftEquiv`. Range inclusion means
  factorization of the underlying scheme morphisms (`range_le_range_iff`).
  Between spectra, factorizations correspond to ring maps (`Spec.preimage`,
  `Spec.map_injective`).
- `range_pointEquiv_symm_le_iff_ker₂`: if `f̃` is surjective, the range
  inclusion holds exactly when `ker f̃ ≤ ker f̃'`. A ring map `ψ` gives the
  kernel inclusion. Conversely, factor `f̃'` through `C ⊗ A / ker f̃ ≅ C ⊗ P`
  (`Ideal.Quotient.lift`, `RingHom.quotientKerEquivOfSurjective`).
- `SplitTorusPoint.range_splitPointEquiv_symm_le_iff_ker₂`: the same
  criterion for homomorphisms from the split tori `D(ℤ^I)` and `D(ℤ^{I'})`
  given by `splitPointEquiv`. Unfold `splitPointEquiv` as a transport of
  `pointEquiv` and combine the two previous results.
- `SplitTorusPoint.range_splitPointEquiv_symm_eq_iff_ker₂`: two closed
  homomorphisms from split tori, of possibly different ranks, have the same
  range exactly when the kernels of the linear extensions of their Hopf points
  agree.
