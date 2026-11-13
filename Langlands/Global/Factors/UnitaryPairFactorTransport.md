# Supercuspidal pair-factor relations along an isomorphism of p-adic fields

Author: Worker 5731. This is a supporting lemma module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement` (Task 5230).
It states no new published mathematics. It lifts the p-adic results of
`Langlands.Representation.RankinSelberg.FieldTransport.Padic` from
representations to the published supercuspidal classes, to the unitary basis
classes, and to the pair-factor relations on unitary virtual supercuspidal
classes used by `Langlands.Global.Factors.RelativeIsometryFactorStatement`.

Throughout, `F` and `E` are p-adic fields (`PadicField p`, canonical topologies)
and `f : F.Carrier ≃ₐ[ℚ_p] E.Carrier`. As in the published module
`Langlands.VirtualRepresentation.Supercuspidal.FieldTransport`, classes over `E`
are pulled back to classes over `F`, so the published bijections
`unitaryBasisEquiv F E f` and `unitaryLatticeEquiv F E f` go from `E` to `F`.
The additive characters `ψ` (of `F`) and `ψ'` (of `E`) and the additive Haar
measures `ν`, `ν'` are related by

- `hψ : ∀ x, ψ' (f x) = ψ x` and
- `hν : ν'.measure = ν.measure.map f` (for the canonical topologies and Borel
  σ-algebras).

## Supercuspidal classes

In namespace `Langlands.Correspondence`:

- `padicClassPullback f n` is the published class pullback
  `GeneralLinear.SupercuspidalClass.fieldPullback f.toRingEquiv`, for the
  canonical topologies and the continuity of `f` and `f.symm` from the
  published `VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv`.
- `isSupercuspidalPairLPolynomial_padicClassPullback_iff hψ hν π τ P`: for
  supercuspidal classes `π` of rank `r + 1` and `τ` of rank `n + 1` over `E`,
  the published `IsSupercuspidalPairLPolynomial F ψ ν` holds for the
  pulled-back classes exactly when `IsSupercuspidalPairLPolynomial E ψ' ν' π τ P`
  holds.
- `isSupercuspidalPairEpsilonFactor_padicClassPullback_iff hψ hν π τ e` is the
  same for `IsSupercuspidalPairEpsilonFactor`.

Both relations are defined by lifting the published symmetric p-adic relations
`IsPadicSymmetricLPolynomial` and `IsPadicSymmetricEpsilonFactor` from
representatives to classes. On representatives `A`, `B` the pullback of a class
is represented by the published `SupercuspidalRep.fieldPullback`, whose
representation is `A.obj.representation ∘ padicGeneralLinearEquiv F E f`
(definitionally), so each statement is
`isPadicSymmetricLPolynomial_comp_iff` (respectively
`isPadicSymmetricEpsilonFactor_comp_iff`) after `Quotient.inductionOn₂`.

## Unitary basis classes and unitary lattices

In namespace `Langlands.VirtualRepresentation.PadicSupercuspidal`:

- `unitaryBasisEquiv_val`: `unitaryBasisEquiv F E f b` keeps the rank of `b` and
  pulls back its class by `padicClassPullback f`.
- The imported `unitaryLatticeEquiv_eq_equivMapDomain` from
  `Langlands.VirtualRepresentation.Supercuspidal.FieldTransportLattice`: `unitaryLatticeEquiv F E f x` is the
  relabelling `Finsupp.equivMapDomain (unitaryBasisEquiv F E f) x` of the
  multiplicities of `x`. `unitaryBasisEquiv_mem_support_iff` deduces that the
  image of `b` lies in the support of the image of `x` exactly when `b` lies in
  the support of `x`.
- `isUnitaryBasisPairLPolynomial_unitaryBasisEquiv_iff hψ hν a b P` and
  `isUnitaryBasisPairEpsilonFactor_unitaryBasisEquiv_iff hψ hν a b e`: the
  published relations `IsUnitaryBasisPairLPolynomial` and
  `IsUnitaryBasisPairEpsilonFactor` hold over `F` for the images of `a` and `b`
  exactly when they hold over `E` for `a` and `b`. The ranks of basis classes are
  positive, so they are `r + 1` and `n + 1`, and the statements are those of the
  previous section.
- **`isUnitaryPairLFactor_unitaryLatticeEquiv_iff hψ hν x y L`**: for unitary
  virtual classes `x`, `y` over `E` and `L : RatFunc ℂ`,

  `IsUnitaryPairLFactor F ψ ν (unitaryLatticeEquiv F E f x) (unitaryLatticeEquiv F E f y) L ↔
   IsUnitaryPairLFactor E ψ' ν' x y L`.

  The published relation asks for a family `P a b` of JPSS L-polynomials on the
  pairs of basis classes in the supports, with `L` the multiplicity-weighted
  product of the factors `1 / P a b`. A family `P` over `F` gives the family
  `(a, b) ↦ P (u a) (u b)` over `E`, where `u = unitaryBasisEquiv F E f`, and a
  family over `E` gives `(a, b) ↦ P (u⁻¹ a) (u⁻¹ b)` over `F`. Supports
  correspond by `unitaryBasisEquiv_mem_support_iff`, the basis relations by the
  previous item, and the products by Mathlib's `Finsupp.prod_equivMapDomain`.
- **`isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff hψ hν x y e`**: the
  same for the published `IsUnitaryPairEpsilonFactor`, whose value is the
  multiplicity-weighted product of the constants and sum of the exponents of
  the basis epsilon factors; it also uses `Finsupp.sum_equivMapDomain`.
- `isUnitaryPairLFactor_unitaryLatticeEquiv_iff_transport f ψ ν x y L` and
  `isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff_transport f ψ ν x y e`
  specialize the two previous statements to the published transported data
  `ψ' = PadicField.ConductorTransport.additiveCharacter F E f ψ`
  (with `ψ' y = ψ (f⁻¹ y)`) and
  `ν' = PadicField.AbelianTransport.haarMeasure F E f ν` (whose measure is
  `ν.measure.map f` by definition), for which `hψ` and `hν` hold.
