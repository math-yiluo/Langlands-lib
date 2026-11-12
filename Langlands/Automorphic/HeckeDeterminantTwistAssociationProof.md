# Proof that weak association passes to twists by every Hecke character

Author: Worker 5137.

`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
proves the published proposition
`Langlands.ClassField.Global.RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement`
of `Langlands.Automorphic.HeckeDeterminantTwistStatement`. The theorem's type is exactly
`PresentedDeterminantMultipleAssociationStatement.{u, uV, uP, uQ}`, with all four
universes independent. No hypothesis is added: the arithmetic class family, the Galois
extension `E / F`, the rank, the representation `S`, the cuspidal realizations `T, T'`,
their presentations `P, P'` (in independent universes) and the Hecke character `χ` are
arbitrary; in particular `χ` need not have finite order or be unitary. The statement's
Lean/Markdown pair and its imported pairs are unchanged, and the proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Henniart (2000), §2.2: at an arithmetic class family `c`, if `S` is weakly associated with
the spectral system of a presentation `P` of `T`, and the realization of `T'` is the
determinant multiple of that of `T` by `χ`, then the twist `(χ ∘ τ_F) ⊗ S` (by
`reciprocityCharacter c F E χ`) is weakly associated with the spectral system of every
presentation `P'` of `T'`.

## Proof

The proof composes two results proved in the helper modules of this contribution.

1. Weil side (`RelativeWeilUnramifiedTwist`): `IsWeaklyAssociated.twist_scale` uses the
   `FundamentalClass.Restriction c` component of `IsArithmeticClassFamily c` and shows
   that `(χ ∘ τ_F) ⊗ S` is weakly associated with
   `SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem`, the system whose
   Satake parameters at `v` are those of `P` multiplied by `χ_v(ϖ_v)`. It rests on the
   computation of the transfer on local relative Weil maps at places of ramification
   index one (`RelativeWeilUnramifiedTransfer`, `LocalRelativeWeilUnramified`,
   `TransferCyclicQuotient`).
2. Automorphic side (`DeterminantMultipleSpectrum`):
   `CuspidalOperatorRealization.sameEulerPolynomials_scale_of_isDeterminantMultiple`
   shows that this scaled system and `P'.spectralSystem` have the same Euler polynomials
   at almost every place. It rests on the abstract spherical computation of
   `TwistedHeckeScalars`.

Weak association depends only on Euler polynomials outside a finite set
(`IsWeaklyAssociated.of_sameEulerPolynomials`, Library module
`Langlands.Automorphic.Unramified.IsobaricWeilAssociation`), which combines the two.

## Helper modules

- `Langlands/GroupTheory/TransferCyclicQuotient.lean`: the transfer to the subgroup of
  elements of degree divisible by `f`, at an element of degree one.
- `Langlands/ClassField/Global/LocalRelativeWeilUnramified.lean`: images of local Weil
  groups and inverse images of `C_E` at ramification index one.
- `Langlands/ClassField/Global/RelativeWeilUnramifiedTransfer.lean`: the transfer of the
  image of an element of degree one is the inverse class of an element of order one.
- `Langlands/ClassField/Global/RelativeWeilUnramifiedTwist.lean`: values of `χ ∘ τ_F`
  and the twisted association.
- `Langlands/Representation/Unramified/TwistedHeckeScalars.lean`: standard Hecke
  scalars of character twists of smooth representations.
- `Langlands/Automorphic/DeterminantMultipleSpectrum.lean`: spectra of determinant
  multiples.
