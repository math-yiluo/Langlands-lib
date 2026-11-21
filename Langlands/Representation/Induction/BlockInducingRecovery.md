# Recovering irreducible admissible inducing data for a standard block parabolic

For a nonarchimedean local field `F`, a block shape `B` of `n`, and a smooth
complex representation `Ξ` of the Levi `B.Levi F`,
`Langlands.GeneralLinear.BlockShape.isIrreducible_isAdmissible_of_smoothInduced`
proves that `Ξ` is irreducible and admissible if the unnormalized smooth
induction of `Ξ.comp (B.leviProjection F)` is irreducible and admissible.
The field and representation-carrier universes are independent and this
lemma does not assume characteristic zero or that the parabolic is proper.

The Library supplies nonarchimedeanness and local compactness of `GL_n(F)`.
The Levi projection is a continuous surjection: its section is the inclusion
of the block diagonal Levi. It is open since it is the second projection in
the parabolic decomposition homeomorphism. Therefore inflation of `Ξ` is
smooth. The two reflection arguments proceed as follows:

- `Induction.isIrreducible_of_smoothInduced` from
  [`IrreducibilityReflection`](IrreducibilityReflection.md) first gives
  irreducibility of the inflated representation. Then
  `Induction.isIrreducible_of_comp_surjective` reflects irreducibility along
  the Levi projection.
- `Induction.isAdmissible_of_smoothInduced` from
  [`InducingRepresentationRecovery`](InducingRepresentationRecovery.md)
  gives admissibility of the inflated representation. The Library's
  `isAdmissible_comp_iff_of_open_surjective` reflects admissibility back
  along the open, continuous, surjective Levi projection.

`Langlands.GeneralLinear.BlockShape.exists_blockScalarCharacter` applies to
any irreducible admissible `Ξ` of this Levi. The Library's admissible Schur
lemma gives a central character. Composing it with `B.blockScalarToCenter F`
gives a homomorphism \(\chi : (F^\times)^{B.\mathrm{length}} \to
\mathbb C^\times\) acting by scalars on `Ξ`. Irreducibility gives a
nontrivial carrier. `Classification.HasScalarCharacter.isOpen_ker` applied
to the continuous block-scalar map and smooth `Ξ` gives an open kernel for
`χ`. This does not assert that `χ` is unitary.

These are internal compositions of the Library's induction, Levi inflation,
and Schur results. They supply the inducing-representation hypotheses used in
the square-integrable non-induction proof.
