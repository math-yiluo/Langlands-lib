# Normalizing a cuspidal realization on the split centre

The module proves `NormPowerTwist.exists_normPower_twist` for actual
cuspidal realizations of positive rank over a number field with the Library's
adelic quotient compactness hypothesis. It returns a complex parameter `λ`
such that twisting by `HeckeCharacter.normPower F (-λ)` through the
determinant makes the realization trivial on the split centre. The twist and
its conjugate both have unitary central characters and are trivial on the
split centre. The conjugate realizes the full operator contragredient.

An irreducible realization has a continuous central character. Its
restriction to the positive archimedean scalar ideles is `exp(μ u)` in
logarithmic coordinates by `ContinuousCharacterReal.exists_eq_exp`. The norm of
that idele is `exp([F : ℚ] u)` and the determinant of a scalar in rank
`r + 1` raises it to power `r + 1`. Thus the choice
`λ = μ / ([F : ℚ] (r + 1))` cancels the central character on those scalars.
The published split-centre unitarity theorem and the unitary conjugation
criterion supply the assertions about unitarity and the contragredient.

`NormPowerTwist.finiteUniformizerValue_normPower` computes `qᵥ^(−s)` for the
complex power `s`, by the published norm of the chosen uniformizer, `qᵥ⁻¹`.
This supplies the local scalar in the trace twist comparison.

Jacquet–Shalika II, Theorem 4.2, printed pp. 806–807 (PDF pp. 31–32),
displays (1) and (4), uses the real norm power that normalizes unitarity.
Removing the phase too aligns the twist with the split-centre hypothesis of
the Library's pair pole statement.
