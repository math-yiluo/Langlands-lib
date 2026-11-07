# Actual local unitarity of cuspidal presentations: proof

`Langlands.Automorphic.cuspidalUnitaryLocalUnitarity` proves the Library statement
`Langlands.Automorphic.CuspidalUnitaryLocalUnitarityStatement.{uF, uQ}` at both independent
universe levels. Its conclusion is that every irreducible admissible actual local component
of every spectral presentation of a cuspidal operator realization with unitary central
character admits an invariant positive definite Hermitian form on its original carrier.
This is the local unitarity input used at the start of Henniart (2000), Appendix A.2.

## The implemented proof

Fix `F`, `r`, a cuspidal realization `T` (so `T.realization : OperatorRealization F (r + 1)`
and `T.cuspidal : T.realization.IsCuspidal`), a presentation `P`, a finite place `v`, and
the irreducibility and admissibility proofs `hI`, `hA`.

1. The premise `HasUnitaryCentralCharacter T` is unpacked into a continuous idele-class
   character `χ` with `‖χ x‖ = 1` and `T.HasCentralCharacter χ`.
2. `AdelicGL F (r + 1)` is given its Borel σ-algebra (`borel`, with `BorelSpace` by `rfl`).
   This is the measurable structure required by the Library's
   `OperatorDeterminantSlice.matrixHaarMeasure`.
3. `OperatorRealization.exists_band_cover` (module
   `Langlands.Automorphic.CuspidalL2.SiegelCover`) is applied to `T.realization`,
   `T.cuspidal`, `lo = 1` and `hi = 2`. It gives a measurable set `t` with two properties:
   - every adelic matrix `x` with `1 ≤ absDet x ≤ 2` has a rational `γ` with
     `rational γ * x ∈ t`;
   - for every left-invariant measure finite on compact sets, and every realized vector `f`,
     `∫⁻ x in t, ‖ev f x‖ₑ ^ 2` is finite.

   Here `absDet x` is definitionally the real coercion of
   `AdelicBlockDeterminantCharacter.determinantNorm F (r + 1) x`, so the first property is
   exactly the covering hypothesis below. The second property is used for the Haar measure
   `matrixHaarMeasure`, which is left invariant and finite on compact sets because it is a
   Haar measure.
4. The Library construction
   `CuspidalSpectralPresentation.padicUnitaryFormOfCover` (module
   `Langlands.Automorphic.CuspidalSpectralUnitaryForm`) takes `χ`, the covering set `t`
   and these two hypotheses. It returns an `InvariantPositiveForm` on the representation of
   `((P.localComponent v).padicObject hI hA).obj`, under the canonical p-adic topology of
   `v`. Through `finiteInvariantPositiveFormOfCover`, it uses the cover to obtain the band
   square integrability, builds the Petersson-type form on the original finite action, and
   restricts that form to the prescribed local component.
5. `IsUnitarizable` is `Nonempty` of such a form, so the anonymous constructor finishes the
   proof.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`. The analytic content is
in the `CuspidalL2` modules. These prove rapid decay along maximal blocks from the vanishing
constant terms (`Representation`, `Decay`), and then decay on a Siegel set and the
countable compact cover (`SiegelCover`, `CompactCover`). The construction of the form from
the cover is in the Library modules `OperatorDeterminantSliceHaar` and
`CuspidalSpectralUnitaryForm`.
