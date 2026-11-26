import Langlands.Global.AdelicSpectralDecompositionReduction
import Langlands.Global.AdelicNonAssociateWavePacketOrthogonality
import Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof
import Langlands.Global.AdelicRelativeWavePacketDescentStatement
import Langlands.Global.AdelicWavePacketProductPairingProof
import Langlands.Global.AdelicPrincipalQuotientProductMeasureProof
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicSpectralBump

/-! # Orthogonality of non-associate relative wave packets on `[G]`: the transfer from `G(F) \ G(𝔸)`

`RelativeWavePacketOrthogonalityStatement` (Lapid 2011, Proposition 2 with `Ω(P, P') = ∅`, on
`[G] = A_G G(F) \ G(𝔸)` with parameters in `i(𝔞_M^G)^*`) follows from the same orthogonality on
`G(F) \ G(𝔸)` with parameters in `i𝔞_P^*` (`NonAssociateWavePacketOrthogonalityStatement`):
multiply both relative packets by the ambient profile of one nonzero smooth compactly supported
coefficient, so that they become wave packets of the same parabolics over all of `i𝔞_P^*`, and
compare the two pairings through the product decomposition of `G(F) \ G(𝔸)` over `A_G`.

* `ambientProfileQuotientLift_eq_of_descent`: on a packet recovered from representatives of
  `[G]`, the quotient lift by the profile is the pointwise product with the profile;
* `relativeWavePacketOrthogonality_of_inputs`: the target from the full-quotient orthogonality,
  the parabolic ambient lift, descent and the product pairing;
* `RelativeWavePacketOrthogonalityTransferStatement` and its proof
  `relativeWavePacketOrthogonalityTransfer`: the target from the full-quotient orthogonality,
  the nonemptiness of regular-parameter regions, the product formula for discrete left
  quotients and descent;
* `relativeWavePacketOrthogonality_of_innerProduct`: the same with Lapid's Proposition 2
  (`WavePacketInnerProductStatement`) in place of the full-quotient orthogonality. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- **The transfer of non-associate orthogonality to `[G]`.** The orthogonality of wave packets
of non-associate presented parabolics on `G(F) \ G(𝔸)` over all of `i𝔞_P^*`
(`NonAssociateWavePacketOrthogonalityStatement`), the nonemptiness of every regular-parameter
region (`EisensteinRegularParameterStatement`), the count-normalized product formula for
discrete left quotients (`LeftCosetSpace.ProductQuotientMeasureStatement`) and the descent of
relative wave packets to `[G]` (`RelativeWavePacketDescentStatement`) imply the orthogonality
on `[G]` of the relative wave packets of non-associate presented standard parabolics
(`RelativeWavePacketOrthogonalityStatement`). -/
def RelativeWavePacketOrthogonalityTransferStatement : Prop :=
  NonAssociateWavePacketOrthogonalityStatement → EisensteinRegularParameterStatement.{0} →
    LeftCosetSpace.ProductQuotientMeasureStatement.{0, 0, 0} →
    RelativeWavePacketDescentStatement → RelativeWavePacketOrthogonalityStatement

/-- The quotient lift of `y ↦ Θ(y.out)` by the profile is `q ↦ profile(q.out) · Θ(q.out)`,
when `Θ` is recovered from the representatives of `[G]`. -/
theorem ambientProfileQuotientLift_eq_of_descent {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {m : ℕ}
    (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
    (hrep : ∀ (f : RestrictionSplitCentre.CanonicalQuotient F G → ℂ) (g : AdelicGroupPoints F G),
      ambientProfileQuotientLift hG eG b f (LeftCosetSpace.mk (rationalSubgroup F G) g) =
        ambientWavePacketProfile eG b g *
          f (LeftCosetSpace.mk (RestrictionSplitCentre.canonicalRationalSubgroup F G) g))
    (Θ : AdelicGroupPoints F G → ℂ)
    (hΘ : ∀ g, Θ (LeftCosetSpace.mk (RestrictionSplitCentre.canonicalRationalSubgroup F G) g).out =
      Θ g) :
    ambientProfileQuotientLift hG eG b (fun y => Θ y.out) =
      fun q : RationalQuotient F G => ambientWavePacketProfile eG b q.out * Θ q.out := by
  funext q
  have hq : LeftCosetSpace.mk (rationalSubgroup F G) q.out = q := Quotient.out_eq q
  conv_lhs => rw [← hq]
  rw [hrep, hΘ]

/-- **Orthogonality on `[G]` from four inputs.** Take the ambient chart `ambientParameterChart hG`
and the nonzero coefficient `b = spectralBump _`. The products of `Θ` and `Θ'` with the profile
of `b` are wave packets of `P` and `P'` over `i𝔞_P^*` and `i𝔞_{P'}^*`, so their pairing on
`G(F) \ G(𝔸)` vanishes. By descent these products are the quotient lifts of `y ↦ Θ(y.out)` and
`y ↦ Θ'(y.out)`, whose pairing is a positive multiple of the pairing on `[G]`. -/
theorem relativeWavePacketOrthogonality_of_inputs
    (hNA : NonAssociateWavePacketOrthogonalityStatement)
    (hLift : WavePacketParabolicAmbientLiftStatement)
    (hDesc : RelativeWavePacketDescentStatement)
    (hPair : WavePacketProductPairingStatement) :
    RelativeWavePacketOrthogonalityStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ _ hP₀ hK₀ P M U A _ _ _ _ p
    _ iU l a r _ _ _ hA hT h₀ hU hK P' M' U' A' _ _ _ _ p' _ iU' l' a' r' _ _ _ hA' hT' h₀' hU'
    hK' hn Θ Θ' hΘ hΘ' hL hL'
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  -- one ambient chart and one nonzero ambient coefficient for both parabolics
  let eG := ambientParameterChart (F := F) (G := G) hG
  obtain ⟨b, hbs, hbc, hb0⟩ := spectralBump (Module.finrank ℝ (RealCharacterParameter F G))
  have hbne : b ≠ 0 := fun h => by simp [h] at hb0
  -- the lifts are wave packets of `P` and `P'`, orthogonal on `G(F) \ G(𝔸)`
  have hΦ := hLift F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc eG b hbs hbc Θ hΘ
  have hΦ' := hLift F G P' M' U' A' p' iU' l' a' r' hA' hT' hG hU' K hK' rho hsmooth hcalc eG b
    hbs hbc Θ' hΘ'
  obtain ⟨-, -, h0⟩ := hNA F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' hG hU
    hU' K hK hK' rho hsmooth hcalc hKmax hrho hn _ _ hΦ hΦ'
  -- the product pairing and descent
  obtain ⟨hc, hrep, -, hpair⟩ := hPair F G hG eG b hbs hbc hbne
  have hd := (hDesc F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc Θ hΘ).2
  have hd' := (hDesc F G P' M' U' A' p' iU' l' a' r' hA' hT' hG hU' K hK' rho hsmooth hcalc Θ'
    hΘ').2
  have hp := hpair (fun y => Θ y.out) (fun y => Θ' y.out) hL hL'
  rw [ambientProfileQuotientLift_eq_of_descent hG eG b hrep Θ hd,
    ambientProfileQuotientLift_eq_of_descent hG eG b hrep Θ' hd'] at hp
  have hz := hp.symm.trans h0
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hc.ne')

/-- **The transfer.** The parabolic ambient lift comes from the nonemptiness of the
regular-parameter regions (`wavePacketParabolicAmbientLift_of_regularParameter`), the product
pairing from the product formula for discrete left quotients
(`principalQuotientProductMeasure_of_productQuotientMeasure`,
`wavePacketProductPairing_of_productMeasure`). -/
theorem relativeWavePacketOrthogonalityTransfer :
    RelativeWavePacketOrthogonalityTransferStatement := fun hNA hR hPQ hDesc =>
  relativeWavePacketOrthogonality_of_inputs hNA
    (wavePacketParabolicAmbientLift_of_regularParameter hR) hDesc
    (wavePacketProductPairing_of_productMeasure
      (RestrictionSplitCentre.principalQuotientProductMeasure_of_productQuotientMeasure hPQ))

/-- Lapid's Proposition 2 (`WavePacketInnerProductStatement`), the nonemptiness of the
regular-parameter regions, the product formula for discrete left quotients and descent imply
`RelativeWavePacketOrthogonalityStatement`. -/
theorem relativeWavePacketOrthogonality_of_innerProduct
    (hWP : WavePacketInnerProductStatement) (hR : EisensteinRegularParameterStatement.{0})
    (hPQ : LeftCosetSpace.ProductQuotientMeasureStatement.{0, 0, 0})
    (hDesc : RelativeWavePacketDescentStatement) :
    RelativeWavePacketOrthogonalityStatement :=
  relativeWavePacketOrthogonalityTransfer (nonAssociateWavePacketOrthogonality_of_innerProduct hWP)
    hR hPQ hDesc

end Langlands.Global
