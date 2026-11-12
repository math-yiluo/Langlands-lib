import Langlands.Representation.Aubert.ZelevinskyComparison

/-!
# Involutivity of the actual support-adjusted graded Aubert operator

The unique effective sign agrees on the two irreducible classes exchanged by
unadjusted Aubert duality. Jordan–Hölder realization and the direct-sum universal
property extend this identity to every actual graded exact class.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear SmoothRep VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem effective_generator {ι : Type*} (c : ι) :
    generator c ∈ effective := by
  classical
  intro d
  simp only [generator, Finsupp.single_apply]
  split_ifs <;> omega

/-- The support-adjusted operator squares to the identity on every actual
irreducible class, including rank zero. -/
private theorem adjustedOperator_twice_irreducible (n : ℕ) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.IsIrreducible),
      let x := GeneralLinear.finiteLengthClass n F.Carrier π
        (hasFiniteLength_of_isIrreducible hπ)
      adjustedOperator.{uF, uV} F T n (adjustedOperator F T n x) = x := by
  let := T.topology
  intro π hπ
  obtain ⟨πD, hπD, hD⟩ := irreducibleImage.{uF, uV} F T n π hπ
  let x := GeneralLinear.finiteLengthClass n F.Carrier π
    (hasFiniteLength_of_isIrreducible hπ)
  let y := GeneralLinear.finiteLengthClass n F.Carrier πD
    (hasFiniteLength_of_isIrreducible hπD)
  let c := SmoothRep.irreducibleIsoClass π hπ
  let d := SmoothRep.irreducibleIsoClass πD hπD
  obtain ⟨s, hs, hxy⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      alternatingOperator.{uF, uV} F T n x = s • y := by
    rcases hD with hD | hD
    · exact ⟨1, Or.inl rfl, by simpa only [one_smul] using hD⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_smul] using hD⟩
  have hss : s * s = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hyx : alternatingOperator.{uF, uV} F T n y = s • x := by
    calc
      alternatingOperator F T n y =
          s • (s • alternatingOperator F T n y) := by
        rw [smul_smul, hss, one_smul]
      _ = s • alternatingOperator F T n (s • y) := by rw [map_smul]
      _ = s • x := by
        rw [← hxy]
        exact congrArg (s • ·) (LinearMap.congr_fun (involutivity.{uF, uV} F T n) x)
  have hxFactors : factorMap x = generator c := by
    exact (factorMap_ofRepresentation _ _).trans (compositionFactors_irreducible π hπ (hasFiniteLength_of_isIrreducible hπ))
  have hyFactors : factorMap y = generator d := by
    exact (factorMap_ofRepresentation _ _).trans (compositionFactors_irreducible πD hπD (hasFiniteLength_of_isIrreducible hπD))
  have hc : supportSign.{uF, uV} F T n c = s := by
    apply supportSign_eq_of_effective F T n c s hs
    change s • factorMap (alternatingOperator F T n
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (generator c))) ∈ effective
    rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
      (hasFiniteLength_of_isIrreducible hπ)]
    change s • factorMap (alternatingOperator F T n x) ∈ effective
    rw [hxy, map_smul, smul_smul, hss, one_smul, hyFactors]
    exact effective_generator d
  have hd : supportSign.{uF, uV} F T n d = s := by
    apply supportSign_eq_of_effective F T n d s hs
    change s • factorMap (alternatingOperator F T n
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (generator d))) ∈ effective
    rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass πD hπD
      (hasFiniteLength_of_isIrreducible hπD)]
    change s • factorMap (alternatingOperator F T n y) ∈ effective
    rw [hyx, map_smul, smul_smul, hss, one_smul, hxFactors]
    exact effective_generator c
  have hAx : adjustedOperator.{uF, uV} F T n x = y := by
    rw [adjustedOperator_irreducible F T n π hπ, hc, hxy,
      smul_smul, hss, one_smul]
  change adjustedOperator F T n (adjustedOperator F T n x) = x
  rw [hAx, adjustedOperator_irreducible F T n πD hπD, hd, hyx,
    smul_smul, hss, one_smul]

/-- Involutivity on the whole actual exact finite-length K0 in every rank. -/
theorem adjustedOperator_involutive (n : ℕ) :
    letI := T.topology
    Function.Involutive (adjustedOperator.{uF, uV} F T n) := by
  let := T.topology
  let A := adjustedOperator.{uF, uV} F T n
  have he : (A.comp A).comp
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)) =
      SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) := by
    apply SmoothRep.eq_realizeIrreducibles_of_irreducible
    intro π hπ
    simp only [LinearMap.comp_apply,
      SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
        (hasFiniteLength_of_isIrreducible hπ)]
    exact adjustedOperator_twice_irreducible.{uF, uV} F T n π hπ
  have hA : A.comp A = LinearMap.id := by
    have h := congrArg (fun f => f.comp factorMap) he
    simpa only [LinearMap.comp_assoc, realize_comp_factorMap, LinearMap.comp_id] using h
  intro x
  exact LinearMap.congr_fun hA x

/-- The actual support-adjusted graded additive Aubert operator is an involution,
with no exactness, ring-law or polynomial-comparison hypotheses. -/
theorem adjustedInvolutivity : AdjustedInvolutivityStatement.{uF, uV} F T := by
  let := T.topology
  have he : (gradedAdjustedOperator.{uF, uV} F T).comp
      (gradedAdjustedOperator F T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change gradedAdjustedOperator F T
        (gradedAdjustedOperator F T (gradedInclusion F T n x)) = gradedInclusion F T n x
    rw [gradedAdjustedOperator_homogeneous, gradedAdjustedOperator_homogeneous,
      adjustedOperator_involutive F T n x]
  intro x
  exact LinearMap.congr_fun he x

end Langlands.Aubert
