import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionAlgebraProof

/-! # Bilinearity, Dirac laws and mixed associativity -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uY uG

section Pairing

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]

theorem compactPartial_add (S R : compactlySupported (X := Y))
    (h : LocallyConstant (X × Y) ℂ) :
    compactPartial (S + R) h = compactPartial S h + compactPartial R h := by
  ext x
  exact compactSupportPairing_add_left S R _

theorem compactPartial_smul (c : ℂ) (S : compactlySupported (X := Y))
    (h : LocallyConstant (X × Y) ℂ) :
    compactPartial (c • S) h = c • compactPartial S h := by
  ext x
  exact compactSupportPairing_smul_left c S _

theorem compactSupportPairing_dirac (y : Y) (h : LocallyConstant Y ℂ) :
    compactSupportPairing (compactDirac y) h = h y := by
  obtain ⟨f, hf⟩ := exists_testFunction_agrees_on_compact (isCompact_singleton (x := y)) h
  have hs : support (dirac y) ⊆ {y} :=
    support_subset_of_mem_supportedOn isClosed_singleton (by
      intro g hg
      exact hg y (Set.mem_singleton y))
  rw [compactSupportPairing_eq_of_agrees (compactDirac y) h f
    (fun z hz => hf z (hs hz))]
  exact hf y (Set.mem_singleton y)

end Pairing

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem convolution_add_left (T S R : compactlySupported (X := G)) :
    convolution (T + S) R = convolution T R + convolution S R := by
  apply Subtype.ext
  ext f
  simp only [convolution_eq_pairing, compactSupportPairing_add_left]
  rfl

theorem convolution_add_right (T S R : compactlySupported (X := G)) :
    convolution T (S + R) = convolution T S + convolution T R := by
  apply Subtype.ext
  ext f
  simp only [convolution_eq_pairing, compactPartial_add, compactSupportPairing_add_right]
  rfl

theorem convolution_smul_left (c : ℂ) (T S : compactlySupported (X := G)) :
    convolution (c • T) S = c • convolution T S := by
  apply Subtype.ext
  ext f
  simp only [convolution_eq_pairing, compactSupportPairing_smul_left]
  rfl

theorem convolution_smul_right (c : ℂ) (T S : compactlySupported (X := G)) :
    convolution T (c • S) = c • convolution T S := by
  apply Subtype.ext
  ext f
  simp only [convolution_eq_pairing, compactPartial_smul, compactSupportPairing_smul_right]
  rfl

theorem convolution_dirac_left (g : G) (T : compactlySupported (X := G)) :
    (convolution (compactDirac g) T : Distribution G) =
      GroupAction.leftDistributions g (T : Distribution G) := by
  ext f
  rw [convolution_eq_pairing, compactSupportPairing_dirac]
  change compactSupportPairing T _ = (T : Distribution G) _
  apply compactSupportPairing_eq_of_agrees
  intro x _
  simp [mulFunction]

theorem convolution_dirac_right (g : G) (T : compactlySupported (X := G)) :
    (convolution T (compactDirac g) : Distribution G) =
      GroupAction.rightDistributions g⁻¹ (T : Distribution G) := by
  ext f
  rw [convolution_eq_pairing]
  have he : compactPartial (compactDirac g) (mulFunction ⟨(f : G → ℂ), f.locallyConstant⟩) =
      ⟨fun x => f (x * g), f.locallyConstant.comp_continuous
        (continuous_id.mul continuous_const)⟩ := by
    ext x
    exact compactSupportPairing_dirac g _
  rw [he]
  apply compactSupportPairing_eq_of_agrees
  intro x _
  change (GroupAction.rightTests (g⁻¹)⁻¹ f) x = f (x * g)
  simp only [inv_inv, GroupAction.rightTests_apply]

theorem convolution_dirac_dirac (g h : G) :
    convolution (compactDirac g) (compactDirac h) = compactDirac (g * h) := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing, compactSupportPairing_dirac]
  exact compactSupportPairing_dirac h _

theorem convolution_dirac_one_left (T : compactlySupported (X := G)) :
    convolution (compactDirac 1) T = T := by
  apply Subtype.ext
  rw [convolution_dirac_left]
  exact LinearMap.congr_fun (map_one GroupAction.leftDistributions) (T : Distribution G)

theorem convolution_dirac_one_right (T : compactlySupported (X := G)) :
    convolution T (compactDirac 1) = T := by
  apply Subtype.ext
  rw [convolution_dirac_right, inv_one]
  exact LinearMap.congr_fun (map_one GroupAction.rightDistributions) (T : Distribution G)

/-- Bundle the actual smooth left convolution kernel. -/
def leftSmoothFunction (T : compactlySupported (X := G)) (f : LocallyConstant G ℂ) :
    LocallyConstant G ℂ :=
  ⟨leftConvolveSmooth T f, leftConvolveSmooth_locallyConstant T f⟩

/-- Bundle the actual smooth right convolution kernel. -/
def rightSmoothFunction (f : LocallyConstant G ℂ) (T : compactlySupported (X := G)) :
    LocallyConstant G ℂ :=
  ⟨rightConvolveSmooth f T, rightConvolveSmooth_locallyConstant T f⟩

theorem leftConvolveSmooth_associative (T S : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) :
    leftConvolveSmooth (convolution T S) f =
      leftConvolveSmooth T (leftSmoothFunction S f) := by
  funext x
  unfold leftConvolveSmooth
  rw [compactSupportPairing_convolution]
  apply compactSupportPairing_congr
  intro y _
  change compactSupportPairing S _ = compactSupportPairing S _
  apply compactSupportPairing_congr
  intro z _
  simp [mulFunction, mul_inv_rev, mul_assoc]

theorem leftConvolveSmooth_right (T S : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) :
    leftConvolveSmooth T (rightSmoothFunction f S) =
      rightConvolveSmooth (leftSmoothFunction T f) S := by
  funext x
  let h : LocallyConstant (G × G) ℂ :=
    ⟨fun p => f (p.1⁻¹ * x * p.2⁻¹), f.isLocallyConstant.comp_continuous
      ((continuous_fst.inv.mul continuous_const).mul continuous_snd.inv)⟩
  change compactSupportPairing T (compactPartial S h) = _
  rw [compactPairing_swap]
  apply compactSupportPairing_congr
  intro z _
  apply compactSupportPairing_congr
  intro y _
  exact congrArg f (mul_assoc y⁻¹ x z⁻¹)

theorem rightConvolveSmooth_associative (T S : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) :
    rightConvolveSmooth (rightSmoothFunction f T) S =
      rightConvolveSmooth f (convolution T S) := by
  funext x
  let h : LocallyConstant (G × G) ℂ :=
    ⟨fun p => f (x * p.1⁻¹ * p.2⁻¹), f.isLocallyConstant.comp_continuous
      ((continuous_const.mul continuous_fst.inv).mul continuous_snd.inv)⟩
  change compactSupportPairing S (compactPartial T h) = compactSupportPairing (convolution T S) _
  rw [compactPairing_swap, compactSupportPairing_convolution]
  apply compactSupportPairing_congr
  intro y _
  apply compactSupportPairing_congr
  intro z _
  simp [h, mulFunction, mul_inv_rev, mul_assoc]

end Group

namespace RenardConvolution

theorem bilinearUnit : BilinearUnitStatement.{uG} := by
  intro G _ _ _ _ _ _
  exact ⟨convolution_add_left, convolution_add_right, convolution_smul_left,
    convolution_smul_right, fun T => ⟨convolution_dirac_one_left T,
      convolution_dirac_one_right T⟩⟩

theorem diracLaws : DiracStatement.{uG} := by
  intro G _ _ _ _ _ _ T g g'
  exact ⟨convolution_dirac_left g T, convolution_dirac_right g T,
    convolution_dirac_dirac g g'⟩

theorem mixedAssociativity : MixedAssociativityStatement.{uG} := by
  intro G _ _ _ _ _ _ T S f
  let F : LocallyConstant G ℂ := ⟨(f : G → ℂ), f.locallyConstant⟩
  refine ⟨leftSmoothFunction T F, rightSmoothFunction F T,
    leftSmoothFunction S F, rightSmoothFunction F S,
    leftConvolveSmooth_eq_test T f, rightConvolveSmooth_eq_test T f,
    leftConvolveSmooth_eq_test S f, rightConvolveSmooth_eq_test S f, ?_,
    leftConvolveSmooth_right T S F, ?_⟩
  · rw [← leftConvolveSmooth_eq_test]
    exact leftConvolveSmooth_associative T S F
  · rw [← rightConvolveSmooth_eq_test]
    exact rightConvolveSmooth_associative T S F

end RenardConvolution
end Langlands.HarmonicAnalysis.Distribution
