import Langlands.Representation.Aubert.CorrectedOrbitCoefficientCutComparison
import Langlands.Representation.Aubert.CorrectedGradedCutComparison
import Langlands.Representation.Induction.SingleBlock

/-! Evaluation at the identity for the actual whole-target orbit pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open CategoryTheory

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Evaluation at one is a linear equivalence for compact induction from the
whole group, with its actual smooth inducing coefficient. -/
def compactInducedTopLinearEquiv (H : Subgroup G) (hH : H = ⊤)
    (σ : Representation R H V) (hσ : IsSmooth σ) :
    CompactFunctions H σ ≃ₗ[R] V := by
  subst H
  letI : Subsingleton (LeftQuotient (⊤ : Subgroup G)) := ⟨by
    intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        exact Quotient.sound ((QuotientGroup.rightRel_apply).mpr
          (show x * y⁻¹ ∈ (⊤ : Subgroup G) from trivial))⟩
  let ρ := σ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom
  have hρ : IsSmooth ρ := isSmooth_comp _ (continuous_id.subtype_mk _) hσ
  exact ((compactInclusion (⊤ : Subgroup G) σ).ofBijective
    (compactInclusion_bijective_of_compactSpace (⊤ : Subgroup G) σ)).toLinearEquiv.trans
    (smoothInducedTopEquiv (⊤ : Subgroup G) rfl σ ρ (fun _ => rfl) hρ).toLinearEquiv

@[simp]
theorem compactInducedTopLinearEquiv_apply (H : Subgroup G) (hH : H = ⊤)
    (σ : Representation R H V) (hσ : IsSmooth σ) (f : CompactFunctions H σ) :
    compactInducedTopLinearEquiv H hH σ hσ f = eval H σ f.val 1 := by
  subst H
  rfl

end Langlands.Induction

namespace Langlands.Geometric

open GeneralLinear

universe uF

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (hW : blockWeyl C ⊓ (blockWeyl B).comap
    (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C)

include hW in
/-- A whole-target Weyl intersection makes the actual target parabolic
intersection the whole product Levi. -/
theorem sourceParabolic_eq_top_of_wholeTarget :
    sourceParabolic F C B w⁻¹ = ⊤ := by
  apply top_unique
  intro m _
  rw [mem_sourceParabolic_iff]
  intro i a b hab
  have he := ((TypeASolomon.intersection_eq_iff C B C w⁻¹).mp hW
    (C.index i a) (C.index i b)).mp (by simp only [blockIndex_index])
  exact False.elim ((ne_of_lt hab) he.2.symm)

include hW in
/-- At a whole target, the actual stages quotient is the full target Levi. -/
theorem parabolicOrbitStagesQuotient_eq_top_of_wholeTarget :
    parabolicOrbitStagesQuotient F B C w = ⊤ := by
  exact (parabolicOrbitStages_comap_section F B C w).trans
    (sourceParabolic_eq_top_of_wholeTarget F B C w hW)

end Langlands.Geometric

namespace Langlands.Aubert.Support

open GeneralLinear Geometric Induction

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The actual nested quotient action is smooth, by the original smooth
coefficient, its continuous section and the surjective quotient map. -/
theorem cutOrbitNestedCoefficientAction_smooth :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsSmooth (parabolicOrbitNestedCoefficientAction F.Carrier B C w
      (T.leviHalfModulus B) (T.normalizedJacquet B A.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let σ := cutOrbitCoefficient T A B C w
  let s := parabolicOrbitStagesSection F.Carrier B C w
  have hs : Continuous s :=
    ((C.leviInParabolicContinuous F.Carrier).continuous.comp
      continuous_subtype_val).subtype_mk _
  have hσ : IsSmooth σ :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) _
        (T.isOpen_ker_leviHalfModulus B)).mpr
          ((T.normalizedJacquetFunctor B).obj A).isSmooth)
  let q : Representation.IntertwiningMap (σ.comp s)
      (parabolicOrbitNestedCoefficientAction F.Carrier B C w
        (T.leviHalfModulus B) (T.normalizedJacquet B A.representation)) :=
    { toLinearMap := Representation.Coinvariants.mk
        (cutOrbitNestedCoefficient T A.representation C w B)
      isIntertwining' l := LinearMap.ext fun v => rfl }
  exact isSmooth_of_surjective q
    (Representation.Coinvariants.mk_surjective
      (cutOrbitNestedCoefficient T A.representation C w B))
    (isSmooth_comp s hs hσ)

/-- The actual Haar ratio has open kernel, by the two actual ambient
normalizer Haar characters and their continuous section maps. -/
theorem cutOrbitHaarRatio_openKernel :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    IsOpen ((Jacquet.complexCharacter
      (parabolicOrbitStagesHaarRatio F.Carrier B C w)).ker :
        Set (parabolicOrbitStagesQuotient F.Carrier B C w)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let U := C.unipotentSubgroup F.Carrier
  let I := intersectionSource U (B.parabolic F.Carrier) (permutation n F.Carrier w)⁻¹
  let : LocallyCompactSpace U := (C.isClosed_unipotentSubgroup F.Carrier).locallyCompactSpace
  let : LocallyCompactSpace I :=
    (General.isClosed_correctionSubgroup _ _ _
      (C.isClosed_unipotentSubgroup F.Carrier) (B.isClosed_parabolic F.Carrier)).locallyCompactSpace
  let χ₁ := (HaarModulus.normalizerCharacter U).comp
    (parabolicOrbitStagesRadicalNormalizer F.Carrier B C w)
  let χ₂ := (HaarModulus.normalizerCharacter I).comp
    (parabolicOrbitStagesCorrectionNormalizer F.Carrier B C w)
  have h₁ : IsOpen (χ₁.ker : Set (parabolicOrbitStagesQuotient F.Carrier B C w)) :=
    (HaarModulus.isOpen_ker_normalizerCharacter U).preimage
      (continuous_parabolicOrbitStagesRadicalNormalizer F.Carrier B C w)
  have h₂ : IsOpen (χ₂.ker : Set (parabolicOrbitStagesQuotient F.Carrier B C w)) :=
    (HaarModulus.isOpen_ker_normalizerCharacter I).preimage
      (continuous_parabolicOrbitStagesCorrectionNormalizer F.Carrier B C w)
  apply Subgroup.isOpen_mono (H₁ := χ₁.ker ⊓ χ₂.ker) ?_ (h₁.inter h₂)
  intro l hl
  have hχ : parabolicOrbitStagesHaarRatio F.Carrier B C w l = 1 := by
    change χ₁ l / χ₂ l = 1
    rw [show χ₁ l = 1 from hl.1, show χ₂ l = 1 from hl.2]
    simp
  change Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F.Carrier B C w) l = 1
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    (parabolicOrbitStagesHaarRatio F.Carrier B C w l) = 1
  rw [hχ, map_one]

/-- The normalized integral's actual inducing coefficient is smooth. -/
theorem cutOrbitIntegratedCoefficient_smooth :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    IsSmooth (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
      (T.normalizedJacquet B A.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact (isSmooth_twist_iff _ _ (cutOrbitHaarRatio_openKernel T B C w)).mpr
    (cutOrbitNestedCoefficientAction_smooth T A B C w)

/-- Evaluation at the identity identifies the actual whole-target compact
orbit piece with its genuine nested quotient coefficient. -/
def cutOrbitWholeTargetEvalEquiv
    (hW : blockWeyl C ⊓ (blockWeyl B).comap
      (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    CompactFunctions (parabolicOrbitStagesQuotient F.Carrier B C w)
      (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
        (T.normalizedJacquet B A.representation)) ≃ₗ[ℂ]
      Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact compactInducedTopLinearEquiv _
    (parabolicOrbitStagesQuotient_eq_top_of_wholeTarget F.Carrier B C w hW) _
    (cutOrbitIntegratedCoefficient_smooth T A B C w)

@[simp]
theorem cutOrbitWholeTargetEvalEquiv_apply
    (hW : blockWeyl C ⊓ (blockWeyl B).comap
      (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ f, cutOrbitWholeTargetEvalEquiv T A B C w hW f = eval _ _ f.val 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro f
  exact compactInducedTopLinearEquiv_apply _
    (parabolicOrbitStagesQuotient_eq_top_of_wholeTarget F.Carrier B C w hW) _
    (cutOrbitIntegratedCoefficient_smooth T A B C w) f

variable (θ : Set (Equiv.Perm (Fin n)))
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ) (hwInc : TypeASolomon.SourceIncreasing B w)
  (Q : BlockShape n) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  (hBQ : B.flatten S = Q)
  (hW : blockWeyl C ⊓ (blockWeyl B).comap
    (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C)

/-- The actual whole-target graded support quotient identifies with a common
actual flattened Jacquet coefficient through coherent orbit integration. -/
def correctedWholeTargetCommonEquiv :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    cutSupportQuotient T A C B (θ \ {w}) θ ≃ₗ[ℂ]
      Q.JacquetModule A.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact (Representation.equivOfIso
    (coherentGradedOrbitIntegralIso T A B C θ w hθ hLower hw hwInc)).toLinearEquiv.trans
    ((cutOrbitWholeTargetEvalEquiv T A B C w hW).trans
      (cutOrbitCoefficientCommonEquiv T A B C Q w S hS hBQ))

/-- This comparison is exactly the common-coefficient image of the coherent
actual graded integral evaluated at one. -/
theorem correctedWholeTargetCommonEquiv_apply :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z, correctedWholeTargetCommonEquiv T A B C w θ hθ hLower hw hwInc
        Q S hS hBQ hW z =
      cutOrbitCoefficientCommonEquiv T A B C Q w S hS hBQ
        (coherentGradedOrbitIntegralValue T A B C θ w hθ hLower hw hwInc z 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z
  exact congrArg (cutOrbitCoefficientCommonEquiv T A B C Q w S hS hBQ)
    (cutOrbitWholeTargetEvalEquiv_apply T A B C w hW
      (((coherentGradedOrbitIntegralIso T A B C θ w hθ hLower hw hwInc).hom).hom z))

/-- Every genuine whole-target graded cut map is the identity after these
identifications with the same actual flattened Jacquet coefficient. -/
theorem correctedWholeTargetCommonEquiv_cutMap
    (D : BlockShape n) (R : BlockRefinement D)
    (hR : IsIntersectionRefinement (F := F.Carrier) D C w R)
    (hDQ : D.flatten R = Q) (h : B.cuts ⊆ D.cuts)
    (hwD : TypeASolomon.SourceIncreasing D w)
    (hWD : blockWeyl C ⊓ (blockWeyl D).comap
      (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z : cutSupportQuotient T A C B (θ \ {w}) θ,
      correctedWholeTargetCommonEquiv T A D C w θ hθ hLower
          (weylSupport_mono_source_cuts C h θ hw) hwD Q R hR hDQ hWD
          ((cutSupportQuotientMap T A C h (θ \ {w}) θ).hom z) =
        correctedWholeTargetCommonEquiv T A B C w θ hθ hLower hw hwInc
          Q S hS hBQ hW z := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z
  have hD := correctedWholeTargetCommonEquiv_apply T A D C w θ hθ hLower
    (weylSupport_mono_source_cuts C h θ hw) hwD Q R hR hDQ hWD
    ((cutSupportQuotientMap T A C h (θ \ {w}) θ).hom z)
  have hB := correctedWholeTargetCommonEquiv_apply T A B C w θ hθ hLower
    hw hwInc Q S hS hBQ hW z
  have hI := coherentGradedOrbitIntegralValue_cutMap T A B C θ w hθ hLower hw
    D h hwInc hwD z 1
  have hQ := cutOrbitCoefficientCommonEquiv_cutMap T A B D C Q w S R hS hR
    h hwInc hBQ hDQ
    (coherentGradedOrbitIntegralValue T A B C θ w hθ hLower hw hwInc z 1)
  exact hD.trans ((congrArg
    (cutOrbitCoefficientCommonEquiv T A D C Q w R hR hDQ) hI).trans (hQ.trans hB.symm))

end Langlands.Aubert.Support
