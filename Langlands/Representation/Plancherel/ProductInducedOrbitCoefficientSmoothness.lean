import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficients

/-! # Parameter smoothness of the actual orbit coefficient -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal TensorProduct ContDiff

namespace Langlands.Plancherel

open Aubert.General Induction CompactInduction

universe uG uI uV uJ

private theorem scalarSmooth_of_mem_finiteSmoothFamilies
    {J : Type uJ} [Fintype J] {F : (J → Circle) → ℂ}
    (hF : F ∈ finiteSmoothFamilies J ℂ) : IsSmoothFiniteTorusFunction F := by
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J ℂ F).mp hF
  change ContDiff ℝ ∞ (fun θ => F (finiteTorusExp θ))
  have heq : (fun θ => F (finiteTorusExp θ)) =
      (fun θ => ∑ i, (f i).val (finiteTorusExp θ) * v i) := by
    funext θ
    simpa only [smul_eq_mul] using hF (finiteTorusExp θ)
  rw [heq]
  exact ContDiff.sum fun i _ =>
    (show ContDiff ℝ ∞ (fun θ => (f i).val (finiteTorusExp θ)) from (f i).property).mul contDiff_const

variable {G : Type uG} [Group G] [TopologicalSpace G] {P M U : Subgroup G}

private theorem coefficientSmoothFactorization (K : OpenSubgroup G)
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) (g : G) :
    ∃ p ∈ P, ∃ k ∈ K, g = p * k := by
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.property, k, k.property, hg⟩

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

private def compactUntwistedCoefficientEquiv :
    Representation.Equiv
      ((productInducedCoefficientObject h hU π.obj).representation.comp
        (K.prod K).toSubgroup.subtype)
      (productInducedCompactRepresentation h K π.obj) :=
  normalizedInductionCompactEquiv (h.prod h) (K.prod K) (hU.prod hU)
    (hP.prod hP) (hK.prod hK) (product_compact_factorization K hPK)
    (productLeviObject π.obj π.obj.contragredient)

/-- One fixed linear functional on the actual compact picture, obtained by
untwisted extension and evaluation of its genuine coefficient at the identity. -/
def productInducedCompactCoefficientAtOne :
    ProductInducedCompactPicture h K π.obj →ₗ[ℂ] ℂ :=
  (LocallyConstant.evalₗ ℂ (1 : G)).comp
    ((CompactInduction.coefficientMap h hU π.obj K hK hP hr
      (coefficientSmoothFactorization K hPK) hG hδ π.property.2).comp
      (compactUntwistedCoefficientEquiv h hU hP K hK hPK π).symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
omit [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
private theorem compactUntwistedCoefficientEquiv_symm_eval
    (F : ProductInducedCompactPicture h K π.obj) (k : K.prod K) :
    Induction.eval _ _ ((compactUntwistedCoefficientEquiv h hU hP K hK hPK π).symm F) k =
      Induction.eval _ _ F k := by
  have ht := normalizedInductionCompactEquiv_eval (h.prod h) (K.prod K)
    (hU.prod hU) (hP.prod hP) (hK.prod hK) (product_compact_factorization K hPK)
    (productLeviObject π.obj π.obj.contragredient)
    ((compactUntwistedCoefficientEquiv h hU hP K hK hPK π).symm F) k
  exact ht.symm.trans (congrArg
    (fun v : ProductInducedCompactPicture h K π.obj => Induction.eval _ _ v k)
    ((compactUntwistedCoefficientEquiv h hU hP K hK hPK π).apply_symm_apply F))

set_option backward.isDefEq.respectTransparency false in
/-- Removing an actual twist preserves coefficient evaluation at the identity
through one fixed functional on the untwisted compact picture. -/
theorem productInducedCompactCoefficientAtOne_twist
    (χ : unramifiedCharacters ν)
    (hχa : (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).IsAdmissible)
    (F : productInducedCoefficientObject h hU
      (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    CompactInduction.coefficientMap h hU
        (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hr
        (coefficientSmoothFactorization K hPK) hG hδ hχa F 1 =
      productInducedCompactCoefficientAtOne h hU hP K hK hPK hG hδ π hr
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ π.obj F) := by
  change CompactInduction.coefficientMap h hU
      (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hr
      (coefficientSmoothFactorization K hPK) hG hδ hχa F 1 =
    CompactInduction.coefficientMap h hU π.obj K hK hP hr
      (coefficientSmoothFactorization K hPK) hG hδ π.property.2
      ((compactUntwistedCoefficientEquiv h hU hP K hK hPK π).symm
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ π.obj F)) 1
  rw [CompactInduction.coefficientMap_integral, CompactInduction.coefficientMap_integral]
  apply integral_congr_ae
  filter_upwards [] with k
  let kk : K.prod K := ⟨((k : G), (k : G)), k.property, k.property⟩
  have ht := compactUntwistedCoefficientEquiv_symm_eval h hU hP K hK hPK π
    (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ π.obj F) kk
  have hp := productCompactTwistTensorEquiv_pairing ν χ π.obj
    (F.val.val (kk : G × G))
  change (TensorProduct.lift (smoothDualPairing
      (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation).flip)
      (F.val.val ((k : G) * 1, (k : G))) =
    (TensorProduct.lift (smoothDualPairing π.obj.representation).flip)
      (((compactUntwistedCoefficientEquiv h hU hP K hK hPK π).symm
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ π.obj F)).val.val
          ((k : G) * 1, (k : G)))
  simp only [mul_one]
  exact hp.symm.trans
    (congrArg (TensorProduct.lift (smoothDualPairing π.obj.representation).flip) ht.symm)

variable {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

omit [Fintype J] in
/-- At the identity, every actual parameter-fiber coefficient uses the same
fixed compact functional. -/
theorem unitaryOrbitRepresentativeCoefficientMap_at_one
    (q : ProductInducedOrbitSections ν π h hU) (z : J → Circle) :
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr
        (unitaryOrbitParameterRepresentative ν π e z)
        (q (unitaryOrbitParameterRepresentative ν π e z)) 1 =
      productInducedCompactCoefficientAtOne h hU hP K hK hPK hG hδ π hr
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU q) z) :=
  productInducedCompactCoefficientAtOne_twist h hU hP K hK hPK hG hδ ν π hν hr
    (unitaryTorusParameter ν e z) (unitaryOrbitParameterRepresentative ν π e z).val.property.2
    (q (unitaryOrbitParameterRepresentative ν π e z))

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- Fixed-group-point evaluation of the actual orbit coefficient is smooth in
the original finite-torus parameters. -/
theorem isSmoothFiniteTorusFunction_unitaryOrbitCoefficient
    (hLaurent : HasLaurentUnitaryCoordinates ν e)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    IsSmoothFiniteTorusFunction (fun z =>
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) g) := by
  let qg := productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent (g, 1) q
  have hfinite := mem_finiteSmoothFamilies_linearMap qg.property.2
    (productInducedCompactCoefficientAtOne h hU hP K hK hPK hG hδ π hr)
  have heq : (fun z => unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) g) =
      (fun z => productInducedCompactCoefficientAtOne h hU hP K hK hPK hG hδ π hr
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU qg.val) z)) := by
    funext z
    have ha := unitaryOrbitCoefficientMap_action h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e
      hLaurent (g, 1) q
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) 1
    have hh : unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) g =
        unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e qg
          (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) 1 := by
      simpa only [qg, Prod.fst, Prod.snd, inv_one, one_mul] using ha.symm
    have hp := congrArg (fun F : LocallyConstant G ℂ => F 1)
      (unitaryOrbitCoefficientMap_parameter h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e qg z)
    have ho := unitaryOrbitRepresentativeCoefficientMap_at_one
      h hU hP K hK hPK hG hδ ν π hν hr e qg.val z
    exact hh.trans (hp.trans ho)
  rw [heq]
  exact scalarSmooth_of_mem_finiteSmoothFamilies hfinite

/-- The actual pulled-back coefficient as an element of the existing smooth scalar algebra. -/
def unitaryOrbitCoefficientTorusSmoothFunction
    (hLaurent : HasLaurentUnitaryCoordinates ν e)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    smoothFiniteTorusFunctions J :=
  ⟨fun z => unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) g,
    isSmoothFiniteTorusFunction_unitaryOrbitCoefficient
      h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq hLaurent q g⟩

/-- Continuity descends to the actual orbit quotient, using only continuity of
the forward coordinates and the derived parameter smoothness. -/
theorem continuous_unitaryOrbitCoefficient
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    Continuous (fun w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) =>
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q w g) := by
  apply (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν
    (discreteSeriesClass C hC μ π hsq)).isQuotientMap.continuous_iff.mpr
  have ht := (isSmoothFiniteTorusFunction_unitaryOrbitCoefficient
    h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq hLaurent q g).continuous.comp he
  simpa only [Function.comp_def, e.symm_apply_apply] using ht

end Langlands.Plancherel
