import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerSplitCenter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelMonomialBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Completeness
import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketSchwartz
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicInducedOrbitWavePacket

/-! # Lower packets of the weak expansion as standard-Levi packets of a lower Levi -/

noncomputable section

universe u uV uG uI uI' uJ uJ'

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz.LowerPacket

/-- Each circle coordinate of the unitary character torus is evaluation at a group element. -/
def HasEvaluationUnitaryCoordinates {G : Type uG} [Group G] [TopologicalSpace G]
    {I : Type uI} (ν : I → (G →* ℝ≥0ˣ)) {J : Type uJ}
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) : Prop :=
  ∀ j, ∃ g : G, ∀ χ : unitaryUnramifiedCharacters ν,
    ((e χ j : Circle) : ℂ) = ((χ.val g : ℂˣ) : ℂ)

/-! ### Two norm families with the same norm-one subgroup -/

section SameLevi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hr : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {I' : Type uI'} (ν' : I' → (M →* ℝ≥0ˣ)) (hν' : ∀ i, Continuous (ν' i))
  {J' : Type uJ'} [Fintype J'] (e' : unitaryUnramifiedCharacters ν' ≃* (J' → Circle))
  (hker : commonNormKernel ν = commonNormKernel ν')

/-- The orbit representatives of `π` for two norm families with the same norm-one subgroup are
the same representations. -/
def representativeChange :
    UnitaryOrbitRepresentative ν π ≃ UnitaryOrbitRepresentative ν' π where
  toFun B := ⟨B.val, by
    obtain ⟨χ, hχ⟩ := B.property
    exact ⟨unitaryUnramifiedCharactersCongr hker χ, hχ⟩⟩
  invFun B := ⟨B.val, by
    obtain ⟨χ, hχ⟩ := B.property
    exact ⟨(unitaryUnramifiedCharactersCongr hker).symm χ, hχ⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

omit [LocallyCompactSpace G] in
@[simp] theorem representativeChange_val (B : UnitaryOrbitRepresentative ν π) :
    (representativeChange π ν ν' hker B).val = B.val := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [Fintype J] in
include hker in
/-- If the coordinates `e` are evaluations at points and the coordinates `e'` are Laurent, then
`e'` is obtained from `e` by an integer monomial change of the torus parameters. -/
theorem exists_monomial_of_eval
    (hcoord : HasEvaluationUnitaryCoordinates ν e)
    (he' : HasLaurentUnitaryCoordinates ν' e') :
    ∃ a : J → J' → ℤ,
      ∀ z : J' → Circle, (e'.symm z).val = (e.symm (finiteTorusMonomial a z)).val := by
  classical
  unfold HasEvaluationUnitaryCoordinates at hcoord
  choose g hg using hcoord
  choose n hn using fun j => he' (g j)
  refine ⟨n, fun z => ?_⟩
  have hχ : e (unitaryUnramifiedCharactersCongr hker.symm (e'.symm z)) =
      finiteTorusMonomial n z := by
    funext j
    apply Circle.ext
    rw [hg j]
    change (((e'.symm z).val (g j) : ℂˣ) : ℂ) = _
    rw [hn j z]
    change ∏ k, ((z k ^ n j k : Circle) : ℂ) = ((∏ k, z k ^ n j k : Circle) : ℂ)
    exact (map_prod Circle.coeHom (fun k => z k ^ n j k) Finset.univ).symm
  rw [← hχ, MulEquiv.symm_apply_apply]
  rfl

/-- Sections over the orbit, reindexed by the same representatives. -/
def sectionChange :
    ProductInducedOrbitSections ν π h hU ≃ₗ[ℂ] ProductInducedOrbitSections ν' π h hU where
  toFun q B := q ((representativeChange π ν ν' hker).symm B)
  invFun q B := q (representativeChange π ν ν' hker B)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sectionChange_apply (q : ProductInducedOrbitSections ν π h hU)
    (B : UnitaryOrbitRepresentative ν π) :
    sectionChange h hU π ν ν' hker q (representativeChange π ν ν' hker B) = q B := rfl

theorem sectionChange_coherent (q : ProductInducedOrbitSections ν π h hU)
    (hq : q ∈ coherentProductInducedOrbitSections ν π h hU) :
    sectionChange h hU π ν ν' hker q ∈ coherentProductInducedOrbitSections ν' π h hU :=
  fun B C a => hq ((representativeChange π ν ν' hker).symm B)
    ((representativeChange π ν ν' hker).symm C) a

/-- The compact picture of a section at a parameter depends on the unitary character only
through its values. -/
private theorem compactEquiv_sectionChange (q : ProductInducedOrbitSections ν π h hU)
    (χ₁ : unitaryUnramifiedCharacters ν) (χ₂ : unitaryUnramifiedCharacters ν')
    (hχ : χ₁.val = χ₂.val) :
    productInducedCompactEquiv ν' h K hP hK hν' hr hU hPK (unitaryUnramifiedInclusion ν' χ₂) π.obj
        (sectionChange h hU π ν ν' hker q
          ⟨IrreducibleAdmissibleRep.twist (unitaryUnramifiedInclusion ν' χ₂).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν' (unitaryUnramifiedInclusion ν' χ₂)) π, χ₂, rfl⟩) =
      productInducedCompactEquiv ν h K hP hK hν hr hU hPK (unitaryUnramifiedInclusion ν χ₁) π.obj
        (q ⟨IrreducibleAdmissibleRep.twist (unitaryUnramifiedInclusion ν χ₁).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ₁)) π, χ₁, rfl⟩) := by
  obtain ⟨v₁, p₁⟩ := χ₁
  obtain ⟨v₂, p₂⟩ := χ₂
  change v₁ = v₂ at hχ
  subst hχ
  rfl

variable {a : J → J' → ℤ}
  (ha : ∀ z : J' → Circle, (e'.symm z).val = (e.symm (finiteTorusMonomial a z)).val)

omit [Fintype J] in
include ha in
/-- After the monomial change of parameters, the reindexed section has the same compact
pictures. -/
theorem familyRestriction_sectionChange (q : ProductInducedOrbitSections ν π h hU)
    (z : J' → Circle) :
    productInducedFamilyRestriction ν' e' h K hP hK hν' hr hU hPK π.obj
        (productInducedOrbitPullback ν' π e' h hU (sectionChange h hU π ν ν' hker q)) z =
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q) (finiteTorusMonomial a z) :=
  compactEquiv_sectionChange h hU hP K hK hPK π hr ν hν ν' hν' hker q _ _ (ha z).symm

include ha in
/-- The reindexed section of a smooth section is smooth for the new coordinates. -/
theorem sectionChange_mem_smooth (q : ProductInducedOrbitSections ν π h hU)
    (hq : q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    sectionChange h hU π ν ν' hker q ∈
      productInducedSmoothOrbitSections ν' π e' h hU K hP hK hν' hr hPK := by
  refine ⟨sectionChange_coherent h hU π ν ν' hker q hq.1, ?_⟩
  have hfun : productInducedFamilyRestriction ν' e' h K hP hK hν' hr hU hPK π.obj
      (productInducedOrbitPullback ν' π e' h hU (sectionChange h hU π ν ν' hker q)) =
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q) ∘ finiteTorusMonomial a :=
    funext (familyRestriction_sectionChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha q)
  change productInducedFamilyRestriction ν' e' h K hP hK hν' hr hU hPK π.obj
      (productInducedOrbitPullback ν' π e' h hU (sectionChange h hU π ν ν' hker q)) ∈
    finiteSmoothFamilies J' (ProductInducedCompactPicture h K π.obj)
  rw [hfun]
  exact mem_finiteSmoothFamilies_comp_monomial hq.2 a

/-- Reindexing as a linear map of smooth orbit sections. -/
def smoothChange :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      productInducedSmoothOrbitSections ν' π e' h hU K hP hK hν' hr hPK :=
  LinearMap.restrict (sectionChange h hU π ν ν' hker).toLinearMap
    (fun q hq => sectionChange_mem_smooth h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha q hq)

/-- The compact pictures of the reindexed smooth section are those of the original section after
the monomial change of parameters. -/
theorem compactRestriction_smoothChange
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (z : J' → Circle) :
    productInducedSmoothOrbitCompactRestriction h hU ν' π K hP hK hν' hr hPK e'
        (smoothChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha q) z =
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e q
        (finiteTorusMonomial a z) :=
  familyRestriction_sectionChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha q.val z

/-- Reindexing preserves each level `C^∞(O,P)^{H×H}`. -/
def levelChange (H : OpenSubgroup G) :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      OrbitSectionLevel ν' π e' h hU K hP hK hν' hr hPK H :=
  LinearMap.restrict (sectionChange h hU π ν ν' hker).toLinearMap
    (p := orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H)
    (q := orbitSectionLevelSubmodule ν' π e' h hU K hP hK hν' hr hPK H)
    (fun q hq => ⟨sectionChange_mem_smooth h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha q hq.1,
      fun x => funext fun B => congrFun (hq.2 x) ((representativeChange π ν ν' hker).symm B)⟩)

theorem toSections_levelChange (H : OpenSubgroup G)
    (q : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :
    OrbitSectionLevel.toSections ν' π e' h hU K hP hK hν' hr hPK H
        (levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha H q) =
      smoothChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) :=
  rfl

include ha in
/-- **Seminorm transfer.** Every seminorm of a level for the new coordinates, evaluated on
reindexed sections, is bounded by a finite supremum of seminorms for the old coordinates. -/
theorem exists_levelChange_seminorm_bound [DecidableEq J] [DecidableEq J'] (H : OpenSubgroup G)
    (i : List J' × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    ∃ t : Finset (List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)), ∃ c : ℝ≥0,
      ∀ q, OrbitSectionLevel.seminormFamily ν' π e' h hU K hP hK hν' hr hPK H i
          (levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha H q) ≤
        (c : ℝ) * (t.sup (OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H)) q := by
  obtain ⟨t, c, hb⟩ := exists_orbitSectionLevel_monomialSeminorm_bound h hU hP K hK hPK ν π hν hr
    e H a (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => i.2)
    (fun q => orbitSectionCoefficient ν' π e' h hU K hP hK hν' hr hPK i.2
      (OrbitSectionLevel.toSections ν' π e' h hU K hP hK hν' hr hPK H
        (levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha H q)))
    (fun q z => by
      simp only [Finset.univ_unique, Finset.sum_singleton, orbitSectionCoefficient_apply,
        OneMemClass.coe_one, Pi.one_apply, one_mul]
      exact congrArg i.2 (familyRestriction_sectionChange h hU hP K hK hPK π hr ν hν e ν' hν' e'
        hker ha _ z)) i.1
  exact ⟨t, c, hb⟩

end SameLevi

/-! ### The wave packets of reindexed sections -/

section SamePacket

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hr : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {I' : Type uI'} (ν' : I' → (M →* ℝ≥0ˣ)) (hν' : ∀ i, Continuous (ν' i))
  {J' : Type uJ'} [Fintype J'] (e' : unitaryUnramifiedCharacters ν' ≃* (J' → Circle))
  (hker : commonNormKernel ν = commonNormKernel ν')
  {a : J → J' → ℤ}
  (ha : ∀ z : J' → Circle, (e'.symm z).val = (e.symm (finiteTorusMonomial a z)).val)
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  [Finite (discreteSeriesStabilizer C hC mu ν (discreteSeriesClass C hC mu π hsq))]
  (C' : Subgroup M) [C'.Normal] (hC' : C' ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C')] (mu' : Measure (M ⧸ C')) [mu'.IsHaarMeasure]
  (hsq' : IsSquareIntegrableModCentralSubgroup C' hC' π.obj.representation mu')
  [Finite (discreteSeriesStabilizer C' hC' mu' ν' (discreteSeriesClass C' hC' mu' π hsq'))]

omit [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The coefficient map at a representative does not depend on the norm family. -/
theorem representativeCoefficientMap_change (A : UnitaryOrbitRepresentative ν π)
    (F : productInducedCoefficientObject h hU (representativeChange π ν ν' hker A).val.obj) :
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν' π hr
        (representativeChange π ν ν' hker A) F =
      unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A F := by
  unfold unitaryOrbitRepresentativeCoefficientMap
  rfl

omit [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- **Wave packets of reindexed sections.** Let `T` be a homeomorphism between the orbits of
`π` for `ν` and for `ν'` that matches the classes of the same representatives, carries the
orbit measure of `ρ` to that of `ρ'` and the weight `w'` to `w`. Then the wave packet of a
reindexed section is the wave packet of the original section. -/
theorem inducedOrbitWavePacket_levelChange
    (ρ : Measure (unitaryUnramifiedCharacters ν)) (ρ' : Measure (unitaryUnramifiedCharacters ν'))
    (w : discreteSeriesOrbit C hC mu ν (discreteSeriesClass C hC mu π hsq) → ℂ)
    (w' : discreteSeriesOrbit C' hC' mu' ν' (discreteSeriesClass C' hC' mu' π hsq') → ℂ)
    (T : discreteSeriesOrbit C hC mu ν (discreteSeriesClass C hC mu π hsq) ≃ₜ
      discreteSeriesOrbit C' hC' mu' ν' (discreteSeriesClass C' hC' mu' π hsq'))
    (hT : ∀ A, T (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC mu hsq A) =
      unitaryOrbitRepresentativeDiscreteSeriesOrbit ν' π C' hC' mu' hsq'
        (representativeChange π ν ν' hker A))
    (hTmu : (discreteSeriesOrbitMeasure ν C hC mu (discreteSeriesClass C hC mu π hsq) ρ).map T =
      discreteSeriesOrbitMeasure ν' C' hC' mu' (discreteSeriesClass C' hC' mu' π hsq') ρ')
    (hw : ∀ x, w' (T x) = w x) (H : OpenSubgroup G)
    (q : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) (g : G) :
    inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν' π hν' hr e' C' hC' mu' hsq' ρ' w'
        (OrbitSectionLevel.toSections ν' π e' h hU K hP hK hν' hr hPK H
          (levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha H q)) g =
      inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC mu hsq ρ w
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) g := by
  unfold inducedOrbitWavePacket
  rw [← hTmu, T.measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC mu hsq x
  change w' _ * _ = w _ * _
  have hsec : (OrbitSectionLevel.toSections ν' π e' h hU K hP hK hν' hr hPK H
      (levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker ha H q)).val
        (representativeChange π ν ν' hker A) =
      (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q).val A := by
    rw [toSections_levelChange]
    exact sectionChange_apply h hU π ν ν' hker _ A
  rw [hw, hT A, unitaryOrbitCoefficientMap_representative,
    unitaryOrbitCoefficientMap_representative, representativeCoefficientMap_change, hsec]

end SamePacket

/-! ### Pointwise bounds from continuity and finite suprema of seminorms -/

section Estimate

variable {G : Type uG} [Group G] [TopologicalSpace G] {Ξ σ : G → ℝ}
  {E : Type uV} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {Idx : Type uI} {p : SeminormFamily ℂ E Idx}

/-- **Pointwise bounds from continuity.** A continuous linear map `L` from a space whose
topology is given by the seminorms `p` into `C(G)` satisfies
`|L x (g)| ≤ c · (sup_{i ∈ t} p_i)(x) · Ξ(g) (1 + σ(g))^{-r}` for some finite `t` and some `c`. -/
theorem exists_norm_le_of_continuousLinearMap (hp : WithSeminorms p) (hΞ : ∀ g, 0 < Ξ g)
    (hσ : ∀ g, 0 ≤ σ g) (L : E →L[ℂ] Space Ξ σ) (r : ℝ) :
    ∃ t : Finset Idx, ∃ c : ℝ≥0, ∀ x g,
      ‖L x g‖ ≤ (c : ℝ) * (t.sup p) x * (Ξ g * (1 + σ g) ^ (-r)) := by
  obtain ⟨t, c, -, hc⟩ := Seminorm.bound_of_continuous hp
    ((Space.seminorm Ξ σ r).comp L.toLinearMap)
    ((Space.continuous_seminorm (Ξ := Ξ) (σ := σ) r).comp L.continuous)
  refine ⟨t, c, fun x g => ?_⟩
  have h2 : (nu Ξ σ r (L x)).toReal ≤ (c : ℝ) * (t.sup p) x := hc x
  calc ‖L x g‖ ≤ (nu Ξ σ r (L x)).toReal * (Ξ g * (1 + σ g) ^ (-r)) :=
        norm_le_of_nu hΞ hσ (Space.nu_ne_top (L x) r) g
    _ ≤ (c : ℝ) * (t.sup p) x * (Ξ g * (1 + σ g) ^ (-r)) :=
        mul_le_mul_of_nonneg_right h2
          (mul_nonneg (hΞ g).le (Real.rpow_nonneg (by linarith [hσ g]) _))

omit [TopologicalSpace E] in
/-- **Finite suprema.** If each seminorm `p'_i`, `i ∈ t'`, composed with `L` is bounded by a
finite supremum of the `p_j`, then so is the finite supremum over `t'`. -/
theorem exists_finset_sup_comp_le {E' : Type uJ} [AddCommGroup E'] [Module ℂ E']
    {Idx' : Type uJ'} {p' : SeminormFamily ℂ E' Idx'} (L : E → E') (t' : Finset Idx')
    (ht : ∀ i ∈ t', ∃ t : Finset Idx, ∃ c : ℝ≥0, ∀ x, p' i (L x) ≤ (c : ℝ) * (t.sup p) x) :
    ∃ t : Finset Idx, ∃ c : ℝ≥0, ∀ x, (t'.sup p') (L x) ≤ (c : ℝ) * (t.sup p) x := by
  classical
  choose T C hTC using ht
  refine ⟨t'.attach.biUnion fun i => T i.1 i.2, ∑ i ∈ t'.attach, C i.1 i.2, fun x => ?_⟩
  refine Seminorm.finset_sup_apply_le (mul_nonneg (NNReal.coe_nonneg _) (apply_nonneg _ _))
    fun i hi => (hTC i hi x).trans ?_
  have hsub : T i hi ⊆ t'.attach.biUnion fun i => T i.1 i.2 :=
    Finset.subset_biUnion_of_mem (fun i : t' => T i.1 i.2) (Finset.mem_attach t' ⟨i, hi⟩)
  have hC : (C i hi : ℝ) ≤ ((∑ i ∈ t'.attach, C i.1 i.2 : ℝ≥0) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun i : t' => C i.1 i.2)
      (fun _ _ => zero_le) (Finset.mem_attach t' ⟨i, hi⟩)
  have hsup : (T i hi).sup p ≤ (t'.attach.biUnion fun i => T i.1 i.2).sup p :=
    Finset.sup_mono hsub
  exact mul_le_mul hC (hsup x) (apply_nonneg _ _) (NNReal.coe_nonneg _)

end Estimate

/-- A pointwise packet bound at a fixed coefficient level and decay order, controlled by
finitely many of that level's seminorms. -/
def LevelPacketBound {G : Type uG} {E : Type uV} [AddCommGroup E] [Module ℂ E]
    {J : Type uJ} (p : SeminormFamily ℂ E J) (packet : E → G → ℂ)
    (Ξ σ : G → ℝ) (r : ℝ) : Prop :=
  ∃ t : Finset J, ∃ c : ℝ≥0, ∀ q g,
    ‖packet q g‖ ≤ (c : ℝ) * (t.sup p) q * (Ξ g * (1 + σ g) ^ (-r))

/-! ### Equal subgroups, a monomial change of coordinates and a pulled-back representation -/

section SubgroupChange

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hr : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P' M' U' : Subgroup G} [LocallyCompactSpace P']
  (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G))
  (hP' : IsClosed (P' : Set G))
  (hPK' : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hδ' : ∀ p : P', Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U' hU' P' h'.le_normalizer p : ℝ≥0))
  (hr' : Continuous h'.projection)
  {I' : Type uI'} (ν' : I' → (M' →* ℝ≥0ˣ)) (hν' : ∀ i, Continuous (ν' i))
  {J' : Type uJ'} [Fintype J'] [DecidableEq J']
  (e' : unitaryUnramifiedCharacters ν' ≃* (J' → Circle))
  (φ : M' ≃ₜ* M)
  [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (C' : Subgroup M') [C'.Normal] (hC' : C' ≤ Subgroup.center M')
  [MeasurableSpace (M' ⧸ C')] [BorelSpace (M' ⧸ C')] (mu' : Measure (M' ⧸ C')) [mu'.IsHaarMeasure]
  (hCC : C'.map φ.toMulEquiv.toMonoidHom = C)
  (hmu : mu'.map (quotientContinuousMulEquiv φ C C' hCC) = mu)
  (π' : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M'))
  (hsq' : IsSquareIntegrableModCentralSubgroup C' hC' π'.obj.representation mu')

set_option hygiene false in
local notation "ω" => discreteSeriesClass C hC mu π hsq
set_option hygiene false in
local notation "ω'" => discreteSeriesClass C' hC' mu' π' hsq'

/-- **Change of subgroups, coordinates and representation.** Let `(P, M, U)` and `(P', M', U')`
be two semidirect decompositions with the same points, identified by `φ : M' ≃ₜ* M` with
`φ x = x` in `G`; let `ν`, `ν'` be norm families with the same norm-one subgroup, `e`, `e'`
coordinates on the unitary unramified characters, where `e` is given by evaluation at points
of `M` and `e'` is Laurent; let `π' = π ∘ φ`. Suppose a homeomorphism `T` of the orbits lifts
the pullback of classes, carries the orbit measure of `ρ` to that of `ρ'`, and carries the
weight `w'` to `w`. Then there are linear maps between the levels `C^∞(O,P)^{H×H}` that
preserve the wave packets and whose new seminorms are bounded by finitely many old ones. -/
theorem exists_subgroupChange
    [Finite (discreteSeriesStabilizer C hC mu ν (ω))]
    [Finite (discreteSeriesStabilizer C' hC' mu' ν' (ω'))]
    (ρ : Measure (unitaryUnramifiedCharacters ν)) (ρ' : Measure (unitaryUnramifiedCharacters ν'))
    (w : discreteSeriesOrbit C hC mu ν (ω) → ℂ) (w' : discreteSeriesOrbit C' hC' mu' ν' (ω') → ℂ)
    (T : discreteSeriesOrbit C hC mu ν (ω) ≃ₜ discreteSeriesOrbit C' hC' mu' ν' (ω'))
    (hT : ∀ x, (T x).val = DiscreteSeriesClass.pullback φ C hC C' hC' hCC mu mu' hmu x.val)
    (hTmu : (discreteSeriesOrbitMeasure ν C hC mu (ω) ρ).map T =
      discreteSeriesOrbitMeasure ν' C' hC' mu' (ω') ρ')
    (hw : ∀ x, w' (T x) = w x)
    (hφ : ∀ x, (φ x : G) = x) (hPP : P' = P) (hUU : U' = U)
    (hπ : π' = IrreducibleAdmissibleRep.pullback φ π)
    (hker : ∀ x : M', x ∈ commonNormKernel ν' ↔ φ x ∈ commonNormKernel ν)
    (hcoord : HasEvaluationUnitaryCoordinates ν e)
    (he' : HasLaurentUnitaryCoordinates ν' e') :
    ∃ L : ∀ H : OpenSubgroup G, OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
        OrbitSectionLevel ν' π' e' h' hU' K hP' hK hν' hr' hPK' H,
      (∀ H q g, inducedOrbitWavePacket h' hU' hP' K hK hPK' hG hδ' ν' π' hν' hr' e' C' hC' mu'
          hsq' ρ' w' (OrbitSectionLevel.toSections ν' π' e' h' hU' K hP' hK hν' hr' hPK' H
            (L H q)) g =
        inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC mu hsq ρ w
          (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) g) ∧
      (∀ H (i : List J' × Module.Dual ℂ (ProductInducedCompactPicture h' K π'.obj)),
        ∃ t : Finset (List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)),
          ∃ c : ℝ≥0, ∀ q,
            OrbitSectionLevel.seminormFamily ν' π' e' h' hU' K hP' hK hν' hr' hPK' H i (L H q) ≤
              (c : ℝ) * (t.sup (OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H)) q) := by
  classical
  have hMM : M' = M := by
    ext x
    constructor
    · intro hx
      have hmem := (φ ⟨x, hx⟩).property
      rwa [hφ] at hmem
    · intro hx
      obtain ⟨y, hy⟩ := φ.surjective ⟨x, hx⟩
      have hyx : (y : G) = x := (hφ y).symm.trans (congrArg Subtype.val hy)
      exact hyx ▸ y.property
  subst hMM hPP hUU
  obtain rfl : φ = ContinuousMulEquiv.refl _ :=
    ContinuousMulEquiv.ext fun x => Subtype.ext (hφ x)
  have hker' : commonNormKernel ν = commonNormKernel ν' := by
    ext x
    exact (hker x).symm
  obtain ⟨n, ha⟩ := exists_monomial_of_eval ν e ν' e' hker' hcoord he'
  obtain rfl : π = π' := hπ.symm
  refine ⟨levelChange h hU hP K hK hPK π hr ν hν e ν' hν' e' hker' ha, ?_, ?_⟩
  · intro H q x
    exact inducedOrbitWavePacket_levelChange h hU hP K hK hPK hG hδ π hr ν hν e ν' hν' e'
      hker' ha C hC mu hsq C' hC' mu' hsq' ρ ρ' w w' T (fun A => Subtype.ext (hT _)) hTmu hw H q x
  · intro H i
    exact exists_levelChange_seminorm_bound h hU hP K hK hPK π hr ν hν e ν' hν' e' hker' ha H i

/-- **Packet bounds from continuous synthesis after a change of subgroups.** In the situation of
`exists_subgroupChange`, suppose the wave packets for `(P', M', U')` are the values of a continuous
linear synthesis map from `C^∞(O,P')` into the Schwartz space `C(G)` of weights `Ξ`, `σ`. Then for
every open `H ≤ K` and every `r` the wave packets for `(P, M, U)` of sections of the level
`C^∞(O,P)^{H×H}` satisfy `|E(q)(g)| ≤ c · (sup_{i ∈ t} p_i)(q) · Ξ(g) (1 + σ(g))^{-r}`. -/
theorem exists_packet_bound_of_subgroupChange
    [Finite (discreteSeriesStabilizer C hC mu ν (ω))]
    [Finite (discreteSeriesStabilizer C' hC' mu' ν' (ω'))]
    (ρ : Measure (unitaryUnramifiedCharacters ν)) (ρ' : Measure (unitaryUnramifiedCharacters ν'))
    (w : discreteSeriesOrbit C hC mu ν (ω) → ℂ) (w' : discreteSeriesOrbit C' hC' mu' ν' (ω') → ℂ)
    (T : discreteSeriesOrbit C hC mu ν (ω) ≃ₜ discreteSeriesOrbit C' hC' mu' ν' (ω'))
    (hT : ∀ x, (T x).val = DiscreteSeriesClass.pullback φ C hC C' hC' hCC mu mu' hmu x.val)
    (hTmu : (discreteSeriesOrbitMeasure ν C hC mu (ω) ρ).map T =
      discreteSeriesOrbitMeasure ν' C' hC' mu' (ω') ρ')
    (hw : ∀ x, w' (T x) = w x)
    (hφ : ∀ x, (φ x : G) = x) (hPP : P' = P) (hUU : U' = U)
    (hπ : π' = IrreducibleAdmissibleRep.pullback φ π)
    (hker : ∀ x : M', x ∈ commonNormKernel ν' ↔ φ x ∈ commonNormKernel ν)
    (hcoord : HasEvaluationUnitaryCoordinates ν e)
    (he' : HasLaurentUnitaryCoordinates ν' e')
    {Ξ σ : G → ℝ} (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (synth : OrbitSectionSpace ν' π' e' h' hU' K hP' hK hν' hr' hPK' →L[ℂ] Space Ξ σ)
    (hsynth : ∀ q g, synth q g = inducedOrbitWavePacket h' hU' hP' K hK hPK' hG hδ' ν' π' hν' hr'
      e' C' hC' mu' hsq' ρ' w' (OrbitSectionSpace.toSections ν' π' e' h' hU' K hP' hK hν' hr' hPK' q) g)
    (H : OpenSubgroup G) (hH : H ≤ K) (r : ℝ) :
    LevelPacketBound (OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H)
      (fun q => inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC mu hsq ρ w
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q)) Ξ σ r := by
  obtain ⟨L, hpacket, hbound⟩ := exists_subgroupChange h hU hP K hK hPK hG hδ π hr ν hν e h' hU'
    hP' hPK' hδ' hr' ν' hν' e' φ C hC mu hsq C' hC' mu' hCC hmu π' hsq' ρ ρ' w w' T hT hTmu hw
    hφ hPP hUU hπ hker hcoord he'
  obtain ⟨t', c', hc'⟩ := exists_norm_le_of_continuousLinearMap
    (OrbitSectionLevel.withSeminorms ν' π' e' h' hU' K hP' hK hν' hr' hPK' H) hΞ hσ
    (synth.comp (OrbitSectionSpace.ofLevelCLM ν' π' e' h' hU' K hP' hK hν' hr' hPK' ⟨H, hH⟩)) r
  obtain ⟨t, c, hc⟩ := exists_finset_sup_comp_le (L H) t' (fun i _ => hbound H i)
  refine ⟨t, c' * c, fun q g => ?_⟩
  have heq : (synth.comp (OrbitSectionSpace.ofLevelCLM ν' π' e' h' hU' K hP' hK hν' hr' hPK'
      ⟨H, hH⟩)) (L H q) g =
      inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC mu hsq ρ w
        (OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H q) g :=
    (hsynth _ g).trans (hpacket H q g)
  have hX : 0 ≤ Ξ g * (1 + σ g) ^ (-r) :=
    mul_nonneg (hΞ g).le (Real.rpow_nonneg (by linarith [hσ g]) _)
  dsimp only
  rw [← heq]
  refine (hc' _ g).trans ?_
  rw [NNReal.coe_mul, mul_assoc (c' : ℝ) (c : ℝ)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hc q) (NNReal.coe_nonneg _)) hX

end SubgroupChange

/-! ### Norm-one subgroups along scheme isomorphisms -/

section SchemeIsoKernel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {L L' : GroupScheme (Spec (CommRingCat.of F))}

end SchemeIsoKernel

/-! ### The dynamic circle coordinates are evaluations -/

section DynamicCoordinates

open Langlands.Plancherel.DynamicOppositeStandardIntertwining

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H) (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H)

omit [LocallyOfFiniteType H.X.hom] in
/-- **The dynamic circle coordinates are evaluations.** Each coordinate of
`DynamicInducedOrbit.leviUnitaryCoordinates` on `Im X(Z_H(χ))` is the evaluation at a point of
the literal Levi `Z_H(χ)(F)`. -/
theorem hasEvaluationUnitaryCoordinates_levi :
    HasEvaluationUnitaryCoordinates (leviNormCharacters χ)
      (DynamicInducedOrbit.leviUnitaryCoordinates hH χ).toMulEquiv := by
  intro j
  obtain ⟨g, hg⟩ := exists_rationalCanonicalUnitaryCoordinate_eq_eval (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hH) j
  refine ⟨parameterHomeomorph χ g, fun z => ?_⟩
  have h := hg
    ((unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ) (normCharacters χ)).symm z)
  change (((DynamicInducedOrbit.leviUnitaryCoordinates hH χ).toMulEquiv z j : Circle) : ℂ) = _
    at h
  have h2 : ((unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ)
      (normCharacters χ)).symm z).val g = z.val (parameterHomeomorph χ g) := by
    obtain ⟨y, rfl⟩ :=
      (unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ) (normCharacters χ)).surjective z
    rw [ContinuousMulEquiv.symm_apply_apply, unitaryUnramifiedCharactersHomeomorph_apply,
      ContinuousMulEquiv.symm_apply_apply]
  rw [h, h2]

end DynamicCoordinates

/-! ### The two restrictions of characters to the centralizer scheme -/

section StandardRestrict

open Langlands.Plancherel.DynamicOppositeStandardIntertwining

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance lowerPacketRestrictLeviClosed (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance lowerPacketRestrictLeviAffine (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance lowerPacketRestrictLeviTopology (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

omit [LocallyOfFiniteType G.X.hom] in
/-- **The two restrictions agree.** If a unitary unramified character `z` of `M_I(F)` and a
unitary unramified character `y` of `Z_G(ζ ∘ i)(F)` agree under `Z_G(ζ ∘ i)(F) = M_I(F)`, then
their restrictions to the points of the centralizer scheme agree. -/
theorem standardLeviCharacterRestrict_eq_leviCharacterRestrict
    (z : unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I))
    (y : unitaryUnramifiedCharacters (leviNormCharacters (CommGroupScheme.groupHom ζ ≫ i)))
    (hzy : ∀ m, z.val (standardLeviDynamicHomeomorph hG hi hν I hζ m) = y.val m) :
    standardLeviCharacterRestrict hG hi hν I hζ z =
      DynamicInducedOrbit.leviCharacterRestrict (CommGroupScheme.groupHom ζ ≫ i) y :=
  Subtype.ext (ContinuousMonoidHom.ext fun m =>
    (standardLeviCharacterRestrict_apply hG hi hν I hζ z m).trans (hzy _))

end StandardRestrict

/-! ### Functions on orbits that factor through restrictions of characters -/

section OrbitFunction

/-- Let `q`, `q'` be surjective parametrizations of two orbits, `T` a map of orbits lifting the
map `c` of parameters, and `W`, `W'` functions on the orbits given through `R`, `R'` by the same
function `f`. If `R' ∘ c = R`, then `W' ∘ T = W`. -/
theorem apply_eq_of_orbitMap {X X' Y Z Z' : Type*} {q : Z → X} (hq : Function.Surjective q)
    {q' : Z' → X'} {T : X → X'} {c : Z → Z'} (hT : ∀ z, T (q z) = q' (c z))
    {W : X → ℂ} {W' : X' → ℂ} {f : Y → ℂ} {R : Z → Y} {R' : Z' → Y}
    (hW : ∀ z, W (q z) = f (R z)) (hW' : ∀ z', W' (q' z') = f (R' z'))
    (hR : ∀ z, R' (c z) = R z) (x : X) : W' (T x) = W x := by
  obtain ⟨z, rfl⟩ := hq x
  rw [hT, hW', hR, hW]

end OrbitFunction

/-! ### The lower packets of the weak expansion at the chamber of `sζ` -/

section Lower

open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open RationalPointFamily WeakExpansion LowerChamber LowerSplitCenter

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerPacketLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerPacketLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hi : IsMaximalSplitTorus i) (I' : Finset (SimpleRoot i ν))
  (ζ : cocharacterLattice T) (n : normalizerPoints i)
  (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)

set_option hygiene false in
local notation "M'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "c" => lowerChamber hi I' ζ n
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "hiL" => lowerTorus_isMaximalSplitTorus hi I'
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "e₀" => lowerChamberLeviHomeomorph hi I' ζ n hG hν
set_option hygiene false in
local notation "e₁" => lowerChamberLeviEquiv hi I' ζ n hG hν
set_option hygiene false in
local notation "Φ₂" => standardLeviParameterIso hM' hiL (c).isGeneric (c).labels (c).isStandard
set_option hygiene false in
local notation "𝐋'" => Standard.leviScheme iL (c).chamber (rootSet iL (c).chamber (c).labels)
-- The standard Levi `M_{J''}(F)` of `M'` for the chamber of `sζ`, as in the target.
set_option hygiene false in
local notation "𝐌'" => {x : rationalPoints M' //
  @Membership.mem (rationalPoints M') (Subgroup (rationalPoints M')) _
    (standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels)) x}

/-! #### Norm-one subgroups and circle coordinates -/

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- `Z_{M'}(sζ)(F) = M_{J''}(F)` on points of the centralizer scheme of `χ_s`, read in
`Z_{M'}(sζ)(F)`. -/
theorem lowerChamberLeviEquiv_map_standardLeviParameterIso
    (m : rationalPoints (parameterScheme χs)) :
    e₁ (leviRationalPointHomeomorph iL (c).chamber (c).labels (rationalPoints.map (Φ₂).hom m)) =
      parameterHomeomorph (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ iL) m :=
  (congrArg (e₁) (leviRationalPointHomeomorph_lowerParameterLeviIso hi I' ζ n hG hν m)).trans
    ((e₀).symm_apply_apply _)

/-- **The norm-one subgroups agree.** Under `Z_{M'}(sζ)(F) = M_{J''}(F)`, the norm-one subgroup of
`M_{J''}(F)` for its rational characters is that of `(s·M)(F)` for the characters of the
centralizer scheme of `χ_s`. -/
theorem mem_commonNormKernel_lowerChamberLeviEquiv (x : 𝐌') :
    x ∈ commonNormKernel (leviRationalNormCharacters iL (c).chamber (c).labels) ↔
      e₁ x ∈ commonNormKernel (leviNormCharacters χs) := by
  obtain ⟨y, rfl⟩ := (leviRationalPointHomeomorph iL (c).chamber (c).labels).surjective x
  obtain ⟨m, rfl⟩ : ∃ m : rationalPoints (parameterScheme χs),
      rationalPoints.map (Φ₂).hom m = y :=
    ⟨rationalPoints.map (Φ₂).inv y, rationalPoints_map_hom_inv (Φ₂) y⟩
  rw [lowerChamberLeviEquiv_map_standardLeviParameterIso]
  refine (mem_commonNormKernel _ _).trans (Iff.trans ?_ (mem_commonNormKernel _ _).symm)
  simp only [leviRationalNormCharacters_apply_points]
  have hsymm : (parameterHomeomorph χs).symm
      (parameterHomeomorph (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ iL) m) = m :=
    ContinuousMulEquiv.symm_apply_apply _ _
  exact (mem_commonNormKernel _ _).symm.trans
    ((Langlands.Geometry.Building.ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff (Φ₂) m).trans ((mem_commonNormKernel _ _).trans
    (forall_congr' fun ψ => Iff.of_eq (congrArg (fun y => normCharacters χs ψ y = 1) hsymm.symm))))

/-! #### The Plancherel weights correspond -/

variable (I : Finset (SimpleRoot i ν)) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left] (s : A.toGrp ⟶ 𝐋)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "CM'" => rationalLeviSplitCenter (c).labels (lowerSplit hi I' ζ n hG hν I hζ hn s)
set_option hygiene false in
local notation "sC" => lowerCentral hG hi hν I I' hζ n hn CM

variable [(CM).Normal] [(CM').Normal]
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  [MeasurableSpace (𝐌' ⧸ CM')] [BorelSpace (𝐌' ⧸ CM')]
  (hs : IsSplitComponent s)

set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "hCM'" => rationalLeviSplitCenter_le_center (c).labels
  (lowerSplit hi I' ζ n hG hν I hζ hn s) (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
set_option hygiene false in
local notation "hsC" => lowerCentral_le_center hG hi hν I I' hζ n hn CM hCM
set_option hygiene false in
local notation "mu'" => lowerChamberQuotientMeasure hi I' ζ n hG hν I hζ hn s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "π'" => lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π
set_option hygiene false in
local notation "hsq'" => lowerChamberRepresentation_isSquareIntegrable hi I' ζ n hG hν I hζ hn s
  mu hs π hsq
set_option hygiene false in
local notation "sμ" => lowerMeasure hG hi hν I I' hζ n hn CM mu
set_option hygiene false in
local notation "sω" => discreteSeriesClass (sC) hsC (sμ)
  (lowerRepresentation hG hi hν I I' hζ n hn π)
  (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)

/-- A lower density package `P`, read as density data at `M'` for the inducing
representation `π' ∘ e₀` of the target (`lowerDensityPackage_eq`). -/
abbrev lowerChamberPackage (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST) :
    DynamicInducedOrbit.DensityPackage iL (conjugatedCocharacter i ζ n) hRefl hCST hM'
      (SmoothRep.pullback (e₀) (π').obj) :=
  P

-- The Plancherel weight of the source-normalized target at `M'`, with the data of a package.
set_option hygiene false in
local notation "W'[" P "]" => standardLeviPlancherelWeight hM' hiL (c).isGeneric (c).labels
  (c).isStandard π' CM' hCM' mu' hsq' hRefl hCST (P).K (P).hK (P).hPK (P).hOppK (P).p (P).q
  (P).hDForward (P).hneForward (P).hDForwardΩ (P).hDReverse (P).hneReverse (P).hDReverseΩ
  (P).hD (P).hne (P).hirr (P).hreg
set_option hygiene false in
local notation "P'" => lowerChamberPackage hi I' ζ n hG hν I hζ hn π hRefl hCST P

set_option hygiene false in
local notation "ω'" => discreteSeriesClass CM' hCM' mu' π' hsq'

set_option maxHeartbeats 1000000 in
omit [IsAffine A.X.left] [(CM').Normal] [MeasurableSpace (𝐌' ⧸ CM')] [BorelSpace (𝐌' ⧸ CM')] in
/-- The lower density at `sπ ⊗ z` is the package weight at the restriction of `z`. -/
theorem lowerPlancherelWeight_orbitMap
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (z : unitaryUnramifiedCharacters (leviNormCharacters χs)) :
    lowerPlancherelWeight hG hi hν I I' hζ n hn CM hCM mu π hsq hRefl hCST P
        (discreteSeriesOrbitMap (sC) hsC (sμ) (leviNormCharacters χs) (sω) z) =
      DynamicInducedOrbit.DensityPackage.weight P (DynamicInducedOrbit.leviCharacterRestrict χs z) :=
  @DynamicInducedOrbit.orbitPlancherelWeight_orbitMap _ _ _ _ _ _ _ _ _ iL
    (conjugatedCocharacter i ζ n) hRefl hCST hM' (lowerRepresentation hG hi hν I I' hζ n hn π) (sC)
    (lowerCentral_normal hG hi hν I I' hζ n hn CM) hsC
    (lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn CM) (sμ)
    (lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn CM mu)
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq) P z

omit [IsAffine A.X.left] in
/-- The target's Plancherel weight at `π' ⊗ z` is the package weight at the restriction of `z`. -/
theorem standardLeviPlancherelWeight_lowerChamberPackage_orbitMap
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (z : unitaryUnramifiedCharacters (leviRationalNormCharacters iL (c).chamber (c).labels)) :
    W'[P'] (discreteSeriesOrbitMap CM' hCM' mu' (leviRationalNormCharacters iL (c).chamber
        (c).labels) (ω') z) =
      DynamicInducedOrbit.DensityPackage.weight P
        (standardLeviCharacterRestrict hM' hiL (c).isGeneric (c).labels (c).isStandard z) :=
  standardLeviPlancherelWeight_orbitMap hM' hiL (c).isGeneric (c).labels
    (c).isStandard π' CM' hCM' mu' hsq' hRefl hCST (P').K (P').hK (P').hPK (P').hOppK (P').p
    (P').q (P').hDForward (P').hneForward (P').hDForwardΩ (P').hDReverse (P').hneReverse
    (P').hDReverseΩ (P').hD (P').hne (P').hirr (P').hreg z

set_option maxHeartbeats 2000000 in
omit [IsAffine A.X.left] in
/-- **The Plancherel weights correspond.** Along `lowerChamberOrbitTransport`, the Plancherel
weight of the source-normalized target at `M'` (for the chamber of `sζ`, the representation
`π'` and the data of a lower density package `P`) is the lower density
`lowerPlancherelWeight P`. -/
theorem standardLeviPlancherelWeight_lowerChamberOrbitTransport
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (x : discreteSeriesOrbit (sC) hsC (sμ) (leviNormCharacters χs) (sω)) :
    W'[P'] (lowerChamberOrbitTransport hi I' ζ n hG hν I hζ hn s mu hs π hsq x) =
      lowerPlancherelWeight hG hi hν I I' hζ n hn CM hCM mu π hsq hRefl hCST P x :=
  apply_eq_of_orbitMap
    (isOpenQuotientMap_discreteSeriesOrbitMap (sC) hsC (sμ) (leviNormCharacters χs)
      (sω)).surjective
    (lowerChamberOrbitTransport_orbitMap hi I' ζ n hG hν I hζ hn s mu hs π hsq)
    (lowerPlancherelWeight_orbitMap hi I' ζ n hG hν I hζ hn s mu hs π hsq hRefl hCST P)
    (standardLeviPlancherelWeight_lowerChamberPackage_orbitMap hi I' ζ n hG hν I hζ hn s mu hs π
      hsq hRefl hCST P)
    (fun z => standardLeviCharacterRestrict_eq_leviCharacterRestrict hM' hiL (c).isGeneric
      (c).labels (c).isStandard _ z fun m =>
        (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn z (e₀ m)).trans
          (congrArg z.val ((e₀).symm_apply_apply m)))
    x

end Lower

end Langlands.HarishChandraSchwartz.LowerPacket
