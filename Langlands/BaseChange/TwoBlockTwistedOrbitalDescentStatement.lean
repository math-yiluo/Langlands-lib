import Langlands.Analysis.Local.ProductModularCharacter
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.BaseChange.ExactNormLeviCentralizer
import Langlands.BaseChange.NormalizedParabolicConstantTerm
import Langlands.BaseChange.RegularSemisimpleLevi
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.BaseChange.RelativeParabolicDiscriminantRegular
import Langlands.BaseChange.TwistedOrbitalConjugation
import Langlands.LocalField.FiniteExtensionModuleTopology

/-! # Twisted orbital descent at a regular two-block Levi representative -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure _root_.Topology
open GeneralLinear HarmonicAnalysis JacquetLanglands
open Langlands.ProductLeviChamber Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- A regular nonelliptic cyclic norm gives a representative in a proper two-block Levi.
The representative has exact block norms, and its twisted centralizer lies in the Levi. -/
theorem exists_twoBlock_of_sigmaRegular_of_not_sigmaElliptic
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l n : ℕ} (hσ : σ ^ l = 1) (hn : 0 < n)
    {δ : GeneralLinear n E} (hreg : IsSigmaRegular σ l δ) (hell : ¬ IsSigmaElliptic σ l δ) :
    ∃ (k : ℕ) (hk : 0 < k) (hkn : k < n),
      let B := twoBlock n k hk hkn
      ∃ (m : B.Levi F) (d : B.Levi E) (x : GeneralLinear n E),
        twistedConj (entrywiseAut σ n) x δ = B.leviEmbedding E d ∧
        IsRegularSemisimple (B.leviEmbedding F m) ∧
        (∀ i, IsRegularSemisimple (m i)) ∧
        (∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i)) ∧
        sigmaCentralizer σ n (B.leviEmbedding E d) ≤ B.leviSubgroup E := by
  obtain ⟨γ, hassoc, hγ⟩ := hreg
  have hγell : ¬ IsRegularElliptic γ := fun h => hell ⟨γ, hassoc, h⟩
  obtain ⟨k, hk, hkn, g, m, hgm, -⟩ :=
    exists_twoBlock_of_regularSemisimple_of_not_regularElliptic hn γ hγ hγell
  let B := twoBlock n k hk hkn
  have hm : IsRegularSemisimple (B.leviEmbedding F m) := by
    rw [← hgm]
    exact (isRegularSemisimple_conj_iff g γ).2 hγ
  have hassocM : IsNormAssociated σ l δ (B.leviEmbedding F m) := by
    have h := hassoc.twistedConj hσ 1 g
    rwa [inv_one, one_mul, map_one, mul_one, hgm] at h
  obtain ⟨x, d, hxd, hd⟩ := regularLeviNormRepresentative F E σ l n hσ B m δ hassocM hm
  have hnorm := cyclicNorm_leviEmbedding_eq_of_blockwise B m d (fun i => (hd i).1)
  exact ⟨k, hk, hkn, m, d, x, hxd, hm, fun i => (hd i).2, fun i => (hd i).1,
    sigmaCentralizer_le_leviSubgroup_of_regularNorm B hσ hnorm hm⟩

/-- The relative discriminant factor in twisted orbital descent with volume-one Haar
normalizations on the ambient group and Levi. -/
def twistedOrbitalDescentFactor
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {E : Type v} [Field E] [Algebra F E] [FiniteDimensional F E] {n : ℕ}
    (σ : E ≃ₐ[F] E) (B : BlockShape n) (d : B.Levi E) : ℝ :=
  (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F
    (twistedRelativeParabolicDiscriminant B σ d)))⁻¹

/-- A regular exact norm makes the relative discriminant factor strictly positive. -/
theorem twistedOrbitalDescentFactor_pos_of_exactNorm
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {E : Type v} [Field E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l n : ℕ} (hE : IsCyclicAlgebra σ l)
    (B : BlockShape n) {m : B.Levi F} {d : B.Levi E}
    (hm : IsRegularSemisimple (B.leviEmbedding F m))
    (hd : cyclicNorm σ l (B.leviEmbedding E d) = baseChange F E n (B.leviEmbedding F m)) :
    letI : FiniteDimensional F E := hE.1
    0 < twistedOrbitalDescentFactor σ B d := by
  let : FiniteDimensional F E := hE.1
  exact inv_pos.mpr (Real.sqrt_pos_of_pos
    ((LocalField.residueNormalizedAbsoluteValue F).pos
      (twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm B hE hd hm)))

section Centralizer

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}
  (σ : E ≃ₐ[F] E) (B : BlockShape n) (d : B.Levi E)

/-- If the ambient twisted centralizer lies in the Levi, the block diagonal embedding
identifies it with the twisted centralizer in the Levi product. -/
def twistedLeviCentralizerEquiv
    (hC : sigmaCentralizer σ n (B.leviEmbedding E d) ≤ B.leviSubgroup E) :
    twistedCentralizer (leviAut σ B) d ≃ₜ*
      sigmaCentralizer σ n (B.leviEmbedding E d) := by
  let H := sigmaCentralizer σ n (B.leviEmbedding E d)
  let e : H.subgroupOf (B.leviSubgroup E) ≃ₜ* H :=
    { Subgroup.subgroupOfEquivOfLe hC with
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  refine (subgroupContinuousMulEquiv (B.leviEquivContinuous E) _ _ fun m => ?_).trans e
  change twistedConj (entrywiseAut σ n) (B.leviEmbedding E m) (B.leviEmbedding E d) =
    B.leviEmbedding E d ↔ twistedConj (leviAut σ B) m d = d
  simp only [twistedConj, entrywiseAut_leviEmbedding, ← map_inv, ← map_mul]
  exact (B.leviEmbedding_injective E).eq_iff

@[simp] theorem twistedLeviCentralizerEquiv_apply_val
    (hC : sigmaCentralizer σ n (B.leviEmbedding E d) ≤ B.leviSubgroup E)
    (z : twistedCentralizer (leviAut σ B) d) :
    (twistedLeviCentralizerEquiv σ B d hC z).val = B.leviEmbedding E z.val := rfl

end Centralizer

section Haar

open scoped ENNReal

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ}

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology

/-- The compact open set of integral points in the actual Levi product. -/
def leviIntegralCompacts (B : BlockShape n) : TopologicalSpace.PositiveCompacts (B.Levi E) where
  carrier := Set.univ.pi fun i => (standardMaximalCompact E (B.size i) :
    Set (GeneralLinear (B.size i) E))
  isCompact' := isCompact_univ_pi fun i => isCompact_standardMaximalCompact E (B.size i)
  interior_nonempty' := by
    have ho := isOpen_set_pi Set.finite_univ
      (fun (i : Fin B.length) _ => isOpen_standardMaximalCompact E (B.size i))
    rw [ho.interior_eq]
    exact ⟨1, fun i _ => (standardMaximalCompact E (B.size i)).one_mem⟩

@[simp] theorem coe_leviIntegralCompacts (B : BlockShape n) :
    (leviIntegralCompacts E B : Set (B.Levi E)) =
      {m | ∀ i, m i ∈ standardMaximalCompact E (B.size i)} := by
  ext m
  simp [leviIntegralCompacts]

variable (B : BlockShape n) [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]

private theorem leviHaar_rightInvariant (μ : Measure (B.Levi E)) [μ.IsHaarMeasure]
    [μ.InnerRegular] :
    μ.IsMulRightInvariant := by
  have hχ (i : Fin B.length) (g : GeneralLinear (B.size i) E) : modularCharacter g = 1 := by
    let _ : MeasurableSpace (GeneralLinear (B.size i) E) := borel _
    have _ : BorelSpace (GeneralLinear (B.size i) E) := ⟨rfl⟩
    let ν : Measure (GeneralLinear (B.size i) E) := Measure.haar
    have : ν.IsMulRightInvariant := generalLinear_haar_rightInvariant E (B.size i) ν
    change modularCharacterFun g = 1
    rw [modularCharacterFun_eq_haarScalarFactor ν g]
    have hfactor (ν' : Measure (GeneralLinear (B.size i) E)) [ν'.IsHaarMeasure]
        (hν : ν' = ν) : haarScalarFactor ν' ν = 1 := by
      subst ν'
      exact haarScalarFactor_self _
    exact hfactor _ (map_mul_right_eq_self ν g)
  refine ⟨fun m => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul]
  have hm : modularCharacterFun m = 1 := by
    change modularCharacter m = 1
    rw [Langlands.ProductMeasure.modularCharacter_pi]
    simp [hχ]
  rw [hm, one_smul]

/-- Haar measure on the Levi with its integral points of volume one. -/
def orbitalDescentLeviHaar : Measure (B.Levi E) :=
  Measure.haarMeasure (leviIntegralCompacts E B)

instance orbitalDescentLeviHaar_isHaarMeasure : (orbitalDescentLeviHaar E B).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance orbitalDescentLeviHaar_isMulRightInvariant :
    (orbitalDescentLeviHaar E B).IsMulRightInvariant := by
  let : (orbitalDescentLeviHaar E B).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact leviHaar_rightInvariant E B _

theorem orbitalDescentLeviHaar_integral :
    orbitalDescentLeviHaar E B {m | ∀ i, m i ∈ standardMaximalCompact E (B.size i)} = 1 := by
  rw [← coe_leviIntegralCompacts]
  exact Measure.haarMeasure_self

end Haar

set_option linter.style.haveILetI false in
/-- Twisted orbital descent for a regular exact norm in a two-block Levi, with compatible
quotient measures formed from the same centralizer Haar measure. -/
def TwoBlockTwistedOrbitalDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l),
    letI : FiniteDimensional F E := hE.1
    letI := LocalField.FiniteExtension.valuativeRel F E
    letI := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
    ∀ (k : ℕ) (hk : 0 < k) (hkn : k < n),
    let B := twoBlock n k hk hkn
    letI : MeasurableSpace (B.Levi E) := borel _
    letI : BorelSpace (B.Levi E) := ⟨rfl⟩
    ∀ [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (m : B.Levi F) (d : B.Levi E),
      IsRegularSemisimple (B.leviEmbedding F m) →
      (∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i)) →
      ∀ (hC : sigmaCentralizer σ n (B.leviEmbedding E d) ≤ B.leviSubgroup E)
        (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
        (μH : Measure (sigmaCentralizer σ n (B.leviEmbedding E d)))
        [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
        (νG : Measure (LeftQuotient (sigmaCentralizer σ n (B.leviEmbedding E d)))),
        IsCompatible _ μG μH νG →
        let e := twistedLeviCentralizerEquiv σ B d hC
        let μHM := Measure.map e.symm μH
        letI : μHM.IsMulRightInvariant := isMulRightInvariant_map e.symm μH
        ∀ (νM : Measure (LeftQuotient (twistedCentralizer (leviAut σ B) d))),
          IsCompatible _ (orbitalDescentLeviHaar E B) μHM νM →
          ∀ (φ : SchwartzBruhat (GeneralLinear n E)),
            sigmaOrbitalIntegral σ n (B.leviEmbedding E d) νG ⇑φ =
              (μG.real (standardMaximalCompact E n) : ℂ) *
                (twistedOrbitalDescentFactor σ B d : ℂ) *
                twistedOrbitalIntegral (leviAut σ B) d νM
                  ⇑(normalizedTwistedParabolicConstantTerm E B σ φ)

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology

private theorem exists_compatible_twistedConj_of_eq
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) {δ δ' x : G} (heq : twistedConj θ x δ = δ')
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (μH : Measure (twistedCentralizer θ δ)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible _ μ μH ν) (f : G → ℂ) :
    ∃ (μH' : Measure (twistedCentralizer θ δ')) (_ : μH'.IsHaarMeasure)
      (_ : μH'.IsMulRightInvariant) (ν' : Measure (LeftQuotient (twistedCentralizer θ δ'))),
      IsCompatible _ μ μH' ν' ∧
      twistedOrbitalIntegral θ δ' ν' f = twistedOrbitalIntegral θ δ ν f := by
  subst δ'
  let e := twistedCentralizerConj θ δ x
  let μH' := Measure.map e μH
  let ν' := Measure.map (twistedOrbitQuotientConj θ δ x) ν
  let : μH'.IsHaarMeasure := e.isHaarMeasure_map μH
  let : μH'.IsMulRightInvariant := isMulRightInvariant_map e μH
  exact ⟨μH', inferInstance, inferInstance, ν',
    isCompatible_map_twistedConj θ δ x μH μH' μ rfl ν hν,
    (twistedOrbitalIntegral_map_conj θ δ x ν f).2⟩

open scoped ENNReal in
set_option linter.style.haveILetI false in
/-- Pointwise two-block descent reduces the orbital integral at a σ-regular nonelliptic
element to the orbital integral of a normalized twisted constant term, with positive factor. -/
theorem exists_levi_twistedOrbitalIntegral_of_not_sigmaElliptic
    (hDescent : TwoBlockTwistedOrbitalDescentStatement.{u, v})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ}
    (hE : IsCyclicAlgebra σ l) (hn : 0 < n) :
    letI : FiniteDimensional F E := hE.1
    letI := LocalField.FiniteExtension.valuativeRel F E
    letI := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
    ∀ [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (δ : GeneralLinear n E), IsSigmaRegular σ l δ → ¬ IsSigmaElliptic σ l δ →
      ∀ (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
        (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
        (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))),
        IsCompatible _ μG μδ νδ →
        ∀ φ : SchwartzBruhat (GeneralLinear n E),
          ∃ (k : ℕ) (hk : 0 < k) (hkn : k < n),
            let B := twoBlock n k hk hkn
            letI : MeasurableSpace (B.Levi E) := borel _
            letI : BorelSpace (B.Levi E) := ⟨rfl⟩
            ∃ (m : B.Levi F) (d : B.Levi E) (x : GeneralLinear n E),
              twistedConj (entrywiseAut σ n) x δ = B.leviEmbedding E d ∧
              IsRegularSemisimple (B.leviEmbedding F m) ∧
              (∀ i, IsRegularSemisimple (m i)) ∧
              (∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i)) ∧
              ∃ (μHM : Measure (twistedCentralizer (leviAut σ B) d))
                (_ : μHM.IsHaarMeasure) (_ : μHM.IsMulRightInvariant)
                (νM : Measure (LeftQuotient (twistedCentralizer (leviAut σ B) d))),
                IsCompatible _ (orbitalDescentLeviHaar E B) μHM νM ∧
                0 < μG.real (standardMaximalCompact E n) * twistedOrbitalDescentFactor σ B d ∧
                sigmaOrbitalIntegral σ n δ νδ ⇑φ =
                  (μG.real (standardMaximalCompact E n) : ℂ) *
                    (twistedOrbitalDescentFactor σ B d : ℂ) *
                    twistedOrbitalIntegral (leviAut σ B) d νM
                      ⇑(normalizedTwistedParabolicConstantTerm E B σ φ) := by
  let : FiniteDimensional F E := hE.1
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  intro _ _ δ hreg hell μG _ μδ hHaarδ hRightδ νδ hνδ φ
  obtain ⟨k, hk, hkn, m, d, x, hx, hm, hmreg, hnorm, hC⟩ :=
    exists_twoBlock_of_sigmaRegular_of_not_sigmaElliptic hE.pow_eq_one hn hreg hell
  let B := twoBlock n k hk hkn
  letI : MeasurableSpace (B.Levi E) := borel _
  letI : BorelSpace (B.Levi E) := ⟨rfl⟩
  let θ := (entrywiseAut σ n).toMonoidHom
  let μH : Measure (twistedCentralizer θ δ) := μδ
  let : μH.IsHaarMeasure := hHaarδ
  let : μH.IsMulRightInvariant := hRightδ
  obtain ⟨μ', hhaar, hright, ν', hν', hO⟩ :=
    exists_compatible_twistedConj_of_eq θ hx μG μH νδ hνδ ⇑φ
  let μH' : Measure (sigmaCentralizer σ n (B.leviEmbedding E d)) := μ'
  let : μH'.IsHaarMeasure := hhaar
  let : μH'.IsMulRightInvariant := hright
  let : BorelSpace (sigmaCentralizer σ n (B.leviEmbedding E d)) := Subtype.borelSpace _
  let e := twistedLeviCentralizerEquiv σ B d hC
  let μHM := Measure.map e.symm μH'
  let : μHM.IsHaarMeasure := e.symm.isHaarMeasure_map μH'
  let : μHM.IsMulRightInvariant := isMulRightInvariant_map e.symm μH'
  let H := twistedCentralizer (leviAut σ B) d
  have hclosed : IsClosed (H : Set (B.Levi E)) :=
    isClosed_twistedCentralizer (leviAut σ B)
      (continuous_pi fun i => (continuous_entrywiseAut σ (B.size i)).comp (continuous_apply i)) d
  let : LocallyCompactSpace H := hclosed.locallyCompactSpace
  let : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  let : μHM.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let μM := orbitalDescentLeviHaar E B
  let : μM.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  obtain ⟨νM, hνM⟩ := compatibleMeasureExists H hclosed μM μHM
  have hD := twistedOrbitalDescentFactor_pos_of_exactNorm hE B hm
    (cyclicNorm_leviEmbedding_eq_of_blockwise B m d hnorm)
  have hK : (standardMaximalCompact E n : Set (GeneralLinear n E)).Nonempty :=
    ⟨1, (standardMaximalCompact E n).one_mem⟩
  have hvol : 0 < μG.real (standardMaximalCompact E n) :=
    ENNReal.toReal_pos ((isOpen_standardMaximalCompact E n).measure_ne_zero μG hK)
      (isCompact_standardMaximalCompact E n).measure_lt_top.ne
  refine ⟨k, hk, hkn, m, d, x, hx, hm, hmreg, hnorm, μHM, inferInstance, inferInstance,
    νM, hνM, mul_pos hvol hD, hO.symm.trans ?_⟩
  exact hDescent F E σ l n hE k hk hkn m d hm hnorm hC μG μH' ν' hν' νM hνM φ

end Langlands.BaseChange
