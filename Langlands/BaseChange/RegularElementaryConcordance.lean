import Langlands.Analysis.Local.CompactOpenOrbitMassProof
import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.RegularElementaryOrbit
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.RegularTransferMeasures

/-! # Concordance of the regular elementary test pair -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Unramified Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.JacquetLanglands HarmonicAnalysis Matrix _root_.Polynomial MeasureTheory
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Mass

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
private theorem quotientMap_mem_compactOpen_image_iff {H : Subgroup G} {K : OpenSubgroup G}
    (x : G) :
    leftQuotientMap H x ∈ leftQuotientMap H '' (K : Set G) ↔
      ∃ c ∈ H, ∃ k ∈ K, x = c * k := by
  constructor
  · rintro ⟨k, hk, he⟩
    have hc : QuotientGroup.rightRel H k x := Quotient.exact he
    exact ⟨x * k⁻¹, (QuotientGroup.rightRel_apply).1 hc, k, hk, by simp⟩
  · rintro ⟨c, hc, k, hk, rfl⟩
    exact ⟨k, hk, (leftQuotientMap_subgroup_mul H ⟨c, hc⟩ k).symm⟩

private theorem twistedOrbitalIntegral_eq_compactOpenOrbitMass
    {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]
    (θ : Θ) (hθ : Continuous θ) (d : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (S : Set G)
    (hS : ∀ x : G, x⁻¹ * d * θ x ∈ S ↔
      ∃ c ∈ twistedCentralizer θ d, ∃ k ∈ K, x = c * k)
    (μ : Measure G) [μ.IsHaarMeasure]
    (μC : Measure (twistedCentralizer θ d)) [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ d)))
    (hν : IsCompatible (twistedCentralizer θ d) μ μC ν) :
    twistedOrbitalIntegral θ d ν (S.indicator (fun _ => (1 : ℂ))) =
      (((μ (K : Set G)).toReal / (μC {c | c.val ∈ K}).toReal : ℝ) : ℂ) := by
  classical
  let C := twistedCentralizer θ d
  have hC : IsClosed (C : Set G) := isClosed_twistedCentralizer θ hθ d
  let : BorelSpace C := Subtype.borelSpace (· ∈ C)
  let : LocallyCompactSpace C := hC.locallyCompactSpace
  let : SecondCountableTopology C := TopologicalSpace.Subtype.secondCountableTopology (C : Set G)
  let : μC.Regular := inferInstance
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hMass⟩ :=
    compactOpenOrbitMass C hC μ μC K hK ν hν
  let A := leftQuotientMap C '' (K : Set G)
  have hOrbit : twistedOrbitFunction θ d (S.indicator (fun _ => (1 : ℂ))) =
      A.indicator (fun _ => (1 : ℂ)) := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [twistedOrbitFunction_mk]
      change S.indicator (fun _ => (1 : ℂ)) (x⁻¹ * d * θ x) =
        A.indicator (fun _ => (1 : ℂ)) (leftQuotientMap C x)
      simp only [Set.indicator_apply, hS, A, quotientMap_mem_compactOpen_image_iff, C]
  change (∫ q, twistedOrbitFunction θ d (S.indicator fun _ => (1 : ℂ)) q ∂ν) = _
  rw [hOrbit]
  exact hMass

end Mass

section Diagonal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}

private theorem isRegularSemisimple_diagonalUnits {a : Fin (r + 1) → F.Carrierˣ}
    (h : Function.Injective fun i => F.canonicalTopologicalData.ord (a i : F.Carrier)) :
    IsRegularSemisimple (diagonalUnits a) := by
  change (diagonalUnits a).val.charpoly.Separable
  rw [diagonalUnits_val, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
  exact fun _ _ hij => h (congrArg F.canonicalTopologicalData.ord hij)

private theorem exists_diagonalUnits_of_diagonal_conj {a : Fin (r + 1) → F.Carrierˣ}
    (h : Function.Injective fun i => F.canonicalTopologicalData.ord (a i : F.Carrier))
    {x : GeneralLinear (r + 1) F.Carrier}
    (hx : x⁻¹ * diagonalUnits a * x = diagonalUnits a) :
    ∃ t : Fin (r + 1) → F.Carrierˣ, x = diagonalUnits t := by
  exact exists_diagonalUnits_of_strict_twistedConj F (1 : F.Carrier ≃ₐ[Padic p] F.Carrier)
    (fun _ => rfl) h (by simpa only [entrywiseAut_one_apply] using hx)

private theorem glCentralizer_diagonalUnits_eq_range {a : Fin (r + 1) → F.Carrierˣ}
    (h : Function.Injective fun i => F.canonicalTopologicalData.ord (a i : F.Carrier)) :
    glCentralizer (diagonalUnits a) = diagonalUnits.range := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := exists_diagonalUnits_of_diagonal_conj F h hx
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    have hcomm := (Commute.all t a).map
      (diagonalUnits : (Fin (r + 1) → F.Carrierˣ) →* GeneralLinear (r + 1) F.Carrier)
    change (diagonalUnits t)⁻¹ * diagonalUnits a * diagonalUnits t = diagonalUnits a
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]

end Diagonal

section Concordance

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  {l r : ℕ} (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
  (hσ : IsCyclicAlgebra σ l)
  (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
  (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)

local notation "T" => F.canonicalTopologicalData
local notation "S" => E.canonicalTopologicalData
local notation "iFE" => baseChange F.Carrier E.Carrier (r + 1)
local notation "θ" => entrywiseAut σ (r + 1)
local notation "β" => fun i : Fin (r + 1) => (l : ℤ) * ν i
local notation "φ" => (Prod.fst (regularElementaryBaseChangeTests F E σ l hσ he ν hν) :
  SchwartzBruhat (GeneralLinear (r + 1) E.Carrier))
local notation "f" => (Prod.snd (regularElementaryBaseChangeTests F E σ l hσ he ν hν) :
  SchwartzBruhat (GeneralLinear (r + 1) F.Carrier))

include hσ hν in
omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem strictAnti_scaled_order : StrictAnti β :=
  fun _ _ hij => mul_lt_mul_of_pos_left (hν hij) (by exact_mod_cast hσ.pos)

set_option maxHeartbeats 1200000 in
private theorem regularElementaryConcordanceAt_diagonal
    (a : Fin (r + 1) → E.Carrierˣ) (b : Fin (r + 1) → F.Carrierˣ)
    (ha : ∀ i, (S).ord (a i : E.Carrier) = ν i)
    (hb : ∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i)
    (hn : cyclicNorm σ l (diagonalUnits a) = iFE (diagonalUnits b)) :
    ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) φ f
      (diagonalUnits a) (diagonalUnits b) := by
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  let : IsModuleTopology F.Carrier E.Carrier := isModuleTopology_padic_extension F E
  let KF := sphericalOpenSubgroup F r
  let KE := sphericalOpenSubgroup E r
  let δ := diagonalUnits a
  let γ := diagonalUnits b
  let CF := glCentralizer γ
  let CE := sigmaCentralizer σ (r + 1) δ
  have hβ := strictAnti_scaled_order F E σ hσ ν hν
  have hbOrd : Function.Injective (fun i => (T).ord (b i : F.Carrier)) := by
    simpa only [hb] using hβ.injective
  have hReg := isRegularSemisimple_diagonalUnits F hbOrd
  have hCF : CF = diagonalUnits.range := glCentralizer_diagonalUnits_eq_range F hbOrd
  have hCE : CE = CF.map iFE := sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq hσ hReg hn
  let τ := σ.restrictScalars (Padic p)
  let SE := regularElementarySupport E τ (elementaryUpperUniformizer F E) ν
  let SF := regularElementarySupport F (1 : F.Carrier ≃ₐ[Padic p] F.Carrier)
    (T).uniformizerUnit β
  have hOrbE (x : GeneralLinear (r + 1) E.Carrier) :
      x⁻¹ * δ * θ x ∈ SE ↔ ∃ c ∈ CE, ∃ k ∈ KE, x = c * k := by
    have h := twistedConj_mem_regularElementarySupport_iff E τ (elementaryUpperUniformizer F E)
      (ord_elementaryUpperUniformizer F E he) ν hν ha x
    change x⁻¹ * δ * θ x ∈ SE ↔ _ at h
    rw [h]
    constructor
    · rintro ⟨t, k, hk, rfl⟩
      obtain ⟨d, k₀, hk₀, hd⟩ := exists_diagonal_baseChange_mul_spherical F E he t
      have hc : iFE (diagonalUnits d) ∈ CE := by
        rw [hCE, hCF]
        exact ⟨diagonalUnits d, ⟨d, rfl⟩, rfl⟩
      exact ⟨iFE (diagonalUnits d), hc, k₀ * k, KE.mul_mem hk₀ hk, by rw [hd, mul_assoc]⟩
    · rintro ⟨c, hc, k, hk, rfl⟩
      rw [hCE, hCF] at hc
      obtain ⟨_, ⟨d, rfl⟩, rfl⟩ := hc
      exact ⟨_, k, hk, by rw [baseChange_diagonalUnits]⟩
  have hOrdF : (T).ord ((T).uniformizerUnit : F.Carrier) = 1 := by
    rw [(T).uniformizerUnit_val, (T).ord_uniformizer]
  have hOrbF (x : GeneralLinear (r + 1) F.Carrier) :
      x⁻¹ * γ * x ∈ SF ↔ ∃ c ∈ CF, ∃ k ∈ KF, x = c * k := by
    rw [hCF]
    rw [show x⁻¹ * γ * x ∈ SF ↔ ∃ t : Fin (r + 1) → F.Carrierˣ,
        ∃ k ∈ KF, x = diagonalUnits t * k from by
      simpa only [entrywiseAut_one_apply] using
        twistedConj_mem_regularElementarySupport_iff F (1 : F.Carrier ≃ₐ[Padic p] F.Carrier)
          (T).uniformizerUnit hOrdF β hβ hb x]
    exact ⟨fun ⟨t, k, hk, h⟩ => ⟨diagonalUnits t, ⟨t, rfl⟩, k, hk, h⟩,
      fun ⟨_, ⟨t, rfl⟩, k, hk, h⟩ => ⟨t, k, hk, h⟩⟩
  intro μδ _ _ μγ _ _ νδ νγ hδ hγ hAssoc
  obtain ⟨x, hEq, hμ⟩ := hAssoc
  have hUpperOrder : Function.Injective (fun i =>
      (S).ord ((Units.map (algebraMap F.Carrier E.Carrier) (b i) : E.Carrierˣ) : E.Carrier)) := by
    intro i j hij
    apply hbOrd
    change (S).ord (algebraMap F.Carrier E.Carrier (b i : F.Carrier)) =
      (S).ord (algebraMap F.Carrier E.Carrier (b j : F.Carrier)) at hij
    simpa only [ord_algebraMap_of_elementary_unramified F E he] using hij
  have hx : x⁻¹ * iFE γ * x = iFE γ := by
    rw [hn] at hEq
    exact hEq
  rw [baseChange_diagonalUnits] at hx
  obtain ⟨t, ht⟩ := exists_diagonalUnits_of_diagonal_conj E hUpperOrder hx
  have hTrivial (c : CE) : x⁻¹ * c.val * x = c.val := by
    have hc : c.val ∈ CF.map iFE := hCE ▸ c.property
    rw [hCF] at hc
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hc
    rw [← hd, ht, baseChange_diagonalUnits]
    have hComm := (Commute.all t (fun i => Units.map (algebraMap F.Carrier E.Carrier) (d i))).map
      (diagonalUnits : (Fin (r + 1) → E.Carrierˣ) →* GeneralLinear (r + 1) E.Carrier)
    rw [mul_assoc, ← hComm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmeas : Measure.map Subtype.val μδ =
      Measure.map (fun c : CF => iFE c.val) μγ := by
    simpa only [hTrivial] using hμ
  have hμIntersection : μδ {c : CE | c.val ∈ KE} = μγ {c : CF | c.val ∈ KF} := by
    have hh := congrArg (fun μ : Measure (GeneralLinear (r + 1) E.Carrier) => μ (KE : Set _)) hmeas
    have hm : Measurable (fun c : CF => iFE c.val) :=
      ((continuous_baseChange_padic F E (r + 1)).comp continuous_subtype_val).measurable
    rw [Measure.map_apply measurable_subtype_coe KE.isOpen.measurableSet,
      Measure.map_apply hm KE.isOpen.measurableSet] at hh
    refine hh.trans (congrArg μγ ?_)
    ext c
    have hc : c.val ∈ diagonalUnits.range := hCF ▸ c.property
    obtain ⟨d, hd⟩ := hc
    change iFE c.val ∈ KE ↔ c.val ∈ KF
    rw [← hd, baseChange_diagonalUnits, diagonalUnits_mem_sphericalOpenSubgroup_iff E,
      diagonalUnits_mem_sphericalOpenSubgroup_iff F]
    exact forall_congr' fun i => by
      change (S).ord (algebraMap F.Carrier E.Carrier (d i : F.Carrier)) = 0 ↔ _
      rw [ord_algebraMap_of_elementary_unramified F E he]
  let : LocallyCompactSpace (GeneralLinear (r + 1) F.Carrier) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
  let : LocallyCompactSpace (GeneralLinear (r + 1) E.Carrier) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier (r + 1)
  let : SecondCountableTopology (GeneralLinear (r + 1) F.Carrier) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F.Carrier (r + 1)
  let : SecondCountableTopology (GeneralLinear (r + 1) E.Carrier) :=
    LocalFieldTopology.generalLinear_secondCountableTopology E.Carrier (r + 1)
  have hOrd := twistedOrbitalIntegral_eq_compactOpenOrbitMass (MonoidHom.id _) continuous_id
    γ KF (sphericalOpenSubgroup_isCompact F r) SF hOrbF (sphericalHaar F r) μγ νγ hγ
  have hTwist := twistedOrbitalIntegral_eq_compactOpenOrbitMass θ
    (continuous_entrywiseAut σ (r + 1)) δ KE (sphericalOpenSubgroup_isCompact E r) SE hOrbE
    (sphericalHaar E r) μδ νδ hδ
  change twistedOrbitalIntegral θ δ νδ (SE.indicator (fun _ => 1)) =
    twistedOrbitalIntegral (MonoidHom.id _) γ νγ (SF.indicator (fun _ => 1))
  rw [hTwist, hOrd, hμIntersection, sphericalHaar_self, sphericalHaar_self]

private theorem exists_ordinary_weighted_diagonal_of_ordinary_support
    (γ : GeneralLinear (r + 1) F.Carrier) (hx : ∃ x, f (x⁻¹ * γ * x) ≠ 0) :
    ∃ b : Fin (r + 1) → F.Carrierˣ, (∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i) ∧
      ∃ y, y⁻¹ * γ * y = diagonalUnits b := by
  obtain ⟨x, hx⟩ := hx
  let U := regularElementarySupport F (1 : F.Carrier ≃ₐ[Padic p] F.Carrier) (T).uniformizerUnit β
  have hmem : x⁻¹ * γ * x ∈ U := by
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨k, _, b, hb, hk⟩ := hmem
  refine ⟨b, (mem_elementaryDiagonalTuples_iff F (T).uniformizerUnit ?_ β b).1 hb,
    x * k⁻¹, ?_⟩
  · rw [(T).uniformizerUnit_val, (T).ord_uniformizer]
  · rw [entrywiseAut_one_apply] at hk
    rw [_root_.mul_inv_rev, inv_inv]
    calc
      _ = k * (x⁻¹ * γ * x) * k⁻¹ := by group
      _ = _ := by rw [← hk]; group

private theorem exists_ordinary_weighted_diagonal_of_twisted_support
    (δ : GeneralLinear (r + 1) E.Carrier) (γ : GeneralLinear (r + 1) F.Carrier)
    (hAssoc : IsNormAssociated σ l δ γ) (hReg : IsRegularSemisimple γ)
    (hx : ∃ x, φ (x⁻¹ * δ * θ x) ≠ 0) :
    ∃ b : Fin (r + 1) → F.Carrierˣ, (∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i) ∧
      ∃ y, y⁻¹ * γ * y = diagonalUnits b := by
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  obtain ⟨x, hx⟩ := hx
  let U := regularElementarySupport E (σ.restrictScalars (Padic p)) (elementaryUpperUniformizer F E) ν
  have hmem : x⁻¹ * δ * θ x ∈ U := by
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨k, _, a, ha, hk⟩ := hmem
  change k⁻¹ * diagonalUnits a * θ k = x⁻¹ * δ * θ x at hk
  have hDiag : (x * k⁻¹)⁻¹ * δ * θ (x * k⁻¹) = diagonalUnits a := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, map_inv]
    calc
      _ = k * (x⁻¹ * δ * θ x) * (θ k)⁻¹ := by group
      _ = _ := by rw [← hk]; group
  let b : Fin (r + 1) → F.Carrierˣ := fun i => Units.map (Algebra.norm F.Carrier) (a i)
  have ha' := (mem_elementaryDiagonalTuples_iff E (elementaryUpperUniformizer F E)
    (ord_elementaryUpperUniformizer F E he) ν a).1 ha
  have hb (i : Fin (r + 1)) : (T).ord (b i : F.Carrier) = (l : ℤ) * ν i := by
    change (T).ord (Algebra.norm F.Carrier (a i : E.Carrier)) = _
    rw [LocalClassField.ord_relative_norm_of_unramified F E T S he.symm, hσ.2.1, ha']
  have h := hAssoc.twistedConj hσ.pow_eq_one (x * k⁻¹) 1
  rw [hDiag, inv_one, one_mul, mul_one] at h
  obtain ⟨z, hz⟩ := h
  rw [cyclicNorm_diagonalUnits_eq hσ a] at hz
  have heq := congrArg (fun d : GeneralLinear (r + 1) E.Carrier => d.val.charpoly) hz
  have hc :
      (iFE (diagonalUnits b)).val.charpoly = (iFE γ).val.charpoly := by
    simpa only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] using heq
  have hcp : (diagonalUnits b).val.charpoly = γ.val.charpoly := by
    apply Polynomial.map_injective _ (algebraMap F.Carrier E.Carrier).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hc
  obtain ⟨y, hy⟩ := exists_matrix_conj_of_charpoly_eq_of_separable _ _ hReg hcp
  exact ⟨b, hb, y⁻¹, by simpa only [inv_inv] using (Units.ext hy :
    y * γ * y⁻¹ = diagonalUnits b)⟩

include hσ he in
private theorem exists_upper_weighted_diagonal_of_exact_norm
    (b : Fin (r + 1) → F.Carrierˣ) (hb : ∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i)
    (hβ : StrictAnti β) (δ : GeneralLinear (r + 1) E.Carrier)
    (hn : cyclicNorm σ l δ = iFE (diagonalUnits b)) :
    ∃ a : Fin (r + 1) → E.Carrierˣ, δ = diagonalUnits a ∧
      ∀ i, (S).ord (a i : E.Carrier) = ν i := by
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  have h := entrywiseAut_cyclicNorm σ l δ
  rw [hn, entrywiseAut_baseChange, hσ.pow_eq_one, entrywiseAut_one_apply] at h
  rw [baseChange_diagonalUnits] at h
  have hOrdMap :
      Function.Injective (fun i => (S).ord
        ((Units.map (algebraMap F.Carrier E.Carrier) (b i) : E.Carrierˣ) : E.Carrier)) := by
    intro i j hij
    apply hβ.injective
    change (S).ord (algebraMap F.Carrier E.Carrier (b i : F.Carrier)) =
      (S).ord (algebraMap F.Carrier E.Carrier (b j : F.Carrier)) at hij
    simpa only [ord_algebraMap_of_elementary_unramified F E he, hb] using hij
  obtain ⟨a, ha⟩ := exists_diagonalUnits_of_diagonal_conj E hOrdMap h.symm
  refine ⟨a, ha, fun i => ?_⟩
  rw [ha, cyclicNorm_diagonalUnits_eq hσ] at hn
  have hi := congrArg (fun d : GeneralLinear (r + 1) E.Carrier => d i i) hn
  rw [baseChange_diagonalUnits, baseChange_diagonalUnits, diagonalUnits_val,
    diagonalUnits_val, diagonal_apply_eq, diagonal_apply_eq] at hi
  have hi' : Algebra.norm F.Carrier (a i : E.Carrier) = (b i : F.Carrier) :=
    (algebraMap F.Carrier E.Carrier).injective hi
  have ho := congrArg (T).ord hi'
  rw [LocalClassField.ord_relative_norm_of_unramified F E T S he.symm, hσ.2.1, hb] at ho
  exact mul_left_cancel₀ (by exact_mod_cast hσ.pos.ne') ho

include hσ he in
private theorem isNorm_of_ordinary_weighted_diagonal (b : Fin (r + 1) → F.Carrierˣ)
    (hb : ∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i) :
    IsNorm σ l (diagonalUnits b) := by
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  have hin (i : Fin (r + 1)) : ∃ a : E.Carrierˣ, Units.map (Algebra.norm F.Carrier) a = b i := by
    apply (LocalClassField.unramifiedNormMembership p F E T S he.symm (b i)).2
    rw [hσ.2.1, hb]
    exact dvd_mul_right _ _
  choose a ha using hin
  refine ⟨diagonalUnits a, 1, ?_⟩
  rw [inv_one, one_mul, mul_one, cyclicNorm_diagonalUnits_eq hσ]
  simp only [ha]

private theorem orbitalIntegral_zero_of_orbitFunction_zero
    {G : Type*} [Group G] {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]
    (ϑ : Θ) (d : G) [MeasurableSpace (LeftQuotient (twistedCentralizer ϑ d))]
    (η : Measure (LeftQuotient (twistedCentralizer ϑ d))) (g : G → ℂ)
    (h : ∀ x, g (x⁻¹ * d * ϑ x) = 0) : twistedOrbitalIntegral ϑ d η g = 0 := by
  have hz : twistedOrbitFunction ϑ d g = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact h x
  simp only [twistedOrbitalIntegral, hz, Pi.zero_apply, integral_zero]

/-- The regular Labesse pair is concordant with the two spherical mass-one
ambient Haar measures. -/
theorem regularElementaryConcordance :
    AreConcordant σ l (sphericalHaar F r) (sphericalHaar E r) φ f := by
  classical
  constructor
  · intro γ _ hNot μγ _ _ νγ hγ
    apply orbitalIntegral_zero_of_orbitFunction_zero (MonoidHom.id _) γ νγ f
    intro x
    by_contra hx
    obtain ⟨b, hb, y, hy⟩ := exists_ordinary_weighted_diagonal_of_ordinary_support
      F E σ hσ he ν hν γ ⟨x, hx⟩
    obtain ⟨δ, hδ⟩ := isNorm_of_ordinary_weighted_diagonal F E σ hσ he ν b hb
    apply hNot
    refine ⟨δ, ?_⟩
    rw [← hy] at hδ
    simpa only [inv_one, one_mul, mul_one, map_one, inv_inv, mul_inv_cancel_left, mul_assoc,
      mul_inv_cancel] using hδ.twistedConj hσ.pow_eq_one 1 y⁻¹
  · intro δ γ hAssoc hReg
    by_cases ht : ∃ b : Fin (r + 1) → F.Carrierˣ,
        (∀ i, (T).ord (b i : F.Carrier) = (l : ℤ) * ν i) ∧ ∃ y, y⁻¹ * γ * y = diagonalUnits b
    · obtain ⟨b, hb, y, hy⟩ := ht
      apply concordAt_of_conj_of_cyclicNorm_eq hσ.pow_eq_one
        (continuous_baseChange_padic F E (r + 1)).measurable δ γ y
      intro d hn
      rw [hy] at hn ⊢
      obtain ⟨a, ha, ha'⟩ := exists_upper_weighted_diagonal_of_exact_norm F E σ hσ he ν b hb
        (strictAnti_scaled_order F E σ hσ ν hν) d hn
      rw [ha] at hn ⊢
      exact regularElementaryConcordanceAt_diagonal F E σ hσ he ν hν a b ha' hb hn
    · intro μδ _ _ μγ _ _ νδ νγ _ _ _
      have hF : orbitalIntegral γ νγ f = 0 := by
        apply orbitalIntegral_zero_of_orbitFunction_zero (MonoidHom.id _) γ νγ f
        intro x
        by_contra hx
        exact ht (exists_ordinary_weighted_diagonal_of_ordinary_support F E σ hσ he ν hν γ ⟨x, hx⟩)
      have hE : sigmaOrbitalIntegral σ (r + 1) δ νδ φ = 0 := by
        apply orbitalIntegral_zero_of_orbitFunction_zero θ δ νδ φ
        intro x
        by_contra hx
        exact ht (exists_ordinary_weighted_diagonal_of_twisted_support F E σ hσ he ν hν
          δ γ hAssoc hReg ⟨x, hx⟩)
      exact hE.trans hF.symm

end Concordance

def RegularElementaryConcordanceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν),
    let tests := regularElementaryBaseChangeTests F E σ l hσ he ν hν
    AreConcordant σ l (sphericalHaar F r) (sphericalHaar E r) ⇑tests.1 ⇑tests.2

theorem regularElementaryConcordanceStatement : RegularElementaryConcordanceStatement.{u,v} := by
  intro p _ F E _ _ σ l r hσ he ν hν
  exact regularElementaryConcordance F E σ hσ he ν hν

end Langlands.BaseChange
