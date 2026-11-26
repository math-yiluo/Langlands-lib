import Langlands.BaseChange.ConcordantIntegrableIntegralEqualityStatement
import Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwardsStatement
import Langlands.BaseChange.TwistedWeylHaarLocalPushforwardsStatement
import Langlands.BaseChange.RegularSetOpenConullStatement
import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.BaseChange.WeylTorusNormImage
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Concordant integrals from the two Weyl decompositions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration Langlands.JacquetLanglands Langlands.TraceFormula
open scoped ENNReal NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

namespace WeylTorus

section Representatives

variable {F : Type*} [Field F] {n : ℕ}

/-- Rational conjugacy of tori is reflexive. -/
theorem isConjugate_refl (T : WeylTorus F n) : T.IsConjugate T := by
  refine ⟨1, ?_⟩
  ext x
  simp [Subgroup.mem_map]

/-- Rational conjugacy of tori is symmetric. -/
theorem IsConjugate.symm {T U : WeylTorus F n} (h : T.IsConjugate U) : U.IsConjugate T := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨x, hx, by group⟩

/-- Rational conjugacy of tori is transitive. -/
theorem IsConjugate.trans {T U V : WeylTorus F n} (h : T.IsConjugate U)
    (h' : U.IsConjugate V) : T.IsConjugate V := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  refine ⟨g' * g, ?_⟩
  rw [← hg', ← hg, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Rational conjugacy of the torus subgroups as a setoid. -/
def conjugacySetoid (F : Type*) [Field F] (n : ℕ) : Setoid (WeylTorus F n) where
  r := IsConjugate
  iseqv := ⟨isConjugate_refl, IsConjugate.symm, IsConjugate.trans⟩

/-- Every rank has a set of representatives of the rational conjugacy classes of tori. -/
theorem exists_isRepresentativeSet (F : Type*) [Field F] (n : ℕ) :
    ∃ S : Set (WeylTorus F n), IsRepresentativeSet S := by
  let s := conjugacySetoid F n
  refine ⟨Set.range (fun c : Quotient s => c.out), fun T => ?_⟩
  refine ⟨(Quotient.mk s T).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact Setoid.symm (Quotient.mk_out (s := s) T)
  · rintro U ⟨⟨c, rfl⟩, hU⟩
    have hc : c = Quotient.mk s T := by
      rw [← Quotient.out_eq c]
      exact Quotient.sound (Setoid.symm hU)
    rw [hc]

end Representatives

end WeylTorus

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- Measures on two equal subgroups and their coset spaces correspond, with the same
compatibility, the same pushforward to the group and the same coset integrals. -/
theorem exists_subgroup_transport {K K' : Subgroup G} (h : K = K') (μG : Measure G)
    (μ' : Measure K') [μ'.IsHaarMeasure] [μ'.IsMulRightInvariant]
    (ν' : Measure (LeftQuotient K')) (hc : IsCompatible K' μG μ' ν') :
    ∃ (μ : Measure K) (_ : μ.IsHaarMeasure) (_ : μ.IsMulRightInvariant)
      (ν : Measure (LeftQuotient K)),
      IsCompatible K μG μ ν ∧ Measure.map Subtype.val μ = Measure.map Subtype.val μ' ∧
      ∀ (g : G → ℂ) (hg : ∀ k : K, ∀ x, g (k.val * x) = g x)
        (hg' : ∀ k : K', ∀ x, g (k.val * x) = g x),
        ∫ q, descend K g hg q ∂ν = ∫ q, descend K' g hg' q ∂ν' := by
  subst h
  exact ⟨μ', inferInstance, inferInstance, ν', hc, rfl, fun _ _ _ => rfl⟩

end Transport

section TorusMeasures

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- Weil's theorem for a closed subgroup of a second countable group, with right Haar
measures. -/
private theorem exists_compatible_of_closed {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μG : Measure G) (μH : Measure H)
    [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] : CompatibleMeasureExists H μG μH := by
  let _ : LocallyCompactSpace H := hH.locallyCompactSpace
  let _ : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology ↥(H : Set G))
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
  exact compatibleMeasureExists H hH μG μH

namespace WeylTorus

/-- The rational points of a torus form a closed subgroup, a centralizer. -/
theorem isClosed_val [T2Space (GeneralLinear n F)] (T : WeylTorus F n) :
    IsClosed (T.val : Set (GeneralLinear n F)) := by
  obtain ⟨γ, -, hT⟩ := T.property
  rw [← hT, glCentralizer_eq_centralizer]
  exact Set.isClosed_centralizer _

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [BorelSpace (GeneralLinear n F)] in
/-- A left Haar measure on the commutative group of rational torus points is right
invariant. -/
theorem isMulRightInvariant_of_isHaarMeasure (T : WeylTorus F n) (μT : Measure T.val)
    [μT.IsHaarMeasure] : μT.IsMulRightInvariant :=
  ⟨fun t => by
    have heq : (· * t) = (t * ·) := funext fun s => Subtype.ext (T.val_commute s t).eq
    rw [heq, map_mul_left_eq_self]⟩

/-- A torus has a Haar measure with a compatible quotient measure for any Haar measure on
`GL_n(F)`. -/
theorem exists_ordinaryMeasures (T : WeylTorus F n)
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure] :
    ∃ (μT : Measure T.val) (_ : μT.IsHaarMeasure) (_ : μT.IsMulRightInvariant)
      (ν : Measure (LeftQuotient T.val)), IsCompatible T.val μF μT ν := by
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ := LocalFieldTopology.generalLinear_secondCountableTopology F n
  have hclosed := T.isClosed_val
  let _ : LocallyCompactSpace T.val := hclosed.locallyCompactSpace
  have : μF.IsMulRightInvariant := generalLinear_haar_rightInvariant F n μF
  let μT : Measure T.val := Measure.haar
  have hright : μT.IsMulRightInvariant := T.isMulRightInvariant_of_isHaarMeasure μT
  obtain ⟨ν, hν⟩ := exists_compatible_of_closed T.val hclosed μF μT
  exact ⟨μT, inferInstance, hright, ν, hν⟩

variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l : ℕ}
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- The base change of a torus has a Haar measure transported from a given Haar measure on
the rational points, and a compatible quotient measure for any Haar measure on
`GL_n(E)`. -/
theorem exists_twistedMeasures (hσ : IsCyclicAlgebra σ l) (T : WeylTorus F n)
    (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
    (μT : Measure T.val) (hμT : μT.IsHaarMeasure) :
    ∃ (μH : Measure (T.val.map (baseChange F E n))) (_ : μH.IsHaarMeasure)
      (_ : μH.IsMulRightInvariant) (ν : Measure (LeftQuotient (T.val.map (baseChange F E n)))),
      Measure.map Subtype.val μH = Measure.map (fun t : T.val => baseChange F E n t.val) μT ∧
      IsCompatible (T.val.map (baseChange F E n)) μE μH ν := by
  let _ := hμT
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.secondCountableTopology F
  let _ : Module.Finite F E := hσ.1
  let _ : IsReduced E := hσ.2.2.1
  let _ : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hE_sep, hE_compact, hE_countable⟩ := finiteAlgebraTopology F E
  let _ : T2Space E := hE_sep
  let _ : LocallyCompactSpace E := hE_compact
  let _ : SecondCountableTopology E := hE_countable
  let _ := generalLinear_t2Space_of_finite F E n
  let _ := generalLinear_locallyCompactSpace_of_finite F E n
  let _ : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  have : μE.IsMulRightInvariant := generalLinear_haar_rightInvariant E n μE
  have : μT.IsMulRightInvariant := T.isMulRightInvariant_of_isHaarMeasure μT
  let H := T.val.map (baseChange F E n)
  have hemb := hσ.isClosedEmbedding_baseChange n
  have hclosed : IsClosed (H : Set (GeneralLinear n E)) := by
    rw [Subgroup.coe_map]
    exact hemb.isClosedMap _ T.isClosed_val
  let e0 := T.val.equivMapOfInjective (baseChange F E n) hemb.injective
  have he0 (x : T.val) : (e0 x : GeneralLinear n E) = baseChange F E n x.val :=
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let e : T.val ≃ₜ* H :=
    { e0 with
      continuous_toFun := by
        change Continuous fun x : T.val => e0 x
        exact (hemb.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := by
        have h1 : Continuous (fun y : H => baseChange F E n (e0.symm y).val) := by
          refine continuous_subtype_val.congr fun y => ?_
          rw [← he0, e0.apply_symm_apply]
        exact (hemb.isEmbedding.continuous_iff.2 h1).subtype_mk _ }
  have he (x : T.val) : (e x : GeneralLinear n E) = baseChange F E n x.val := he0 x
  let μH : Measure H := Measure.map e μT
  have hHaar : μH.IsHaarMeasure := e.isHaarMeasure_map μT
  have hright : μH.IsMulRightInvariant := isMulRightInvariant_map e μT
  obtain ⟨ν, hν⟩ := exists_compatible_of_closed H hclosed μE μH
  refine ⟨μH, hHaar, hright, ν, ?_, hν⟩
  rw [show μH = Measure.map e μT from rfl,
    Measure.map_map continuous_subtype_val.measurable (map_continuous e).measurable]
  congr 1

end WeylTorus

end TorusMeasures

section TermComparison

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

namespace WeylTorus

/-- The inner integral of the ordinary Weyl decomposition at a regular point is an
orbital integral there, for transported centralizer and quotient measures. -/
theorem exists_orbitalIntegral_eq (T : WeylTorus F n) (μF : Measure (GeneralLinear n F))
    (μT : Measure T.val) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (νT : Measure (LeftQuotient T.val)) (hνT : IsCompatible T.val μF μT νT)
    (t : T.regularPoints) :
    ∃ (μγ : Measure (glCentralizer t.val.val)) (_ : μγ.IsHaarMeasure)
      (_ : μγ.IsMulRightInvariant) (νγ : Measure (LeftQuotient (glCentralizer t.val.val))),
      IsCompatible (glCentralizer t.val.val) μF μγ νγ ∧
      Measure.map Subtype.val μγ = Measure.map Subtype.val μT ∧
      ∀ f : GeneralLinear n F → ℂ,
        orbitalIntegral t.val.val νγ f = ∫ q, f (T.ordinaryOrbitMap (q, t)) ∂νT := by
  obtain ⟨μγ, h1, h2, νγ, hc, hmap, hint⟩ :=
    exists_subgroup_transport (T.glCentralizer_eq_of_regularPoint t) μF μT νT hνT
  refine ⟨μγ, h1, h2, νγ, hc, hmap, fun f => ?_⟩
  have hg' (k : T.val) (x : GeneralLinear n F) :
      f ((k.val * x)⁻¹ * t.val.val * (k.val * x)) = f (x⁻¹ * t.val.val * x) := by
    have hk : k.val ∈ glCentralizer t.val.val := by
      rw [T.glCentralizer_eq_of_regularPoint t]
      exact k.property
    exact congrArg f (twistedConj_left_mul (MonoidHom.id _) t.val.val ⟨k.val, hk⟩ x)
  rw [orbitalIntegral, twistedOrbitalIntegral]
  refine (hint (fun x => f (x⁻¹ * t.val.val * x)) _ hg').trans ?_
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l : ℕ}
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

omit [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)] in
/-- The inner integral of the twisted Weyl decomposition at a regular norm point is the
σ-orbital integral at its lift, for transported centralizer and quotient measures. -/
theorem exists_sigmaOrbitalIntegral_eq (hσ : IsCyclicAlgebra σ l) (T : WeylTorus F n)
    (lift : T.regularNormPoints σ l → T.points E)
    (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)
    (μE : Measure (GeneralLinear n E))
    (μH : Measure (T.val.map (baseChange F E n))) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (νH : Measure (LeftQuotient (T.val.map (baseChange F E n))))
    (hνH : IsCompatible (T.val.map (baseChange F E n)) μE μH νH)
    (t : T.regularNormPoints σ l) :
    ∃ (μδ : Measure (sigmaCentralizer σ n (lift t).val)) (_ : μδ.IsHaarMeasure)
      (_ : μδ.IsMulRightInvariant)
      (νδ : Measure (LeftQuotient (sigmaCentralizer σ n (lift t).val))),
      IsCompatible (sigmaCentralizer σ n (lift t).val) μE μδ νδ ∧
      Measure.map Subtype.val μδ = Measure.map Subtype.val μH ∧
      ∀ φ : GeneralLinear n E → ℂ,
        sigmaOrbitalIntegral σ n (lift t).val νδ φ =
          ∫ q, φ (T.twistedOrbitMap hσ lift hlift (q, t)) ∂νH := by
  have hcent : sigmaCentralizer σ n (lift t).val = T.val.map (baseChange F E n) := by
    rw [sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq hσ t.property.1 (hlift t),
      T.glCentralizer_eq_of_regularPoint ⟨t.val, t.property.1⟩]
  obtain ⟨μδ, h1, h2, νδ, hc, hmap, hint⟩ := exists_subgroup_transport hcent μE μH νH hνH
  refine ⟨μδ, h1, h2, νδ, hc, hmap, fun φ => ?_⟩
  have hg' (k : T.val.map (baseChange F E n)) (x : GeneralLinear n E) :
      φ ((k.val * x)⁻¹ * (lift t).val * entrywiseAut σ n (k.val * x)) =
        φ (x⁻¹ * (lift t).val * entrywiseAut σ n x) := by
    have hk : k.val ∈ sigmaCentralizer σ n (lift t).val := by
      rw [hcent]
      exact k.property
    exact congrArg φ (twistedConj_left_mul (entrywiseAut σ n) (lift t).val ⟨k.val, hk⟩ x)
  rw [sigmaOrbitalIntegral, twistedOrbitalIntegral]
  refine (hint (fun x => φ (x⁻¹ * (lift t).val * entrywiseAut σ n x)) _ hg').trans ?_
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- For concordant `φ` and `f`, the torus terms of the twisted and ordinary Weyl
decompositions agree. -/
theorem twistedTerm_eq_ordinaryTerm (hσ : IsCyclicAlgebra σ l) (T : WeylTorus F n)
    (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n E))
    (μT : Measure T.val) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (νT : Measure (LeftQuotient T.val)) (hνT : IsCompatible T.val μF μT νT)
    (μH : Measure (T.val.map (baseChange F E n))) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (νH : Measure (LeftQuotient (T.val.map (baseChange F E n))))
    (hmapH : Measure.map Subtype.val μH =
      Measure.map (fun t : T.val => baseChange F E n t.val) μT)
    (hνH : IsCompatible (T.val.map (baseChange F E n)) μE μH νH)
    (hreg : MeasurableSet T.regularPoints) (hnorm : MeasurableSet (T.regularNormPoints σ l))
    (lift : T.regularNormPoints σ l → T.points E)
    (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)
    (φ : GeneralLinear n E → ℂ) (f : GeneralLinear n F → ℂ)
    (hφf : AreConcordant σ l μF μE φ f) :
    ∫ t, T.twistedOrbitIntegrand hσ lift hlift νH
        (fun t => T.discriminantWeight ⟨t.val, t.property.1⟩) φ t ∂(μT.comap Subtype.val) =
      ∫ t, T.ordinaryOrbitIntegrand νT T.discriminantWeight f t ∂(μT.comap Subtype.val) := by
  classical
  have hcont : Continuous (baseChange F E n) :=
    SigmaLiftCharacterIdentity.continuous_baseChange
  have hA (t : T.regularNormPoints σ l) :
      ∫ q, φ (T.twistedOrbitMap hσ lift hlift (q, t)) ∂νH =
        ∫ q, f (T.ordinaryOrbitMap (q, ⟨t.val, t.property.1⟩)) ∂νT := by
    obtain ⟨μδ, h1, h2, νδ, hcδ, hmapδ, hδ⟩ :=
      T.exists_sigmaOrbitalIntegral_eq hσ lift hlift μE μH νH hνH t
    obtain ⟨μγ, h3, h4, νγ, hcγ, hmapγ, hγ⟩ :=
      T.exists_orbitalIntegral_eq μF μT νT hνT ⟨t.val, t.property.1⟩
    have hN : (1 : GeneralLinear n E)⁻¹ * cyclicNorm σ l (lift t).val * 1 =
        baseChange F E n t.val.val := by
      rw [inv_one, one_mul, mul_one, hlift t]
    have hassoc : IsAssociatedMeasure σ l (lift t).val t.val.val μδ μγ := by
      refine ⟨1, hN, ?_⟩
      have hl : (fun c : sigmaCentralizer σ n (lift t).val =>
          (1 : GeneralLinear n E)⁻¹ * (c : GeneralLinear n E) * 1) = Subtype.val := by
        funext c
        simp
      have hr : (fun s : glCentralizer t.val.val => baseChange F E n (s : GeneralLinear n F)) =
          baseChange F E n ∘ Subtype.val := rfl
      rw [hl, hmapδ, hmapH, hr, ← Measure.map_map hcont.measurable
        continuous_subtype_val.measurable, hmapγ,
        Measure.map_map hcont.measurable continuous_subtype_val.measurable]
      rfl
    have h := hφf.2 (lift t).val t.val.val ⟨1, hN⟩ t.property.1 μδ μγ νδ νγ hcδ hcγ hassoc
    rw [← hδ φ, ← hγ f]
    exact h
  have hB (t : T.regularPoints) (ht : t.val ∉ T.normImage σ l) :
      ∫ q, f (T.ordinaryOrbitMap (q, t)) ∂νT = 0 := by
    obtain ⟨μγ, h3, h4, νγ, hcγ, -, hγ⟩ := T.exists_orbitalIntegral_eq μF μT νT hνT t
    have hnot : ¬ IsNorm σ l t.val.val := fun h =>
      ht ((T.mem_normImage_iff_isNorm hσ t.property).2 h)
    rw [← hγ f]
    exact hφf.1 t.val.val t.property hnot μγ νγ hcγ
  let G₁ : T.val → ℂ := fun x =>
    if h : x ∈ T.regularPoints then
      T.ordinaryOrbitIntegrand νT T.discriminantWeight f ⟨x, h⟩
    else 0
  let G₂ : T.val → ℂ := fun x =>
    if h : x ∈ T.regularNormPoints σ l then
      T.twistedOrbitIntegrand hσ lift hlift νH
        (fun t => T.discriminantWeight ⟨t.val, t.property.1⟩) φ ⟨x, h⟩
    else 0
  have h1 : ∫ t, T.ordinaryOrbitIntegrand νT T.discriminantWeight f t ∂(μT.comap Subtype.val) =
      ∫ x in T.regularPoints, G₁ x ∂μT := by
    rw [← integral_subtype_comap hreg]
    congr 1
    funext t
    simp only [G₁, dite_eq_left t.property]
  have h2 : ∫ t, T.twistedOrbitIntegrand hσ lift hlift νH
        (fun t => T.discriminantWeight ⟨t.val, t.property.1⟩) φ t ∂(μT.comap Subtype.val) =
      ∫ x in T.regularNormPoints σ l, G₂ x ∂μT := by
    rw [← integral_subtype_comap hnorm]
    congr 1
    funext t
    simp only [G₂, dite_eq_left t.property]
  rw [h1, h2, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hreg Set.inter_subset_left]
  · refine setIntegral_congr_fun hnorm fun x hx => ?_
    simp only [G₁, G₂, dite_eq_left hx, dite_eq_left hx.1, twistedOrbitIntegrand, ordinaryOrbitIntegrand]
    rw [hA ⟨x, hx⟩]
  · intro x hx
    simp only [G₁, dite_eq_left hx.1, ordinaryOrbitIntegrand]
    rw [hB ⟨x, hx.1⟩ (fun h => hx.2 ⟨hx.1, h⟩)]
    simp

end WeylTorus

end TermComparison

section Reduction

/-- The comparison of the integrals of integrable concordant functions follows from the
local Haar pushforward identities of the ordinary and twisted Weyl maps and from the
openness and Haar conullity of the regular semisimple and σ-regular sets. -/
def ConcordantIntegralComparisonReductionStatement.{u, v} : Prop :=
  OrdinaryWeylHaarLocalPushforwardsStatement.{u} →
  TwistedWeylHaarLocalPushforwardsStatement.{u, v} →
  RegularSemisimpleOpenConullStatement.{u} →
  SigmaRegularOpenConullStatement.{u, v} →
  ConcordantIntegrableIntegralEqualityStatement.{u, v}

/-- The conull premise for the Borel σ-algebra applied to a Borel instance. -/
private theorem measure_not_regularSemisimple_eq_zero.{u}
    (hreg : RegularSemisimpleOpenConullStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ) [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure] :
    μ {g | ¬ IsRegularSemisimple g} = 0 := by
  have h := BorelSpace.measurable_eq (α := GeneralLinear n F)
  subst h
  exact (hreg F n).2 μ

/-- The σ-regular conull premise applied to a Borel instance. -/
private theorem measure_not_sigmaRegular_eq_zero.{u, v}
    (hreg : SigmaRegularOpenConullStatement.{u, v})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] :
    μ {d | ¬ IsSigmaRegular σ l d} = 0 := by
  have h := BorelSpace.measurable_eq (α := GeneralLinear n E)
  subst h
  exact (hreg F E σ l n hσ).2 μ

/-- Proof of `ConcordantIntegralComparisonReductionStatement`. -/
theorem concordantIntegralComparisonReduction.{u, v} :
    ConcordantIntegralComparisonReductionStatement.{u, v} := by
  intro hord htw hreg hsreg F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _ φ f hφ hf hφf
  classical
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ := LocalFieldTopology.secondCountableTopology F
  let _ : Module.Finite F E := hσ.1
  obtain ⟨hE_sep, hE_compact, hE_countable⟩ := finiteAlgebraTopology F E
  let _ : T2Space E := hE_sep
  let _ : LocallyCompactSpace E := hE_compact
  let _ : SecondCountableTopology E := hE_countable
  let _ := generalLinear_t2Space_of_finite F E n
  let _ := generalLinear_locallyCompactSpace_of_finite F E n
  let _ : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  obtain ⟨S, hS⟩ := WeylTorus.exists_isRepresentativeSet F n
  choose μT hμTH hμTR νT hνT using fun T : WeylTorus F n => T.exists_ordinaryMeasures μF
  choose μH hμHH hμHR νH hmapH hνH using
    fun T : WeylTorus F n => T.exists_twistedMeasures hσ μE (μT T) (hμTH T)
  have hregOpen : IsOpen {g : GeneralLinear n F | IsRegularSemisimple g} := (hreg F n).1
  have hregT (T : WeylTorus F n) : MeasurableSet T.regularPoints :=
    (hregOpen.preimage continuous_subtype_val).measurableSet
  have hordT (T : WeylTorus F n) : T.HasOrdinaryLocalPushforwards μF
      (T.weightedOrdinaryOrbitMeasure (νT T) ((μT T).comap Subtype.val)
        T.discriminantWeight) := by
    have := hμTH T
    have := hμTR T
    exact hord F n μF T (μT T) (νT T) (hνT T)
  have htwT : ∀ T : WeylTorus F n, MeasurableSet (T.regularNormPoints σ l) ∧
      ∃ (lift : T.regularNormPoints σ l → T.points E)
        (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val),
        T.HasTwistedLocalPushforwards hσ lift hlift μE
          (T.weightedTwistedOrbitMeasure σ l (νH T) ((μT T).comap Subtype.val)
            (fun t => T.discriminantWeight ⟨t.val, t.property.1⟩)) := fun T => by
    have := hμTH T
    have := hμHH T
    have := hμHR T
    exact htw F E σ l n hσ μE T (μT T) (μH T) (νH T) (hmapH T) (hνH T)
  choose hnormT lift hlift hlocT using htwT
  have hμTσ (T : WeylTorus F n) : SigmaFinite (μT T) := by
    have := hμTH T
    let _ : LocallyCompactSpace T.val := T.isClosed_val.locallyCompactSpace
    let _ : SecondCountableTopology T.val :=
      inferInstanceAs (SecondCountableTopology ↥(T.val : Set (GeneralLinear n F)))
    infer_instance
  have hνTSF (T : WeylTorus F n) : SFinite (νT T) := by
    let _ := leftQuotient_locallyCompactSpace T.val
    let _ : SecondCountableTopology (LeftQuotient T.val) :=
      _root_.Topology.IsOpenQuotientMap.secondCountableTopology
        (leftQuotient_isOpenQuotientMap T.val)
    have := (hνT T).regular
    infer_instance
  have hνHSF (T : WeylTorus F n) : SFinite (νH T) := by
    let _ := leftQuotient_locallyCompactSpace (T.val.map (baseChange F E n))
    let _ : SecondCountableTopology (LeftQuotient (T.val.map (baseChange F E n))) :=
      _root_.Topology.IsOpenQuotientMap.secondCountableTopology
        (leftQuotient_isOpenQuotientMap _)
    have := (hνH T).regular
    infer_instance
  have hτSF (T : WeylTorus F n) : SFinite ((μT T).comap (Subtype.val : T.regularPoints → _)) := by
    have := hμTσ T
    have : SigmaFinite ((μT T).comap (Subtype.val : T.regularPoints → _)) :=
      SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
        (by rw [map_comap_subtype_coe (hregT T)]; infer_instance)
    infer_instance
  have hτ'SF (T : WeylTorus F n) :
      SFinite ((μT T).comap (Subtype.val : T.regularNormPoints σ l → _)) := by
    have := hμTσ T
    have : SigmaFinite ((μT T).comap (Subtype.val : T.regularNormPoints σ l → _)) :=
      SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
        (by rw [map_comap_subtype_coe (hnormT T)]; infer_instance)
    infer_instance
  have hne (T : WeylTorus F n) (t : T.regularPoints) : weylDiscriminant t.val.val ≠ 0 := by
    obtain ⟨hunit, hdet⟩ := det_ordinaryWeylDifferential t.val.val t.property
    exact hdet ▸ hunit.ne_zero
  have hwm (T : WeylTorus F n) : Measurable T.discriminantWeight :=
    (T.isLocallyConstant_discriminantWeight (hne T)).continuous.measurable
  have hw'm (T : WeylTorus F n) :
      Measurable (fun t : T.regularNormPoints σ l => T.discriminantWeight ⟨t.val, t.property.1⟩) :=
    (T.isLocallyConstant_discriminantWeight (hne T)).continuous.measurable.comp
      (continuous_subtype_val.subtype_mk _).measurable
  obtain ⟨-, -, -, hEqF⟩ := ordinaryWeylIntegralDecomposition F n μF S hS
    (fun T => νT T.val) (fun T => (μT T.val).comap Subtype.val)
    (fun T => T.val.discriminantWeight) (fun T => hνTSF T.val) (fun T => hτSF T.val)
    (fun T => hwm T.val)
    (fun T => Filter.Eventually.of_forall fun t => T.val.discriminantWeight_pos t (hne T.val t))
    (fun T => hordT T.val) f hf.integrableOn
  obtain ⟨-, -, -, hEqE⟩ := twistedWeylIntegralDecomposition F E σ l n hσ μE S hS
    (fun T => lift T.val) (fun T => hlift T.val) (fun T => νH T.val)
    (fun T => (μT T.val).comap Subtype.val)
    (fun T t => T.val.discriminantWeight ⟨t.val, t.property.1⟩)
    (fun T => hνHSF T.val) (fun T => hτ'SF T.val) (fun T => hw'm T.val)
    (fun T => Filter.Eventually.of_forall fun t =>
      T.val.discriminantWeight_pos _ (hne T.val ⟨t.val, t.property.1⟩))
    (fun T => hlocT T.val) φ hφ.integrableOn
  have hFullF : ∫ γ, f γ ∂μF = ∫ γ in {g | IsRegularSemisimple g}, f γ ∂μF := by
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
    have hnull := measure_not_regularSemisimple_eq_zero hreg F n μF
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with g hg hg'
    exact absurd (not_not.1 hg) hg'
  have hFullE : ∫ δ, φ δ ∂μE = ∫ δ in {d | IsSigmaRegular σ l d}, φ δ ∂μE := by
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
    have hnull := measure_not_sigmaRegular_eq_zero hsreg F E σ l n hσ μE
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with g hg hg'
    exact absurd (not_not.1 hg) hg'
  rw [hFullE, hFullF, hEqE, hEqF]
  refine tsum_congr fun T => ?_
  have := hμTH T.val
  have := hμTR T.val
  have := hμHH T.val
  have := hμHR T.val
  exact T.val.twistedTerm_eq_ordinaryTerm hσ μF μE (μT T.val) (νT T.val) (hνT T.val)
    (μH T.val) (νH T.val) (hmapH T.val) (hνH T.val) (hregT T.val) (hnormT T.val)
    (lift T.val) (hlift T.val) φ f hφf

end Reduction

end Langlands.BaseChange
