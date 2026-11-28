import Langlands.BaseChange.TwistedCharacter.SemisimpleLocalReduction
import Langlands.BaseChange.TwistedCharacter.SemisimpleFixedAlgebra
import Langlands.BaseChange.TwistedCharacter.SemisimpleDescentDistribution
import Langlands.BaseChange.TwistedCharacter.SemisimpleClopenDomain
import Langlands.BaseChange.TwistedCharacter.TranslatedCosetCharacter
import Langlands.HarmonicAnalysis.Distribution.ClopenCutoff
import Langlands.BaseChange.TwistedCharacter.MatrixHaarChart

/-! # Semisimple descent of characters on the cyclic matrix extensions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function _root_.Topology
open scoped SemidirectProduct

section Algebra

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]
  {l n : ℕ} [NeZero l] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1}

local notation "G" => GeneralLinear n E
local notation "H" => CyclicGLSemidirect σ hσ n

/-- The actual algebra automorphism of the matrix Lie algebra induced by a cyclic element. -/
def cyclicAdjointAlgEquiv (s : H) : Matrix (Fin n) (Fin n) E ≃ₐ[F] Matrix (Fin n) (Fin n) E :=
  twistedAdjointAlgEquiv (cyclicPowerHom σ hσ s.right) s.left

/-- The cyclic adjoint algebra automorphism acts on units by ambient conjugation. -/
theorem cyclicAdjointAlgEquiv_onUnits (s : H) (g : G) :
    (SemidirectProduct.inl (φ := cyclicGLAction σ hσ n) : G →* H)
      (Units.map (cyclicAdjointAlgEquiv s).toMonoidHom g) = s * SemidirectProduct.inl g * s⁻¹ := by
  let i : G →* H := SemidirectProduct.inl
  let j : CyclicComponent l →* H := SemidirectProduct.inr
  let a := cyclicGLAction σ hσ n
  have ha : a s.right = entrywiseAut (cyclicPowerHom σ hσ s.right) n := by
    change (entrywiseAutHom n σ) ^ s.right.toAdd.val = entrywiseAutHom n (σ ^ s.right.toAdd.val)
    rw [map_pow]
  have h : Units.map (cyclicAdjointAlgEquiv s).toMonoidHom g = s.left * a s.right g * s.left⁻¹ := by
    rw [ha]
    exact Units.ext rfl
  have hform : i (a s.right g) = j s.right * i g * (j s.right)⁻¹ := by
    rw [← map_inv j]
    exact SemidirectProduct.inl_aut s.right g
  have hsplit : i s.left * j s.right = s := SemidirectProduct.inl_left_mul_inr_right s
  change i _ = s * i g * s⁻¹
  calc
    _ = (i s.left * j s.right) * i g * (i s.left * j s.right)⁻¹ := by
      rw [h, map_mul, map_mul, map_inv, hform]
      group
    _ = _ := by rw [hsplit]

end Algebra

/-- The actual ordinary character restricted to a cyclic component descends to an invariant
 distribution on a clopen neighborhood of zero in the fixed algebra. The open slice distribution
 is specified by the Haar tensor identity and agrees with the ambient Lie-algebra distribution
 on tests supported in that neighborhood. -/
def CyclicGLSemisimpleDescentStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    haveI := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
    let Mat := Matrix (Fin n) (Fin n) E
    let G := GeneralLinear n E
    let H := CyclicGLSemidirect σ hE.pow_eq_one n
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    letI : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedRing Mat := finiteAlgebraNormedRing F Mat
    letI : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
    letI : CompleteSpace Mat := FiniteDimensional.complete F Mat
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    haveI : BorelSpace H := ⟨rfl⟩
    ∀ {W : Type w} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ H W) (hπ : IsAdmissible π),
      ∀ (s : H), IsCyclicGLSemisimple s → ∀ (ν : Measure H) [ν.IsHaarMeasure],
        let α := cyclicAdjointAlgEquiv s
        let S := adjointFixedAlgebra α
        let U := adjointConjugationDomain α
        let i : G →* H := SemidirectProduct.inl
        let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
        let μ := ν.comap (translatedCosetEmbedding i s)
        let D := translatedCosetDistribution i hi s (Character.distribution ν π hπ)
        letI : MeasurableSpace S := borel S
        ∃ (ρ : AdditiveHaarMeasure S) (P : SchwartzBruhat (G × U) →ₗ[ℂ] SchwartzBruhat G)
          (T : Distribution U) (T₀ : Distribution S) (C : Set S),
          IsClopen C ∧ 0 ∈ C ∧ C ⊆ U ∧
          SchwartzBruhat.IsTestPushforward (μ.prod (ρ.measure.comap Subtype.val)) μ
            (adjointConjugationOnUnits α) P ∧
          (letI : IsFiniteMeasureOnCompacts μ :=
              IsFiniteMeasureOnCompacts.comap' ν (isOpenEmbedding_translatedCoset i hi s).continuous
                (isOpenEmbedding_translatedCoset i hi s).measurableEmbedding
           D.comp P = Distribution.tensor (Distribution.ofMeasure μ) T) ∧
          UnitConjugation.IsConjugationInvariant T₀ ∧ T₀ ∈ Distribution.supportedOn C ∧
          ∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
            T₀ (SchwartzBruhat.extendZero (isOpen_adjointConjugationDomain α) f) = T f

theorem cyclicGLSemisimpleDescent.{u, v, w} : CyclicGLSemisimpleDescentStatement.{u, v, w} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE Mat G H
  let : NeZero l := ⟨hE.pos.ne'⟩
  let : Module.Finite F E := hE.1
  let : IsReduced E := hE.2.2.1
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  let : T2Space (GeneralLinear n E) := generalLinear_t2Space_of_finite F E n
  let : LocallyCompactSpace (GeneralLinear n E) := generalLinear_locallyCompactSpace_of_finite F E n
  let : TotallyDisconnectedSpace (GeneralLinear n E) :=
    generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : CompleteSpace Mat := FiniteDimensional.complete F Mat
  let : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
  let : ProperSpace Mat := FiniteDimensional.proper F Mat
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology G := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  let : SecondCountableTopology H :=
    (SemidirectProduct.homeomorphProd (cyclicGLAction σ hE.pow_eq_one n)).secondCountableTopology
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace Mat := borel Mat
  let : BorelSpace Mat := ⟨rfl⟩
  intro W _ _ π hπ s hs ν hν
  let α := cyclicAdjointAlgEquiv s
  let S := adjointFixedAlgebra α
  let U := adjointConjugationDomain α
  let i : G →* H := SemidirectProduct.inl
  let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
  let μ := ν.comap (translatedCosetEmbedding i s)
  let D := translatedCosetDistribution i hi s (Character.distribution ν π hπ)
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : IsModuleTopology F S := isModuleTopologyOfFiniteDimensional
  let : ProperSpace S := FiniteDimensional.proper F S
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  have hU := isOpen_adjointConjugationDomain α
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let ρ : AdditiveHaarMeasure S := ⟨Measure.addHaar, inferInstance, inferInstance⟩
  let : IsFiniteMeasureOnCompacts (ρ.measure.comap (Subtype.val : U → S)) :=
    IsFiniteMeasureOnCompacts.comap' ρ.measure continuous_subtype_val
      hU.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hα : Module.End.IsSemisimple α.toLinearMap := hs
  let : μ.IsHaarMeasure := isHaarMeasure_comap_translatedCoset i hi s ν
  let : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant E n μ
  let νG := ν.comap i
  let : νG.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) _ hi
  have hνG : νG.IsMulRightInvariant := generalLinear_haar_rightInvariant E n νG
  have hD (g : G) : Distribution.pushforward (adjointComponentHomeomorph α g) D = D := by
    apply translatedCosetCharacter i hi s ν π hπ hνG
    intro x
    change i (g * x * (Units.map α.toMonoidHom g)⁻¹) * s =
      i g * (i x * s) * (i g)⁻¹
    rw [map_mul, map_mul, map_inv, cyclicAdjointAlgEquiv_onUnits s g]
    change i g * i x * (s * i g * s⁻¹)⁻¹ * s = _
    simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    rw [_root_.inv_inv s]
  let B := adjointFixedTracePairing α
  have hB : UnitConjugation.IsInvariantPairing B :=
    ⟨adjointFixedTracePairing_isSymm α, adjointFixedTracePairing_nondegenerate α hα,
      adjointFixedTracePairing_conjugation α⟩
  have hval := isOpenEmbedding_generalLinearVal F E n
  obtain ⟨P, hP⟩ := semisimpleDescentPushforward α ρ.measure hval μ
  obtain ⟨T, hT, hinv⟩ := semisimpleDescentDistribution α μ ρ.measure D P hP hD
    (UnitConjugation.pairingHaarPreservation B ρ.measure hB)
  obtain ⟨C, hC, hzero, hCU, hstable⟩ := semisimpleClopenDomain α hα
  let T₀ := Distribution.clopenCutoff hC hCU T
  obtain ⟨hsupp, hagree, hcast⟩ := Distribution.clopenCutoff_spec hC hCU T
  have hT₀ : UnitConjugation.IsConjugationInvariant T₀ := by
    intro z
    let e := UnitConjugation.conjugationHomeomorph z
    have hCstable (x : S) : x ∈ C ↔ e x ∈ C := by
      refine ⟨hstable z x, fun hx => ?_⟩
      have h := hstable z⁻¹ (e x) hx
      rw [← UnitConjugation.conjugationHomeomorph_symm z, e.symm_apply_apply] at h
      exact h
    rw [hcast e (adjointSliceHomeomorph α z) (fun _ => rfl) hCstable, hinv z]
  exact ⟨ρ, P, T, T₀, C, hC, hzero, hCU, hP, hT, hT₀, hsupp, hagree hU⟩

end Langlands.BaseChange
