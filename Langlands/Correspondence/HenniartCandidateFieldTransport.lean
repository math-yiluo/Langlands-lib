import Langlands.Global.Factors.HenniartCompositeOperationWeil
import Langlands.Global.Factors.HenniartCompositeOperationSupercuspidalTwist
import Langlands.Global.Factors.HenniartCompositeFactorWeil
import Langlands.Global.Factors.HenniartCompositeFactorCentral
import Langlands.Global.Factors.UnitaryPairFactorTransport
import Langlands.LocalFactor.NonabelianSystemFieldTransportPairEpsilon
import Langlands.Correspondence.RankOneArithmeticEpsilonData

/-! # Field transport of the properties of Henniart's lattice maps -/

noncomputable section

namespace Langlands.Correspondence.LatticeMap

open Langlands.Weil.Local Langlands.VirtualRepresentation
open Langlands.LocalFactor.NonabelianSystem.FieldTransport

universe uF uE uW uV uC

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)
  {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uE, uW} E)}
  {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uE, uV} E)}

local notation "φ" => extensionWeilEquiv E F f.symm
local notation "wPull" => Weil.restrictUnitaryLatticeEquiv φ
local notation "aPull" => PadicSupercuspidal.unitaryLatticeEquiv F E f

/-- Pull back the domain and range along the Weil and field isomorphisms. -/
def fieldPullback (T : W ≃ₗ[ℤ] A) : W.map (wPull).toLinearMap ≃ₗ[ℤ] A.map (aPull).toLinearMap :=
  ((wPull).submoduleMap W).symm ≪≫ₗ T ≪≫ₗ (aPull).submoduleMap A

@[simp]
theorem fieldPullback_apply (T : W ≃ₗ[ℤ] A) (x : W) :
    ((fieldPullback F E f T) (((wPull).submoduleMap W) x) :
      PadicSupercuspidal.UnitaryLattice F) = aPull (T x) := by
  simp [fieldPullback]

private theorem fieldPullback_commutes (T : W ≃ₗ[ℤ] A)
    {wE : LocalWeil.UnitaryLattice.{uE, uW} E → LocalWeil.UnitaryLattice.{uE, uW} E}
    {wF : LocalWeil.UnitaryLattice.{uF, uW} F → LocalWeil.UnitaryLattice.{uF, uW} F}
    {aE : PadicSupercuspidal.UnitaryLattice.{uE, uV} E →
      PadicSupercuspidal.UnitaryLattice.{uE, uV} E}
    {aF : PadicSupercuspidal.UnitaryLattice.{uF, uV} F →
      PadicSupercuspidal.UnitaryLattice.{uF, uV} F}
    (hw : ∀ x, wPull (wE x) = wF (wPull x)) (ha : ∀ y, aPull (aE y) = aF (aPull y))
    (h : ∀ x : W, ∃ hx : wE x ∈ W, (T ⟨_, hx⟩ : PadicSupercuspidal.UnitaryLattice E) =
      aE (T x)) (x : W.map (wPull).toLinearMap) :
    ∃ hx : wF x ∈ W.map (wPull).toLinearMap,
      (fieldPullback F E f T ⟨_, hx⟩ : PadicSupercuspidal.UnitaryLattice F) =
        aF (fieldPullback F E f T x) := by
  obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
  obtain ⟨hx, hTx⟩ := h x
  have hmem : wF (wPull x) ∈ W.map (wPull).toLinearMap := by
    rw [← hw]
    exact Submodule.mem_map_of_mem hx
  refine ⟨hmem, ?_⟩
  have hsub : (⟨wF (wPull x), hmem⟩ : W.map (wPull).toLinearMap) =
      ((wPull).submoduleMap W) ⟨wE x, hx⟩ := Subtype.ext (hw x).symm
  change (fieldPullback F E f T ⟨wF (wPull x), hmem⟩ :
    PadicSupercuspidal.UnitaryLattice F) = _
  rw [hsub, fieldPullback_apply, hTx, ha, fieldPullback_apply]

private theorem fieldPullback_reciprocity (e : ReciprocityCandidate F)
    (he : IsGeometricReciprocity F e) :
    ∃ e' : ReciprocityCandidate E, IsGeometricReciprocity E e' ∧
      ∀ w, reciprocityHom E e' (φ w) =
        PadicSupercuspidal.unitsAlgEquiv F E f (reciprocityHom F e w) := by
  obtain ⟨e', he', h⟩ := LocalClassField.exists_geometric_extensionWeilEquiv E F f.symm e he
  exact ⟨e', he', fun w => Units.ext (h w)⟩

private theorem fieldPullback_operations (T : W ≃ₗ[ℤ] A) (hT : OperationProperties E T) :
    OperationProperties F (fieldPullback F E f T) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
    obtain ⟨y, rfl⟩ := ((wPull).submoduleMap W).surjective y
    change PadicSupercuspidal.unitaryPairing F _ _ = LocalWeil.unitaryPairing F (wPull x) (wPull y)
    rw [fieldPullback_apply, fieldPullback_apply, PadicSupercuspidal.unitaryPairing_unitaryLatticeEquiv]
    exact (hT.1.1 x y).trans (Weil.unitaryPairing_restrictUnitaryLatticeEquiv φ x.1 y.1).symm
  · intro x
    obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
    change PadicSupercuspidal.unitaryDegree F _ = LocalWeil.unitaryDegree F (wPull x)
    rw [fieldPullback_apply, PadicSupercuspidal.unitaryDegree_unitaryLatticeEquiv]
    exact (hT.1.2 x).trans (Weil.unitaryDegree_restrictUnitaryLatticeEquiv φ x.1).symm
  · intro x
    obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
    change (∃ b, wPull x = generator b) ↔
      (∃ b, (fieldPullback F E f T (((wPull).submoduleMap W) x) :
        PadicSupercuspidal.UnitaryLattice F) = generator b)
    simp only [fieldPullback_apply]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := (Weil.restrictUnitaryBasisEquiv φ).surjective b
      rw [← Weil.restrictUnitaryLatticeEquiv_generator] at hb
      obtain ⟨a, ha⟩ := (hT.2.1 x).mp ⟨b, (wPull).injective hb⟩
      exact ⟨_, by rw [ha, PadicSupercuspidal.unitaryLatticeEquiv_generator]⟩
    · rintro ⟨a, ha⟩
      obtain ⟨a, rfl⟩ := (PadicSupercuspidal.unitaryBasisEquiv F E f).surjective a
      rw [← PadicSupercuspidal.unitaryLatticeEquiv_generator] at ha
      obtain ⟨b, hb⟩ := (hT.2.1 x).mpr ⟨a, (aPull).injective ha⟩
      exact ⟨_, by rw [hb, Weil.restrictUnitaryLatticeEquiv_generator]⟩
  · exact fieldPullback_commutes F E f T
      (Weil.restrictUnitaryLatticeEquiv_unitaryDualLatticeEquiv φ)
      (PadicSupercuspidal.unitaryLatticeEquiv_unitaryContragredientLatticeEquiv F E f) hT.2.2.1
  · intro e he χ hχ
    obtain ⟨e', he', hrec⟩ := fieldPullback_reciprocity F E f e he
    let χ' : QuasiCharacter E := PadicField.ConductorTransport.quasicharacter F E f χ
    have hχ' : ∀ a, ‖(χ' a : ℂ)‖ = 1 := fun _ => hχ _
    have hrel (a : F.Carrierˣ) (b : E.Carrierˣ) (hab : (b : E.Carrier) = f (a : F.Carrier)) :
        χ' b = χ a := by
      change χ ((PadicField.ConductorTransport.unitsEquiv F E f).symm b) = χ a
      congr 1
      exact Units.ext ((PadicField.ConductorTransport.unitsEquiv_symm_apply F E f b).trans
        (f.symm_apply_eq.mpr hab))
    have hcomp : (LocalFactor.RankOne.weilCharacter E e' χ').comp
        (φ : localWeilGroup F →ₜ* localWeilGroup E) = LocalFactor.RankOne.weilCharacter F e χ := by
      ext w
      exact congrArg (fun b : ℂˣ => (b : ℂ)) (hrel _ _ (congrArg Units.val (hrec w)))
    obtain ⟨hTw, hChar⟩ := hT.2.2.2 e' he' χ' hχ'
    constructor
    · apply fieldPullback_commutes F E f T _
        (PadicSupercuspidal.unitaryLatticeEquiv_unitaryCharacterTwistLatticeEquiv
          F E f χ' hχ' χ hχ hrel) hTw
      intro x
      have hlift : ∀ w, ‖(((LocalFactor.RankOne.weilCharacter E e' χ').comp
          (φ : localWeilGroup F →ₜ* localWeilGroup E)) w : ℂ)‖ = 1 := fun w => by
        rw [hcomp]
        exact LocalWeil.norm_weilCharacter_eq_one F e χ hχ w
      exact (Weil.restrictUnitaryLatticeEquiv_unitaryTwistLatticeEquiv φ
        (LocalFactor.RankOne.weilCharacter E e' χ')
        (LocalWeil.norm_weilCharacter_eq_one E e' χ' hχ') hlift x).trans
          (LinearEquiv.congr_fun (Weil.unitaryTwistLatticeEquiv_congr hcomp _ _) _)
    · obtain ⟨x, hxW, hxA⟩ := hChar
      refine ⟨((wPull).submoduleMap W) x, ?_, ?_⟩
      · change Weil.includeUnitary _ (wPull x) = _
        rw [Weil.includeUnitary_restrictUnitaryLatticeEquiv]
        change Weil.restrictLatticeEquiv φ (LocalWeil.includeUnitary E x) = _
        rw [hxW, Weil.restrictLatticeEquiv_generator]
        unfold rankOneWeilCharacterClass
        rw [Weil.restrictBasisEquiv_characterClass, hcomp]
      · rw [fieldPullback_apply]
        exact PadicSupercuspidal.includeUnitary_unitaryLatticeEquiv_rankOne F E f χ' χ hrel _ hxA

private theorem fieldPullback_determinant (T : W ≃ₗ[ℤ] A)
    (hT : ∀ e : ReciprocityCandidate E, IsGeometricReciprocity E e → DeterminantCompatibility E T e)
    (e : ReciprocityCandidate F) (he : IsGeometricReciprocity F e) :
    DeterminantCompatibility F (fieldPullback F E f T) e := by
  obtain ⟨e', he', hrec⟩ := fieldPullback_reciprocity F E f e he
  intro x
  obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
  obtain ⟨ω, hω, hdet⟩ := hT e' he' x
  refine ⟨ω.comp (PadicSupercuspidal.unitsAlgEquiv F E f), ?_, fun w => ?_⟩
  · rw [fieldPullback_apply]
    exact PadicSupercuspidal.isUnitaryCentralCharacter_unitaryLatticeEquiv F E f _ ω hω
  · change ω (PadicSupercuspidal.unitsAlgEquiv F E f (reciprocityHom F e w)) =
      Additive.toMul (LocalWeil.unitaryDeterminant F (wPull x)) w
    rw [← hrec, LocalWeil.unitaryDeterminant_restrictUnitaryLatticeEquiv]
    exact hdet (φ w)

private theorem fieldPullback_pairFactors (T : W ≃ₗ[ℤ] A)
    (hT : ∀ ψ : NontrivialAdditiveCharacter E, PairFactorCompatibility.{uE, uW, uV, uC} E T ψ)
    (ψ : NontrivialAdditiveCharacter F) :
    PairFactorCompatibility.{uF, uW, uV, uC} F (fieldPullback F E f T) ψ := by
  let ψ' : NontrivialAdditiveCharacter E := PadicField.ConductorTransport.additiveCharacter F E f ψ
  refine ⟨(existsUnique_localSelfDualMeasure F ψ).exists, ?_⟩
  intro ν hν x y
  obtain ⟨x, rfl⟩ := ((wPull).submoduleMap W).surjective x
  obtain ⟨y, rfl⟩ := ((wPull).submoduleMap W).surjective y
  have hν' : IsSelfDualMeasure E ψ' (PadicField.AbelianTransport.haarMeasure F E f ν) :=
    (PadicField.AbelianTransport.isSelfDual_iff F E f ψ ν).mpr hν
  obtain ⟨hL, hε⟩ := (hT ψ').2 _ hν' x y
  simp only [fieldPullback_apply]
  refine ⟨?_, ?_⟩
  · change PadicSupercuspidal.IsUnitaryPairLFactor F ψ ν (aPull (T x)) (aPull (T y))
      (LocalWeil.unitaryPairLFactor F (wPull x) (wPull y))
    rw [LocalWeil.unitaryPairLFactor_restrictUnitaryLatticeEquiv E F φ
      (localDegreeInt_extensionWeilEquiv E F f.symm)]
    exact (PadicSupercuspidal.isUnitaryPairLFactor_unitaryLatticeEquiv_iff_transport
      f ψ ν _ _ _).mpr hL
  · intro eC ε hεF
    have hsys := isSystem_transportAssignment E F f.symm hεF
    obtain ⟨c, hW, hA⟩ := hε (transportFamily E F f.symm eC)
      (transportAssignment E F f.symm ε) hsys
    refine ⟨c, ?_, (PadicSupercuspidal.isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff_transport
      f ψ ν _ _ c).mpr hA⟩
    exact isUnitaryPairEpsilonFactor_transport E F f.symm eC ε hεF hsys ψ' ψ
      (fun _ => rfl) x y c hW

/-- All of the character, representation and pair-factor clauses are preserved
by pullback along an isomorphism of p-adic fields. -/
theorem henniartProperties_fieldPullback (T : W ≃ₗ[ℤ] A)
    (hT : HenniartProperties.{uE, uW, uV, uC} E T) :
    HenniartProperties.{uF, uW, uV, uC} F (fieldPullback F E f T) :=
  ⟨fieldPullback_operations F E f T hT.1,
    fieldPullback_determinant F E f T hT.2.1, fieldPullback_pairFactors F E f T hT.2.2⟩

end Langlands.Correspondence.LatticeMap
