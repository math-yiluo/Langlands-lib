import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransportLattice
import Langlands.Correspondence.AssemblyDeterminant

/-!
# Central characters along an isomorphism of p-adic fields
-/

noncomputable section

universe uF uE uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- An isomorphism of p-adic fields on unit groups. -/
def unitsAlgEquiv : F.Carrierˣ →* E.Carrierˣ :=
  Units.map (f : F.Carrier →* E.Carrier)

@[simp]
theorem coe_unitsAlgEquiv_apply (a : F.Carrierˣ) : (unitsAlgEquiv F E f a : E.Carrier) = f a :=
  rfl

/-- Pullback along `f` turns a central character `ω` of a unitary supercuspidal basis
class into `ω ∘ f`. -/
theorem isUnitaryBasisCentralCharacter_unitaryBasisEquiv (b : UnitaryBasis.{uE, uV} E)
    (ω : E.Carrierˣ →* ℂˣ) (h : IsUnitaryBasisCentralCharacter E b ω) :
    IsUnitaryBasisCentralCharacter F (unitaryBasisEquiv F E f b)
      (ω.comp (unitsAlgEquiv F E f)) := by
  let _ := F.canonicalTopologicalData.topology
  let _ := E.canonicalTopologicalData.topology
  obtain ⟨⟨n, c⟩, hb⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    intro a
    have hA := h (unitsAlgEquiv F E f a)
    refine ⟨(GeneralLinear.SupercuspidalRep.fieldPullback (σ := f.toRingEquiv)
      (hσ := continuous_algEquiv F E f) (hσs := continuous_algEquiv E F f.symm)
      A).toIrreducibleAdmissible, rfl, fun v => ?_⟩
    have hs : GeneralLinear.fieldEquiv (n : ℕ) f.toRingEquiv (continuous_algEquiv F E f)
        (continuous_algEquiv E F f.symm) (GeneralLinear.scalar a) =
          GeneralLinear.scalar (unitsAlgEquiv F E f a) := by
      change Matrix.GeneralLinearGroup.map f.toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin n) a) = _
      rw [Matrix.GeneralLinearGroup.map_scalar]
      rfl
    change A.obj.representation (GeneralLinear.fieldEquiv (n : ℕ) f.toRingEquiv
      (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) (GeneralLinear.scalar a)) v = _
    rw [hs]
    exact AssemblyDeterminant.centralActsBy_apply E hA A.toIrreducibleAdmissible rfl v

/-- Pullback along `f` turns a central character `ω` of a unitary virtual
supercuspidal class into `ω ∘ f`. -/
theorem isUnitaryCentralCharacter_unitaryLatticeEquiv (y : UnitaryLattice.{uE, uV} E)
    (ω : E.Carrierˣ →* ℂˣ) (h : IsUnitaryCentralCharacter E y ω) :
    IsUnitaryCentralCharacter F (unitaryLatticeEquiv F E f y)
      (ω.comp (unitsAlgEquiv F E f)) := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨fun b' => (g ((unitaryBasisEquiv F E f).symm b')).comp (unitsAlgEquiv F E f),
    fun b' hb' => ?_, ?_⟩
  · have hmem : (unitaryBasisEquiv F E f).symm b' ∈ y.support := by
      rw [Finsupp.mem_support_iff] at hb' ⊢
      rwa [← unitaryLatticeEquiv_coefficient F E f y, Equiv.apply_symm_apply]
    have := isUnitaryBasisCentralCharacter_unitaryBasisEquiv F E f _ _ (hg _ hmem)
    rwa [Equiv.apply_symm_apply] at this
  · rw [unitaryLatticeEquiv_eq_equivMapDomain, Finsupp.prod_equivMapDomain]
    simp only [Equiv.symm_apply_apply]
    ext a
    simp [Finsupp.prod, MonoidHom.zpow_apply]

end Langlands.VirtualRepresentation.PadicSupercuspidal
