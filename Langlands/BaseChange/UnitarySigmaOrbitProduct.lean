import Langlands.BaseChange.SigmaOrbitConjugates
import Langlands.BaseChange.PseudoCoefficient
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-! # Unitary supercuspidal orbit products over characteristic-zero local fields -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe u v uW

/-- The canonical tempered induction theorem in the supplied realization. -/
private theorem unitaryProduct_isTempered {p : ℕ} [Fact p.Prime] {L : PadicField.{v} p}
    (S : L.TopologicalData) {r : ℕ} (hr : 0 < r) (B : BlockShape r) :
    letI := S.topology
    ∀ (A : ∀ i, SupercuspidalRep.{v, max v uW} (F := L.Carrier) (n := B.size i)),
      (∀ i, IsUnitarizable (A i).obj.representation) →
      S.IsTempered (S.normalizedProductInduced B (fun i => (A i).obj.representation)) := by
  rw [S.eq_canonicalTopologicalData]
  exact Classification.unitarizableSupercuspidalProduct_isTempered.{v,uW} L hr B

set_option maxHeartbeats 800000 in
/-- The actual positive-length normalized orbit product of a unitarizable
irreducible supercuspidal is irreducible, unitarizable and analytically tempered. -/
theorem sigmaOrbitProduct_isIrreducible_isUnitarizable_isTempered
    {F : Type u} [Field F] [TopologicalSpace F]
    {E : Type v} [Field E] [CharZero E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) {s n : ℕ} (hs : 0 < s) (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W)
    (hP : P.IsIrreducible) (hsc : IsSupercuspidal P) (hu : IsUnitarizable P) :
    (sigmaOrbitProduct σ s hn P).IsIrreducible ∧
      IsUnitarizable (sigmaOrbitProduct σ s hn P) ∧
      IsTemperedRep (sigmaOrbitProduct σ s hn P) := by
  let T := LocalFieldData.ofInstances E
  let p := CharZeroLocalField.residueChar E
  let : Fact p.Prime := ⟨CharZeroLocalField.residueChar_prime E⟩
  let L := CharZeroLocalField.padicField E
  let S : L.TopologicalData := CharZeroLocalField.topologicalData E
  let B := BlockShape.uniform s n hn
  let ρ (i : Fin B.length) : Representation ℂ (GeneralLinear n E) W :=
    P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom
  let A₀ (i : Fin B.length) : SupercuspidalRep.{v,uW} (F := E) (n := B.size i) := by
    have hi : IsSupercuspidal (ρ i) := isSupercuspidal_comp_entrywiseAut (σ ^ (i : ℕ)) P hsc
    exact ⟨SmoothRep.of (ρ i) hi.1.1,
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff P (entrywiseAut _ _)).mpr hP, hi⟩
  let A (i : Fin B.length) := (A₀ i).universeLift
  have hAu (i : Fin B.length) : IsUnitarizable (A i).obj.representation :=
    (isUnitarizable_iff_of_equiv (A₀ i).universeLiftEquiv).mp (hu.comp _)
  have hAb : (S.normalizedProductInduced B (fun i => (A i).obj.representation)).IsIrreducible ∧
      IsUnitarizable (S.normalizedProductInduced B (fun i => (A i).obj.representation)) :=
    Classification.bernsteinUnitaryProductIrreducibility.{v,uW} L S (s * n) B
      (fun i => (A i).obj) (fun i => ⟨(A i).property.1, hAu i⟩)
  have hAt := unitaryProduct_isTempered.{v,uW} S (Nat.mul_pos hs hn) B A hAu
  let (i : Fin B.length) : AddCommGroup (A i).obj := inferInstance
  let (i : Fin B.length) : Module ℂ (A i).obj := inferInstance
  let e := T.normalizedProductInducedEquiv B (fun i => (A₀ i).universeLiftEquiv)
  change (sigmaOrbitProduct σ s hn P).Equiv
    (S.normalizedProductInduced B (fun i => (A i).obj.representation)) at e
  exact ⟨(CentralEigenspaceSplitting.isIrreducible_iff_of_equiv e).mpr hAb.1,
    (isUnitarizable_iff_of_equiv e).mpr hAb.2,
    (isTemperedRep_iff_of_equiv e).mpr
      ((isTemperedRep_iff_isTempered S _).mpr hAt)⟩

end Langlands.BaseChange
