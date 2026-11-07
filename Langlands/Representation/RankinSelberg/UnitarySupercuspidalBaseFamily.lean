import Langlands.Representation.RankinSelberg.SupercuspidalEulerFamily
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity

/-! # Actual smooth-dual base factors for unitary supercuspidal families -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV uW uI

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Apply the pair constructor to the actual smooth contragredient. Its
supercuspidality, irreducibility and unitarity follow from proved duality. -/
def unitarySupercuspidalDualPairEuler
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hiπ : π.IsIrreducible) (hiσ : σ.IsIrreducible)
    (hsπ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π)
    (hsσ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ)
    (huπ : IsUnitarizable π) (huσ : IsUnitarizable σ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    SupercuspidalPairEuler ψ ν π (smoothContragredient σ) := by
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  have hsd := isSupercuspidal_smoothContragredient F
    F.canonicalTopologicalData (n + 1) W σ hsσ
  have hid := ((supercuspidalContragredient p F F.canonicalTopologicalData
    (n + 1) W σ hsσ.1.1).2 hsσ.1).mpr hiσ
  have hud := HarishChandraSchwartz.isUnitarizable_smoothContragredient_of_admissible
    (compactOpen_cofinal F F.canonicalTopologicalData (n + 1)) hsσ.1 huσ
  exact supercuspidalPairEuler hEq ψ ν π (smoothContragredient σ)
    hiπ hid hsπ hsd huπ hud

/-- An equivalence of the original actions, with the original rank transport,
gives the exact contragredient relation to the smooth dual, by reflexivity. -/
theorem isRankContragredient_dual_of_equiv
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hadm : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    (hr : r = n) (he : Nonempty ((hr ▸ π).Equiv σ)) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    IsRankContragredient π (smoothContragredient σ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  refine ⟨hr, ?_⟩
  obtain ⟨e⟩ := he
  have hb := ((smoothAdmissibleDuality
    (G := Langlands.GeneralLinear (n + 1) F.Carrier) (V := W)
    (compactOpen_cofinal F F.canonicalTopologicalData (n + 1))).2 σ hadm).2
  exact ⟨e.trans ((smoothBidual hadm.1).ofBijective hb)⟩

/-- Construct the base factors of a dependent family with varying positive
ranks, always pairing an original action with the actual smooth dual. -/
def unitarySupercuspidalBaseFamily
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {I : Type uI} (r : I → ℕ)
    (V : I → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (Langlands.GeneralLinear (r i + 1) F.Carrier) (V i))
    (hi : ∀ i, (ρ i).IsIrreducible)
    (hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSupercuspidal (ρ i))
    (hu : ∀ i, IsUnitarizable (ρ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ i j, letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r j + 1)
      SupercuspidalPairEuler ψ ν (ρ i) (smoothContragredient (ρ j)) :=
  fun i j => unitarySupercuspidalDualPairEuler hEq ψ ν (ρ i) (ρ j)
    (hi i) (hi j) (hs i) (hs j) (hu i) (hu j)

/-- Original-action matching supplies genuine poles, and the finite Euler
analysis proves every Appendix base-pair condition for the actual family. -/
theorem unitarySupercuspidalBaseFamily_conditions
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {I : Type uI} (r : I → ℕ)
    (V : I → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (Langlands.GeneralLinear (r i + 1) F.Carrier) (V i))
    (hi : ∀ i, (ρ i).IsIrreducible)
    (hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSupercuspidal (ρ i))
    (hu : ∀ i, IsUnitarizable (ρ i))
    (partner : I → I) (hr : ∀ i, r i = r (partner i))
    (he : ∀ i, Nonempty (((hr i) ▸ ρ i).Equiv (ρ (partner i)))) :
    Global.PoleComparison.BasePairConditions partner
      (fun i j => (unitarySupercuspidalBaseFamily hEq ψ ν r V ρ hi hs hu i j).data.reciprocal) := by
  let := F.canonicalTopologicalData.topology
  apply LocalFactor.FiniteUnitaryEuler.basePairConditions
  intro i
  apply (unitarySupercuspidalBaseFamily hEq ψ ν r V ρ hi hs hu i (partner i)).one_mem_iff.mpr
  exact isRankContragredient_dual_of_equiv (ρ i) (ρ (partner i))
    (hs (partner i)).1 (hr i) (he i)

end Langlands.RankinSelberg
