import Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.SigmaOrbitPeriod
import Langlands.Global.FiniteCompletionLocalField
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport

/-! # A common sigma-lift at a finite completion -/

noncomputable section

universe uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality JacquetLanglands
open scoped NumberField FiniteExtension WithZero

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance (n : ℕ) : T2Space (GeneralLinear n K) :=
  LocalFieldTopology.generalLinear_t2Space K n

local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n K) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace K n

local instance (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n K) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace K n

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

local notation "Fv" => FiniteCompletion F v
local notation "Ew" => FiniteCompletion E w

local instance : ValuativeRel Fv := FiniteCompletion.valuativeRel v
local instance : ValuativeRel Ew := FiniteCompletion.valuativeRel w
local instance : IsNonarchimedeanLocalField Fv := FiniteCompletion.isNonarchimedeanLocalField v
local instance : IsNonarchimedeanLocalField Ew := FiniteCompletion.isNonarchimedeanLocalField w

/-- Given cuspidal sigma-lift existence, a downstairs action with the regular
orbit product as its sigma-lift at a finite completion shares that lift with
an irreducible supercuspidal, essentially square-integrable action at the
original downstairs rank. -/
def CompletionCommonSigmaLiftStatement : Prop :=
  CuspidalSigmaLiftExistenceStatement.{uF, uE, uV', uW} →
  ∀ (σ : Ew ≃ₐ[Fv] Ew) (d : ℕ), IsCyclicAlgebra σ d →
  ∀ (n m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n Fv) V)
    (τ : Representation ℂ (GeneralLinear (m + 1) Ew) W),
    GeneralLinear.IsSupercuspidal τ → τ.IsIrreducible →
    HasTrivialGaloisStabilizer Fv τ →
    ∀ hRank : n = d * (m + 1),
    let ρ : Representation ℂ (GeneralLinear (d * (m + 1)) Fv) V :=
      π.comp (GeneralLinear.reindex (R := Fv) (finCongr hRank)).symm.toMonoidHom
    let Q := sigmaOrbitProduct σ d (Nat.succ_pos m) τ
    ∀ (hρ : IsAdmissible ρ) (hQ : IsAdmissible Q)
      (B : SigmaIntertwiner σ (d * (m + 1)) Q) (b : ℂ),
      IsSigmaLift σ d ρ hρ Q hQ B b →
    ∃ (X : Type (max uE uW)) (_ : AddCommGroup X) (_ : Module ℂ X)
      (P : Representation ℂ (GeneralLinear n Ew) X) (hP : IsAdmissible P)
      (V' : Type uV') (_ : AddCommGroup V') (_ : Module ℂ V')
      (π' : Representation ℂ (GeneralLinear n Fv) V') (hπ' : IsAdmissible π')
      (hπ : IsAdmissible π)
      (A A' : SigmaIntertwiner σ n P) (c c' : ℂ),
      P.IsIrreducible ∧ π'.IsIrreducible ∧ GeneralLinear.IsSupercuspidal π' ∧
      IsEssentiallySquareIntegrable π' ∧
      IsSigmaLift σ d π hπ P hP A c ∧ IsSigmaLift σ d π' hπ' P hP A' c'

set_option maxHeartbeats 800000 in
/-- Apply local cuspidal existence to the actual completions and move the
common-lift data to the original rank of the downstairs action. -/
theorem exists_commonSigmaLift_of_orbitProductLift_at_completion :
    CompletionCommonSigmaLiftStatement v w := by
  intro hExist σ d hcyc n m V _ _ W _ _ π τ hτ hIrred hstab hRank
  dsimp only
  intro hρ hP A c hLift
  subst n
  let : NontriviallyNormedField Fv :=
    Valued.toNontriviallyNormedField Fv (WithZero (Multiplicative ℤ))
  have : CharZero Fv := charZero_of_injective_algebraMap (algebraMap F Fv).injective
  have : IsModuleTopology Fv Ew := isModuleTopologyOfFiniteDimensional
  have hper (i : ℕ) :
      Nonempty (τ.Equiv (τ.comp (entrywiseAut (σ ^ i) (m + 1)).toMonoidHom)) ↔ d ∣ i := by
    simpa only [hcyc.2.2.2.1] using
      conjugate_equiv_iff_orderOf_dvd Fv Ew σ (m + 1) W τ hstab i
  have hsize : 0 < d * (m + 1) := Nat.mul_pos hcyc.pos (Nat.succ_pos m)
  obtain ⟨hPI, _, V', addV', modV', π', hπ', A', c', hSC', hI', _, hLift'⟩ :=
    hExist Fv Ew σ d hcyc d (m + 1) (Nat.succ_pos m) W τ hτ hIrred hper
  let := addV'
  let := modV'
  have hESQ : IsEssentiallySquareIntegrable π' := by
    have h := padicSupercuspidalEssentialSquareIntegrability _
      (CompletionPadic.padicField v) (CompletionPadic.topologicalData v)
      (d * (m + 1)) hsize V' π' hI' hSC'
    have transfer (R : ValuativeRel Fv)
        (hR : @IsNonarchimedeanLocalField Fv _ R _)
        (hEq : R = FiniteCompletion.valuativeRel v) :
        @IsEssentiallySquareIntegrable Fv _ R _ hR _ _ _ _ π' →
          @IsEssentiallySquareIntegrable Fv _ (FiniteCompletion.valuativeRel v) _
            (FiniteCompletion.isNonarchimedeanLocalField v) _ _ _ _ π' := by
      subst R
      exact id
    exact transfer (CompletionPadic.topologicalData v).valuativeRel
      (CompletionPadic.topologicalData v).localField
      (FiniteCompletion.topologicalData_valuativeRel_eq v) h
  have hEq := RankinSelberg.SupercuspidalLFactorCharacterization.comp_reindex_finCongr_rfl
    (CompletionPadic.padicField v) π
  let hπ : IsAdmissible π := hEq ▸ hρ
  let e : Representation.Equiv (π.comp (GeneralLinear.reindex (R := Fv)
    (finCongr (rfl : d * (m + 1) = d * (m + 1)))).symm.toMonoidHom) π :=
    hEq.symm ▸ Representation.Equiv.refl π
  let P := sigmaOrbitProduct σ d (Nat.succ_pos m) τ
  let eP : P.Equiv P := Representation.Equiv.refl _
  exact ⟨_, _, _, P, hP, V', addV', modV', π', hπ', hπ,
    A.transport eP, A', c, c', hPI, hI', hSC', hESQ, hLift.transport hπ e hP eP, hLift'⟩

end LocalField

end Langlands.BaseChange
