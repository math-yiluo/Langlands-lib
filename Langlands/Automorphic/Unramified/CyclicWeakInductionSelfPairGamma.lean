import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof
import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.Automorphic.Unramified.WeakInductionUnitaryCentralCharacter
import Langlands.Representation.RankinSelberg.UnitarySupercuspidalPairGammaOrder

/-! # Unique-place supercuspidality from the Rankin–Selberg self-pair comparison -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open CuspidalOperatorRealization Correspondence GeneralLinear Whittaker
open HarmonicAnalysis LocalFactor RankinSelberg
open ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open scoped NumberField FiniteExtension

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local instance selfPairMatchingRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance selfPairMatchingContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance selfPairMatchingSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance selfPairMatchingFormAddCommGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance selfPairMatchingLocalAddCommGroup {v : FinitePlace K} (A : LocalRealization K n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

/-- The integral gamma certificate for an actual local factor against the
actual smooth contragredient of a second factor at the same completion. -/
def HasLocalDualPairGamma {v : FinitePlace K} {r : ℕ}
    (A B : LocalRealization K (r + 1) v) (ψ : NontrivialAdditiveCharacter (padicField v))
    (ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ)
    (G : RatFunc ℂ) : Prop :=
  let T := (padicField v).canonicalTopologicalData
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (r + 1)
  IsPadicSymmetricGammaFactor (padicField v) ψ ν.val
    A.representation (smoothContragredient B.representation) G

/-- The local order comparison for the self-pair of a supplied weak induction.
The upper product pairs the original upper action with the smooth dual of
each of its arithmetic conjugates, including the identity conjugate. -/
def CyclicWeakInductionSelfPairGammaOrderAtUniquePlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (r m : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E m)
      (Q : CuspidalSpectralPresentation.{uF, uV} S) (P : CuspidalSpectralPresentation.{uE, uW} T)
      (U : Fin (Module.finrank F E) → CuspidalOperatorRealization E m)
      (R : ∀ i, CuspidalSpectralPresentation.{uE, uW} (U i)),
      HasUnitaryCentralCharacter S → HasUnitaryCentralCharacter T →
      (Q.localComponent v).IsIrreducible → (Q.localComponent v).IsAdmissible →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i, ((R i).localComponent w.1).IsSupercuspidal) →
      (∀ i : Fin (Module.finrank F E),
        T.isoClass.IsGaloisConjugate (σ ^ (i : ℕ)) (U i).isoClass) →
      S.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass →
      ∃ (ψv : NontrivialAdditiveCharacter (padicField v))
        (νv : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψv)
        (ψw : NontrivialAdditiveCharacter (padicField w.1))
        (νw : PadicAbelian.SelfDualHaar (padicField w.1).canonicalTopologicalData ψw)
        (G : RatFunc ℂ) (D : Fin (Module.finrank F E) → RatFunc ℂ),
        HasLocalDualPairGamma (Q.localComponent v) (Q.localComponent v) ψv νv G ∧
        (∀ i, HasLocalDualPairGamma (P.localComponent w.1) ((R i).localComponent w.1) ψw νw (D i)) ∧
        ∀ t : ℝ, meromorphicOrderAt
          (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality G)
          (t : ℂ) =
          ∑ i, meromorphicOrderAt
            (rationalSpectralValue (padicField w.1).canonicalTopologicalData.residueCardinality (D i))
            (t : ℂ)

private theorem isSupercuspidal_iff_padicObject {r : ℕ} {v : FinitePlace K}
    (A : LocalRealization K (r + 1) v) (hi : A.IsIrreducible) (ha : A.IsAdmissible) :
    A.IsSupercuspidal ↔
      letI := (padicField v).canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal (A.padicObject hi ha).obj.representation :=
  A.isSupercuspidal_iff_representation.trans ((and_iff_right hi).trans (iff_of_eq (congrArg
    (fun t : TopologicalSpace (FiniteCompletion K v) =>
      @GeneralLinear.IsSupercuspidal (FiniteCompletion K v) _ t (r + 1) _ _ _ A.representation)
    (completion_topology_eq v))))

set_option maxHeartbeats 1000000 in
private theorem upper_gamma_orders {E : Type uE} [Field E] [NumberField E]
    {w : FinitePlace E} {m : ℕ} (A B : LocalRealization E (m + 1) w)
    (hA : A.IsSupercuspidal) (hB : B.IsSupercuspidal)
    (huA : IsUnitarizable A.representation) (huB : IsUnitarizable B.representation)
    (ψ : NontrivialAdditiveCharacter (padicField w))
    (ν : PadicAbelian.SelfDualHaar (padicField w).canonicalTopologicalData ψ)
    (G : RatFunc ℂ) (hG : HasLocalDualPairGamma A B ψ ν G) : by
    classical
    exact (∀ t : ℝ, t ≠ 0 → meromorphicOrderAt
        (rationalSpectralValue (padicField w).canonicalTopologicalData.residueCardinality G)
        (t : ℂ) ≤ 0) ∧
      meromorphicOrderAt
        (rationalSpectralValue (padicField w).canonicalTopologicalData.residueCardinality G) 0 =
        if A.isoClass = B.isoClass then 1 else 0 := by
  classical
  obtain ⟨hAI, hAA, hASC⟩ := hA
  obtain ⟨hBI, hBA, hBSC⟩ := hB
  let L := padicField w
  let T := L.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (m + 1)
  let π : SupercuspidalRep.{uE, uE} (F := L.Carrier) (n := m + 1) :=
    ⟨(A.padicObject hAI hAA).obj, hAI,
      (isSupercuspidal_iff_padicObject A hAI hAA).mp ⟨hAI, hAA, hASC⟩⟩
  let σ : SmoothRep.{0, uE, uE} ℂ (GeneralLinear (m + 1) L.Carrier) :=
    (B.padicObject hBI hBA).obj
  have hBSc := (isSupercuspidal_iff_padicObject B hBI hBA).mp ⟨hBI, hBA, hBSC⟩
  have hadm : σ.IsAdmissible := (B.padicObject hBI hBA).property.2
  have hcof := compactOpen_cofinal L T (m + 1)
  let σd : SupercuspidalRep.{uE, uE} (F := L.Carrier) (n := m + 1) :=
    ⟨σ.contragredient, (σ.isIrreducible_contragredient_iff hcof hadm).mpr hBI,
      isSupercuspidal_smoothContragredient L T (m + 1) σ σ.representation hBSc⟩
  have huBd : IsUnitarizable σd.obj.representation := by
    have hUσ : IsUnitarizable σ.representation := huB
    obtain ⟨b⟩ := hUσ
    let e := b.smoothDualEquiv hcof hadm
    exact (isUnitarizable_iff_of_conjugateEquiv (ρ := σ.representation)
      (σ := σ.contragredient.representation) e (b.toSmoothDual_apply_action hadm.1)).mp ⟨b⟩
  have horder := unitarySupercuspidalPairGammaOrder (residuePrime w) L ψ ν m m
    π σd huA huBd G hG
  let e := (smoothBidual hadm.1).ofBijective
    ((smoothAdmissibleDuality (V := σ) hcof).2 σ.representation hadm).2
  have hclasses : IsRankContragredient π.obj.representation σd.obj.representation ↔
      A.isoClass = B.isoClass := by
    rw [A.isoClass_eq_iff B]
    constructor
    · rintro ⟨h, ⟨f⟩⟩
      have hh : h = rfl := Subsingleton.elim _ _
      rw [hh] at f
      exact ⟨f.trans e.symm⟩
    · rintro ⟨f⟩
      exact ⟨rfl, ⟨f.trans e⟩⟩
  refine ⟨fun t ht => horder.2.1 (t : ℂ) (by simpa using ht), horder.2.2.trans ?_⟩
  exact if_congr hclasses rfl rfl

/-- The self-pair order comparison at the unique place suffices for the
unrestricted supercuspidality target. -/
def CyclicWeakInductionSupercuspidalFromGammaOrderStatement : Prop :=
  CyclicWeakInductionSelfPairGammaOrderAtUniquePlaceStatement.{uF, uE, uV, uW} →
  CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW}

set_option maxHeartbeats 1500000 in
theorem cyclicWeakInductionSupercuspidal_of_gammaOrder :
    CyclicWeakInductionSupercuspidalFromGammaOrderStatement.{uF, uE, uV, uW} := by
  classical
  intro hMatch F E _ _ _ _ _ _ _ _ hPrime σ hgen v w hw r m S T P hT hP hconj hWeak
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let d := Module.finrank F E
  let i₀ : Fin d := ⟨0, hPrime.pos⟩
  have hOrbit (i : Fin d) :
      ∃ (U : CuspidalOperatorRealization E m) (R : CuspidalSpectralPresentation.{uE, uW} U),
        T.isoClass.IsGaloisConjugate (σ ^ (i : ℕ)) U.isoClass ∧
        (R.localComponent w.1).IsSupercuspidal ∧
        ((P.localComponent w.1).isoClass = (R.localComponent w.1).isoClass ↔ i = i₀) := by
    by_cases h : i = i₀
    · subst i
      exact ⟨T, P, by simpa [i₀] using (IsoClass.isGaloisStable_one (F := F) T.isoClass), hP, by simp⟩
    · have hi : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun hzero => h (Fin.ext hzero)
      obtain ⟨U, R, hTU, hR, hne⟩ := hconj (i : ℕ) hi i.isLt
      exact ⟨U, R, hTU, hR, ⟨fun he => (hne he.symm).elim, fun he => (h he).elim⟩⟩
  choose U R hTU hR hclasses using hOrbit
  have hS := weakInductionUnitaryCentralCharacter F E r m S T hT hWeak
  obtain ⟨A, hI, hA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r S
  obtain ⟨Q₀, hQ₀⟩ := S.exists_presentation_of_finiteSlice A hI hA
  have hSmall : ∃ Q : CuspidalSpectralPresentation.{uF, uV} S,
      ∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible :=
    Q₀.exists_small hQ₀
  obtain ⟨Q, hQ⟩ := hSmall
  obtain ⟨ψv, νv, ψw, νw, G, D, hG, hD, hOrders⟩ :=
    hMatch F E hPrime σ hgen v w hw r m S T Q P U R hS hT (hQ v).1 (hQ v).2 hP hR hTU hWeak
  have hPu := cuspidalUnitaryLocalUnitarity E m T hT P w.1 hP.choose hP.choose_spec.choose
  have hRu (i : Fin d) : IsUnitarizable ((R i).localComponent w.1).representation := by
    obtain ⟨e⟩ := P.nonempty_localComponent_equiv_of_galoisConjugate w (R i) hw
      (σ ^ (i : ℕ)) (hTU i) hP.choose (hR i).choose
    exact (isUnitarizable_iff_of_equiv e).mp (hPu.comp _)
  have hUpper (i : Fin d) := upper_gamma_orders (P.localComponent w.1)
    ((R i).localComponent w.1) hP (hR i) hPu (hRu i) ψw νw (D i) (hD i)
  let K := padicField v
  let Kv := K.canonicalTopologicalData
  let := Kv.topology
  let := Kv.generalLinearTopologicalGroup (r + 1)
  let π := (Q.localComponent v).padicObject (hQ v).1 (hQ v).2
  have hπ := cuspidalUnitaryLocalGenericity F r S hS Q v (hQ v).1 (hQ v).2 ψv
  have hπu := cuspidalUnitaryLocalUnitarity F r S hS Q v (hQ v).1 (hQ v).2
  have hzero (t : ℝ) (ht : 0 < meromorphicOrderAt
      (rationalSpectralValue Kv.residueCardinality G) (t : ℂ)) : t = 0 := by
    by_contra hne
    rw [hOrders t] at ht
    exact (not_lt_of_ge (Finset.sum_nonpos fun i _ => (hUpper i).1 t hne)) ht
  have hsimple : meromorphicOrderAt (rationalSpectralValue Kv.residueCardinality G) 0 = 1 := by
    have h := hOrders 0
    simp only [Complex.ofReal_zero] at h
    rw [h]
    simp_rw [fun i => (hUpper i).2, hclasses]
    simp
  have hSC := supercuspidalOfSelfPairGammaOrder (residuePrime v) K ψv νv r π.obj
    hπ hπu G hG hzero hsimple
  exact ⟨S, Q, rfl, (isSupercuspidal_iff_padicObject (Q.localComponent v) (hQ v).1 (hQ v).2).mpr hSC⟩

/-- The same argument supplies the totally complex target under the local order comparison. -/
theorem cyclicWeakInductionSupercuspidalTC_of_gammaOrder
    (hMatch : CyclicWeakInductionSelfPairGammaOrderAtUniquePlaceStatement.{uF, uE, uV, uW}) :
    CyclicWeakInductionSupercuspidalTCStatement.{uF, uE, uV, uW} :=
  cyclicWeakInductionSupercuspidalTC_of_unrestricted
    (cyclicWeakInductionSupercuspidal_of_gammaOrder hMatch)

end Langlands.Automorphic.Unramified
