import Langlands.Automorphic.LocalArithmeticTransport
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement
import Langlands.Automorphic.Unramified.WeakInductionUniqueness
import Langlands.BaseChange.CyclicLocalInduction
import Langlands.Global.FiniteCompletionLocalField

/-! # Reduction of unique-place supercuspidality to local induction and matching -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.BaseChange

/-- A generator of a finite Galois field extension presents it as a cyclic
algebra of degree equal to its field degree. -/
theorem isCyclicAlgebra_of_galois_generator
    {K : Type uF} {L : Type uE} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    IsCyclicAlgebra σ (Module.finrank K L) := by
  refine ⟨inferInstance, rfl, inferInstance,
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L), ?_⟩
  intro x hx
  apply (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) x).mpr
  intro τ
  have hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) x := hx
  exact (Subgroup.zpowers_le.mpr hσ) (hgen τ)

/-- Henniart--Herb Proposition 5.5 for the local cyclic induction
characterization of Henniart (2012), Theorem 6, in prime degree. -/
def CyclicLocalInductionSupercuspidalCriterionStatement : Prop :=
  ∀ (K : Type uF) (L : Type uE) [Field K] [Field L] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (d : ℕ),
    d.Prime → IsCyclicAlgebra σ d →
    ∀ (r m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear (r + 1) K) V)
      (τ : Representation ℂ (GeneralLinear (m + 1) L) W),
      GeneralLinear.IsSupercuspidal τ →
      HasTrivialGaloisStabilizer K τ →
      IsCyclicLocalInductionOf σ d π τ →
      GeneralLinear.IsSupercuspidal π

open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension

/-- The local criterion over the actual completions at a pair of finite places. -/
def CyclicLocalInductionSupercuspidalAtCompletionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal],
    let := FiniteCompletion.valuativeRel v
    let := FiniteCompletion.valuativeRel w
    have := FiniteCompletion.isNonarchimedeanLocalField v
    have := FiniteCompletion.isNonarchimedeanLocalField w
    ∀ (σ : FiniteCompletion E w ≃ₐ[FiniteCompletion F v] FiniteCompletion E w)
      (d : ℕ), d.Prime → IsCyclicAlgebra σ d →
      ∀ (r m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) (FiniteCompletion F v)) V)
        (τ : Representation ℂ (GeneralLinear (m + 1) (FiniteCompletion E w)) W),
        GeneralLinear.IsSupercuspidal τ →
        HasTrivialGaloisStabilizer (FiniteCompletion F v) τ →
        IsCyclicLocalInductionOf σ d π τ →
        GeneralLinear.IsSupercuspidal π

end Langlands.BaseChange

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality
open CuspidalOperatorRealization
open scoped NumberField FiniteExtension

section LocalRealization

variable {K : Type uF} [Field K] [NumberField K] {r : ℕ} {v : FinitePlace K}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance (A : LocalRealization K (r + 1) v) : AddCommGroup A.Space := Submodule.addCommGroup _

namespace LocalRealization

private theorem padicClass_isSupercuspidal_iff
    (A : LocalRealization K (r + 1) v) (hI : A.IsIrreducible) (hA : A.IsAdmissible) :
    Correspondence.IsSupercuspidalClass (CompletionPadic.padicField v) (A.padicClass hI hA) ↔
      GeneralLinear.IsSupercuspidal (F := FiniteCompletion K v) (n := r + 1) A.representation := by
  let Kv := CompletionPadic.padicField v
  let : TopologicalSpace Kv.Carrier := Kv.canonicalTopologicalData.topology
  let B := A.padicObject hI hA
  have ht := congrArg (fun t : TopologicalSpace (FiniteCompletion K v) =>
    @GeneralLinear.IsSupercuspidal (FiniteCompletion K v) _ t (r + 1) _ _ _ A.representation)
    (CompletionPadic.completion_topology_eq v)
  refine Iff.trans ?_ (iff_of_eq ht.symm)
  constructor
  · rintro ⟨c, hc⟩
    revert hc
    refine Quotient.inductionOn c ?_
    intro C hC
    change Correspondence.automorphicClassOf Kv C.toIrreducibleAdmissible =
      Correspondence.automorphicClassOf Kv B at hC
    obtain ⟨e⟩ := (Correspondence.automorphicClassOf_eq_iff Kv _ _).mp hC
    exact GeneralLinear.isSupercuspidal_of_equiv e C.property.2
  · intro h
    let C : GeneralLinear.SupercuspidalRep (F := Kv.Carrier) (n := r + 1) := ⟨B.obj, hI, h⟩
    exact ⟨C.isoClass, rfl⟩

/-- The supercuspidal class condition on a local factor is the irreducibility
and Jacquet-vanishing condition on its original representation. -/
theorem isSupercuspidal_iff_representation (A : LocalRealization K (r + 1) v) :
    A.IsSupercuspidal ↔ A.IsIrreducible ∧
      GeneralLinear.IsSupercuspidal (F := FiniteCompletion K v) (n := r + 1) A.representation := by
  constructor
  · rintro ⟨hI, hA, h⟩
    exact ⟨hI, (A.padicClass_isSupercuspidal_iff hI hA).mp h⟩
  · rintro ⟨hI, h⟩
    exact ⟨hI, h.1, (A.padicClass_isSupercuspidal_iff hI h.1).mpr h⟩

end LocalRealization

end LocalRealization

namespace Unramified

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance {v : FinitePlace K} (A : LocalRealization K n v) : AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- At a unique finite place in prime degree, a unitary regular source with
a supercuspidal factor has a cuspidal weak induction whose indicated local
factor satisfies the local cyclic induction characterization. -/
def CyclicInductionMatchingAtUniquePlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v) (hw : ∀ w' : FinitePlacesAbove E v, w' = w)
      (r m : ℕ) (T : CuspidalOperatorRealization E m)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      r + 1 = (m + 1) * Module.finrank F E →
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      ∃ (U : CuspidalOperatorRealization F r) (Q : CuspidalSpectralPresentation.{uF, uV} U),
        U.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass ∧
        let : w.1.asIdeal.LiesOver v.asIdeal := w.2
        let := FiniteCompletion.valuativeRel v
        let := FiniteCompletion.valuativeRel w.1
        have := FiniteCompletion.isNonarchimedeanLocalField v
        have := FiniteCompletion.isNonarchimedeanLocalField w.1
        BaseChange.IsCyclicLocalInductionOf (uniquePlaceCompletionAutEquiv w hw σ)
          (Module.finrank F E) (Q.localComponent v).representation (P.localComponent w.1).representation

private theorem isCyclicAlgebra_uniquePlace
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] {v : FinitePlace F} (w : FinitePlacesAbove E v)
    (hw : ∀ w' : FinitePlacesAbove E v, w' = w) (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) :
    let : w.1.asIdeal.LiesOver v.asIdeal := w.2
    BaseChange.IsCyclicAlgebra (uniquePlaceCompletionAutEquiv w hw σ) (Module.finrank F E) := by
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let e := uniquePlaceCompletionAutEquiv w hw
  have : IsGalois (FiniteCompletion F v) (FiniteCompletion E w.1) := isGalois_adicCompletion v w.1
  rw [← localDegree_eq_global_of_unique w hw]
  apply BaseChange.isCyclicAlgebra_of_galois_generator
  intro τ
  obtain ⟨i, hi⟩ := hgen (e.symm τ)
  use i
  change σ ^ i = e.symm τ at hi
  change e σ ^ i = τ
  exact (map_zpow e σ i).symm.trans ((congrArg e hi).trans (e.apply_symm_apply τ))

set_option maxHeartbeats 1000000 in
/-- Matched induction, the criterion at finite completions and cuspidal
Euler rigidity imply the unique-place consequence. -/
theorem cyclicWeakInductionSupercuspidal_of_matching_at_completion
    (hMatch : CyclicInductionMatchingAtUniquePlaceStatement.{uF, uE, uV, uW})
    (hLocal : BaseChange.CyclicLocalInductionSupercuspidalAtCompletionStatement.{uF, uE, uF, uE})
    (hRig : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ _ hPrime σ hgen v w hw r m S T P hunit hP hconj hweak
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have hP' := (P.localComponent w.1).isSupercuspidal_iff_representation.mp hP
  have hreg (i : ℕ) (hi : 0 < i) (hdeg : i < Module.finrank F E) :
      ¬ T.isoClass.IsGaloisStable (σ ^ i) := by
    obtain ⟨U, Q, hTU, hQ, hne⟩ := hconj i hi hdeg
    exact CuspidalSpectralPresentation.not_isGaloisStable_of_localComponent_isoClass_ne
      w P Q (σ ^ i) hTU hP'.1 hQ.choose hne
  have hstab := CuspidalSpectralPresentation.hasTrivialGaloisStabilizer_of_distinct_conjugates
    w P hw σ hgen hP'.1 (fun i hi hdeg => by
      obtain ⟨U, Q, hTU, hQ, hne⟩ := hconj i hi hdeg
      exact ⟨U, Q, hTU, hQ.choose, hne⟩)
  obtain ⟨U, Q, hweak', hlocal⟩ :=
    hMatch F E hPrime σ hgen v w hw r m T P hweak.rank_eq hunit hP hreg
  have hQ := hLocal F E v w.1
    (uniquePlaceCompletionAutEquiv w hw σ) (Module.finrank F E) hPrime
    (isCyclicAlgebra_uniquePlace w hw σ hgen) r m _ _
    (Q.localComponent v).representation (P.localComponent w.1).representation hP'.2 hstab hlocal
  obtain ⟨ψ, hψ⟩ := hlocal.2.2.1
  have hclasses := weakInductionUniqueness_of_cuspidalEulerConstituentRecovery hRig
    F E r m U.isoClass S.isoClass T.isoClass hweak' hweak
  exact ⟨U, Q, hclasses, (Q.localComponent v).isSupercuspidal_iff_representation.mpr ⟨hψ.1, hQ⟩⟩

/-- The criterion over local fields specializes to the actual completions. -/
theorem cyclicWeakInductionSupercuspidal_of_matching
    (hMatch : CyclicInductionMatchingAtUniquePlaceStatement.{uF, uE, uV, uW})
    (hLocal : BaseChange.CyclicLocalInductionSupercuspidalCriterionStatement.{uF, uE, uF, uE})
    (hRig : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW} := by
  apply cyclicWeakInductionSupercuspidal_of_matching_at_completion hMatch ?_ hRig
  intro F E _ _ _ _ _ v w _
  let := FiniteCompletion.valuativeRel v
  let := FiniteCompletion.valuativeRel w
  have := FiniteCompletion.isNonarchimedeanLocalField v
  have := FiniteCompletion.isNonarchimedeanLocalField w
  have : CharZero (FiniteCompletion F v) :=
    charZero_of_injective_algebraMap (algebraMap F (FiniteCompletion F v)).injective
  exact hLocal (FiniteCompletion F v) (FiniteCompletion E w)

/-- The unrestricted statement specializes to the totally complex input by
introducing the additional base-field instance. -/
theorem cyclicWeakInductionSupercuspidalTC_of_unrestricted
    (h : CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW}) :
    CyclicWeakInductionSupercuspidalTCStatement.{uF, uE, uV, uW} :=
  fun F E _ _ _ => h F E

end Unramified
end Langlands.Automorphic
