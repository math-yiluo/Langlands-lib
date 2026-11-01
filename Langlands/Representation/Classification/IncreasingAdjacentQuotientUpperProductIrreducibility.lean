import Langlands.Representation.Classification.AdjacentQuotientUpperProductFirstDerivative
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Induction.ThreeFactorProductPresentation
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Mathlib.Data.Nat.Find

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.AdjacentUpperIrreducibility

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A proper highest derivative must have common-rank order d or 2d. -/
theorem eq_d_or_two_d_of_dvd {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hkn : k < (d+d)+d) (hdiv : d ∣ k) : k = d ∨ k = d+d := by
  obtain ⟨t,ht⟩ := hdiv
  have htpos : 0 < t := by nlinarith
  have htlt : t < 3 := (Nat.mul_lt_mul_left hd).mp (by nlinarith : d*t < d*3)
  have ht12 : t = 1 ∨ t = 2 := by omega
  rcases ht12 with rfl | rfl
  · left
    simpa using ht
  · right
    nlinarith

/-- Finite length and upper-datum occurrence in each possibly nonzero proper
derivative exclude a proper highest derivative by the actual support shift. -/
theorem top_nontrivial_of_upper_derivative_support {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (M : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((d+d)+d) F.Carrier))
      (ρ : CuspidalDatum.{max uF uV,uF} T),
      (∀ (k : ℕ) (hk : k ≤ (d+d)+d), k = d ∨ k = d+d →
        ((generalLinearDerivative T ψ ((d+d)+d) k hk).obj M).HasFiniteLength) →
      (∀ (k : ℕ) (hk : k ≤ (d+d)+d), k = d ∨ k = d+d →
        ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (((d+d)+d)-k) F.Carrier),
          D.IsIrreducible → SmoothRep.IsSubquotient D
            ((generalLinearDerivative T ψ ((d+d)+d) k hk).obj M) →
          ∃ s : Multiset (CuspidalDatum.{max uF uV,uF} T),
            T.IsSupercuspidalSupport D s ∧ ρ.twist 1 ∈ s) →
      ∀ ω : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((d+d)+d) F.Carrier),
        ω.IsIrreducible → SmoothRep.IsSubquotient ω M →
        T.IsSupercuspidalSupport ω (RepeatedCuspidalSupport.pairSupport T ρ 2 1) →
        NondivisibleProperDerivativeVanishing T d ω →
        Nontrivial ((generalLinearDerivative T ψ ((d+d)+d) ((d+d)+d) le_rfl).obj ω) := by
  classical
  let := T.topology
  intro M ρ hfinite hupper ω hω hωM hsω hvan
  let N := (d+d)+d
  let P : ℕ → Prop := fun k => ∃ hk : k ≤ N,
    Nontrivial ((generalLinearDerivative T ψ N k hk).obj ω)
  have hP₀ : P 0 := ⟨Nat.zero_le N,
    SupercuspidalTopDerivative.nontrivial_of_isIrreducible ω.representation hω⟩
  let k := Nat.findGreatest P N
  have hk : k ≤ N := Nat.findGreatest_le N
  obtain ⟨hk',hnt⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP₀
  have hnt : Nontrivial ((generalLinearDerivative T ψ N k hk).obj ω) := hnt
  have hhigh : ∀ (j : ℕ) (hj : j ≤ N), k < j →
      Subsingleton ((generalLinearDerivative T ψ N j hj).obj ω) := by
    intro j hj hkj
    apply not_nontrivial_iff_subsingleton.mp
    intro hne
    exact Nat.findGreatest_is_greatest hkj hj ⟨hj,hne⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro hzero
  have hkn : k < N := by
    by_contra h
    have heq : k = N := by omega
    have key : ∀ (i : ℕ) (hi : i ≤ N), i = N →
        Nontrivial ((generalLinearDerivative T ψ N i hi).obj ω) →
        Nontrivial ((generalLinearDerivative T ψ N N le_rfl).obj ω) := by
      intro i hi he
      subst i
      exact id
    exact (not_nontrivial_iff_subsingleton.mpr hzero) (key k hk heq hnt)
  have hkpos : 0 < k := highestGeneralLinearDerivativeOrder_pos T ψ
    (by dsimp [N]; omega) hk ω hnt hhigh
  have hdiv : d ∣ k := by
    by_contra hdiv
    exact (not_nontrivial_iff_subsingleton.mpr (hvan ψ k hk hkpos hkn hdiv)) hnt
  have hk12 : k = d ∨ k = d+d := eq_d_or_two_d_of_dvd hd hkpos hkn hdiv
  let J := generalLinearDerivative.{uF,max uF uV} T ψ N k hk
  have hJ := generalLinearDerivativeExactness.{uF,max uF uV} F T ψ N k hk
  have hsub : SmoothRep.IsSubquotient (J.obj ω) (J.obj M) :=
    ExactSmoothTransport.map_isSubquotient J hJ hωM
  have hfin : (J.obj ω).HasFiniteLength :=
    SmoothRep.hasFiniteLength_of_isSubquotient (hfinite k hk hk12) hsub
  let : Nontrivial (J.obj ω) := hnt
  obtain ⟨D,hD,j,hj⟩ :=
    AdjacentQuotientUpperProductFirstDerivative.exists_irreducible_subrepresentation
      (J.obj ω) hfin
  have hDj : SmoothRep.IsSubquotient D (J.obj ω) :=
    (show SmoothRep.IsSubrepresentation D (J.obj ω) from ⟨SmoothRep.ofHom j,hj⟩).isSubquotient
  have hDM := smoothSubquotientTransitivity ℂ _ (J.obj M) (J.obj ω) D hDj hsub
  obtain ⟨s,hs,hmem⟩ := hupper k hk hk12 D hD hDM
  have hshift := highestDerivativeSupportShift.{uF,max uF uV} F T ψ N ω k hk
    hω hnt hhigh D ⟨hD,j,hj⟩ _ s hsω hs
  exact (RepeatedCuspidalSupport.upper_not_mem_of_shift_le T ρ 2 1 s hshift) hmem

/-- A supplied actual support presentation passes to each irreducible actual
subquotient by composing the actual subquotient relations. -/
theorem support_of_irreducible_subquotient {n : ℕ} :
    letI := T.topology
    ∀ (X D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (s : Multiset (CuspidalDatum.{max uF uV,uF} T)),
      T.IsSupercuspidalSupport X s → D.IsIrreducible →
      SmoothRep.IsSubquotient D X → T.IsSupercuspidalSupport D s := by
  let := T.topology
  intro X D s hs hD hDX
  obtain ⟨k,ρ,hρ,h,A,hA,hX,hXP⟩ := hs
  exact ⟨k,ρ,hρ,h,A,hA,hD,
    smoothSubquotientTransitivity ℂ _ (T.cuspidalProductInduced ρ h A) X D hDX hXP⟩

/-- Each possibly nonzero proper common-rank derivative has finite length and
all of its irreducible actual constituents have a support containing A. -/
theorem proper_derivative_data {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let M := (T.binaryNormalizedProductFunctor (d+d) d).obj (SmoothRep.quotient P S,A.obj)
        (∀ (k : ℕ) (hk : k ≤ (d+d)+d), k = d ∨ k = d+d →
          ((generalLinearDerivative T ψ ((d+d)+d) k hk).obj M).HasFiniteLength) ∧
        (∀ (k : ℕ) (hk : k ≤ (d+d)+d), k = d ∨ k = d+d →
          ∀ D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (((d+d)+d)-k) F.Carrier),
            D.IsIrreducible → SmoothRep.IsSubquotient D
              ((generalLinearDerivative T ψ ((d+d)+d) k hk).obj M) →
            ∃ s : Multiset (CuspidalDatum.{max uF uV,uF} T),
              T.IsSupercuspidalSupport D s ∧ (⟨d,hd,A.isoClass⟩ : CuspidalDatum T) ∈ s) := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁ M
  have hfirst := increasingAdjacentQuotientUpperProductFirstDerivative.{uF,uV}
    F T ψ d hd B A hAB S hS₀ hS₁
  have hsecond := increasingAdjacentQuotientUpperProductSecondDerivative.{uF,uV}
    F T ψ d hd B A hAB S hS₀ hS₁
  constructor
  · intro k hk hk12
    rcases hk12 with rfl | rfl
    · exact hfirst.1
    · exact hsecond.1
  · intro k hk hk12
    rcases hk12 with rfl | rfl
    · exact hfirst.2
    · intro D hD hDM
      let cA : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,A.isoClass⟩
      refine ⟨{cA},?_,by simp [cA]⟩
      apply AdjacentQuotientUpperProductFirstDerivative.support_of_subquotient_rankCast
        T _ A.obj {cA} _ D hD (hsecond.2 D hD hDM)
      intro E hE hEA
      exact support_of_irreducible_subquotient T A.obj E {cA}
        (TwoSupercuspidalTopDerivatives.supercuspidal_singleton_support T hd A) hE hEA

/-- An actual supercuspidal-product presentation with the required displayed
multiset suffices for irreducibility of Q × A. The presentation itself is an
actual subquotient relation, not an irreducibility or classification premise. -/
theorem irreducible_of_product_presentation {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (C : BlockShape ((d+d)+d)) (hdiv : ∀ i, d ∣ C.size i) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      ∀ (CA : ∀ i, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := C.size i)),
      (List.ofFn (fun i => (⟨C.size i,C.positive i,(CA i).isoClass⟩ :
        CuspidalDatum.{max uF uV,uF} T)) : Multiset _) =
        RepeatedCuspidalSupport.pairSupport T (⟨d,hd,B.isoClass⟩ : CuspidalDatum T) 2 1 →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let M := (T.binaryNormalizedProductFunctor (d+d) d).obj (SmoothRep.quotient P S,A.obj)
        SmoothRep.IsSubquotient M
          ((T.normalizedProductInductionFunctor C).obj (fun i => (CA i).obj)) →
        M.IsIrreducible := by
  let := T.topology
  intro B A hAB CA hCA P S hS₀ hS₁ M hMP
  let ρ : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,B.isoClass⟩
  let cA : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,A.isoClass⟩
  have hcA : cA = ρ.twist 1 := congrArg (CuspidalDatum.mk d hd) hAB
  have hdata := proper_derivative_data.{uF,uV} T hd ψ B A hAB S hS₀ hS₁
  let J := generalLinearDerivative.{uF,max uF uV} T ψ ((d+d)+d) ((d+d)+d) le_rfl
  apply ExactFunctorIrreducibility.isIrreducible_of_finrank_obj_eq_one J
    (generalLinearDerivativeExactness.{uF,max uF uV} F T ψ _ _ le_rfl) M
    (AdjacentQuotientUpperProductFirstDerivative.binary_finite_length T (by omega) hd
      (SmoothRep.quotient P S) A.obj
      (AdjacentQuotientUpperProductFirstDerivative.quotient_irreducible.{uF,uV}
        T hd B A hAB S hS₀ hS₁) A.property.1)
  · intro ω hω hωM
    have hωP := smoothSubquotientTransitivity ℂ _
      ((T.normalizedProductInductionFunctor C).obj (fun i => (CA i).obj)) M ω hωM hMP
    have hsω := TwoSupercuspidalTopDerivatives.support_of_product_subquotient
      T C CA ω hω hωP
    rw [hCA] at hsω
    apply top_nontrivial_of_upper_derivative_support.{uF,uV} T hd ψ M ρ hdata.1 _
      ω hω hωM hsω
      (supercuspidal_product_subquotient_nondivisible_derivatives T (by omega) C hdiv CA ω hωP)
    intro k hk hk12 D hD hDM
    obtain ⟨s,hs,hm⟩ := hdata.2 k hk hk12 D hD hDM
    exact ⟨s,hs,by simpa only [← hcA] using hm⟩
  · exact AdjacentQuotientUpperProduct.increasing_quotient_upper_product_top.{uF,uV}
      T hd ψ B A hAB S hS₀ hS₁

/-- An actual product presentation after transport of the ambient source rank
is the corresponding actual presentation over the transported block shape. -/
theorem subquotient_product_of_rankCast {m n : ℕ} (h : m=n) (C : BlockShape n) :
    letI := T.topology
    ∀ (CA : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
      (M : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)),
      SmoothRep.IsSubquotient ((generalLinearRankCast T h).obj M)
        ((T.normalizedProductInductionFunctor C).obj CA) →
      SmoothRep.IsSubquotient M
        ((T.normalizedProductInductionFunctor (C.rankCast h.symm)).obj CA) := by
  subst h
  exact fun _ _ hs => hs

/-- The actual quotient presentation of B × A × A discharges the final
presentation input of the derivative argument. -/
theorem increasing_quotient_upper_product_irreducible {d : ℕ} (hd : 0 < d)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        ((T.binaryNormalizedProductFunctor (d+d) d).obj
          (SmoothRep.quotient P S,A.obj)).IsIrreducible := by
  let := T.topology
  intro B A hAB P S hS₀ hS₁
  let C := Parabolic.threeBlocksRight d d d hd hd hd
  let CA : ∀ i, SupercuspidalRep.{uF,max uF uV}
      (F := F.Carrier) (n := C.size i) :=
    Fin.cases B (Fin.cases A (Fin.cases A finZeroElim))
  have hdiv : ∀ i, d ∣ C.size i := by
    intro i
    fin_cases i <;> exact dvd_rfl
  have hCA : (List.ofFn (fun i => (⟨C.size i,C.positive i,(CA i).isoClass⟩ :
      CuspidalDatum.{max uF uV,uF} T)) : Multiset _) =
      RepeatedCuspidalSupport.pairSupport T (⟨d,hd,B.isoClass⟩ : CuspidalDatum T) 2 1 := by
    let ρ : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,B.isoClass⟩
    let cA : CuspidalDatum.{max uF uV,uF} T := ⟨d,hd,A.isoClass⟩
    have hcA : cA = ρ.twist 1 := congrArg (CuspidalDatum.mk d hd) hAB
    change ({ρ,cA,cA} : Multiset _) = RepeatedCuspidalSupport.pairSupport T ρ 2 1
    rw [hcA]
    change ({ρ} : Multiset _) + (ρ.twist 1 ::ₘ {ρ.twist 1}) =
      (ρ.twist 1 ::ₘ {ρ.twist 1}) + {ρ}
    exact add_comm _ _
  apply irreducible_of_product_presentation.{uF,uV} T hd ψ C hdiv
    B A hAB CA hCA S hS₀ hS₁
  have hfam : (fun i => (CA i).obj) = Parabolic.threeBlockSmoothFamily B.obj A.obj A.obj := by
    funext i
    fin_cases i <;> rfl
  rw [hfam]
  exact (Parabolic.binaryRightProduct_isQuotient_threeBlocksRight.{uF,uV} F T hd hd hd
    B.obj A.obj A.obj (SmoothRep.quotient P S) (SmoothRep.quotient_isQuotient S)).isSubquotient

end Langlands.Classification.AdjacentUpperIrreducibility

namespace Langlands.Classification

open GeneralLinear

universe uF uV

/-- A supplied proper quotient of the increasing adjacent product B × A
remains irreducible after taking its normalized product with A = νB. -/
def IncreasingAdjacentQuotientUpperProductIrreducibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      ((T.binaryNormalizedProductFunctor (d+d) d).obj
        (SmoothRep.quotient P S,A.obj)).IsIrreducible

/-- The supplied-quotient upper-factor irreducibility theorem has no
additive-character or product-presentation premise. -/
theorem increasingAdjacentQuotientUpperProductIrreducibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IncreasingAdjacentQuotientUpperProductIrreducibility.{uF,uV} F T := by
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  intro d hd
  exact AdjacentUpperIrreducibility.increasing_quotient_upper_product_irreducible.{uF,uV} T hd ψ

end Langlands.Classification
