import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.SingleBlockFactors
import Langlands.Representation.Parabolic.HeadTailProductInduction

/-! Finite-block gamma multiplicativity from the two-block analytic input. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- Substitute an equality of matrix ranks while retaining the representation carrier. -/
def rankCastRepresentation {F : Type uF} [Field F] {a b : ℕ}
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (h : a = b)
    (σ : Representation ℂ (GeneralLinear a F) W) :
    Representation ℂ (GeneralLinear b F) W := h ▸ σ

/-- Normalized product induction commutes with substitution of the total rank. -/
def normalizedProductRankCastEquiv
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {a b : ℕ} (C : BlockShape a) (h : a = b)
    {W : Fin C.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (C.size i) F.Carrier) (W i)) :
    (rankCastRepresentation h (T.normalizedProductInduced C σ)).Equiv
      (T.normalizedProductInduced (C.rankCast h) σ) := by
  subst b
  exact Representation.Equiv.refl _

private theorem twoBlockGamma_on_shape
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) (size : Fin 2 → ℕ) (pos : ∀ i, 0 < size i)
    (total : ∑ i, size i = t + 1) (m : Fin 2 → ℕ)
    (hs : size = fun i => m i + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (size i) F.Carrier) (W i))
    (hπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i))
        (rankCastRepresentation (congrFun hs i) (σ i))) :
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π
        (rankCastRepresentation (congrFun hs i) (σ i)) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        (F.canonicalNormalizedProductInduced ⟨2, size, pos, total⟩ σ) (∏ i, G i) := by
  subst size
  exact hTwo p F ψ ν r t m total π σ hπ hσ

private theorem exists_gamma_of_twoBlock
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r s : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (s + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType s (standardCharacter ψ s) σ) :
    ∃ G, IsPadicSymmetricGammaFactor F ψ ν.val π σ G := by
  have h : ∑ i : Fin 2, ((fun _ => s) i + 1) = (s + s + 1) + 1 := by
    simp only [Fin.sum_univ_two]
    omega
  obtain ⟨G, hG, _⟩ := hTwo p F ψ ν r (s + s + 1) (fun _ => s) h
    π (fun _ => σ) hπ (fun _ => hσ)
  exact ⟨G 0, hG 0⟩

set_option maxHeartbeats 800000 in
/-- Finite induction on the ordered block family, retaining the two analytic
inputs at the original and induced carrier universes. -/
theorem gammaMultiplicativity_of_twoBlock
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
    (hTwoLift : TwoBlockGammaMultiplicativityStatement.{uF,uV,max uF uW}) :
    GammaMultiplicativityStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r t k m h V _ _ W _ _ π σ hπ hσ
  let T := F.canonicalTopologicalData
  let := T.topology
  induction k generalizing t with
  | zero =>
      simp at h
  | succ k ih =>
      cases k with
      | zero =>
          obtain ⟨G, hG⟩ := exists_gamma_of_twoBlock hTwo p F ψ ν r (m 0) π (σ 0) hπ (hσ 0)
          refine ⟨fun _ => G, fun i => ?_, ?_⟩
          · have hi : i = 0 := Fin.eq_zero i
            subst i
            exact hG
          · simpa using (singleBlock_gamma_iff F m σ π h (fun i => (hσ i).1.1)).mpr hG
      | succ k =>
          let B := succBlockShape m h
          let tailM : Fin (k + 1) → ℕ := fun j => m j.succ
          have hpos : 0 < ∑ j : Fin (k + 1), (tailM j + 1) := by
            apply Finset.sum_pos
            · intro j _
              exact Nat.succ_pos _
            · exact Finset.univ_nonempty
          obtain ⟨s, hs⟩ : ∃ s, (∑ j : Fin (k + 1), (tailM j + 1)) = s + 1 :=
            ⟨(∑ j : Fin (k + 1), (tailM j + 1)) - 1, by omega⟩
          let tailσ := fun j : Fin (k + 1) => σ j.succ
          obtain ⟨Gt, hGt, hIt⟩ := ih s tailM hs (W := fun j => W j.succ)
            tailσ (fun j => hσ j.succ)
          have htype := normalizedProductWhittakerType p F ψ s (k + 1) tailM hs
            tailσ (fun j => hσ j.succ)
          let bundled := fun i => SmoothRep.of (σ i) (hσ i).1.1
          let outer := T.headTailProductFactors B rfl bundled
          let C := B.headTailShape rfl
          let outerM : Fin 2 → ℕ := Fin.cases (m 0) (fun _ => s)
          have hsize : C.size = fun i => outerM i + 1 := by
            funext i
            fin_cases i
            · rfl
            · exact hs
          let et := normalizedProductRankCastEquiv T (B.tailShape rfl) hs tailσ
          have houter : ∀ i, IsOfWhittakerType (outerM i) (standardCharacter ψ (outerM i))
              (rankCastRepresentation (congrFun hsize i) (outer i).representation) := by
            intro i
            fin_cases i
            · exact (hσ 0).of_equiv (universeLiftEquiv.{uF} (σ 0))
            · exact htype.of_equiv et.symm
          obtain ⟨H, hH, hI⟩ := twoBlockGamma_on_shape hTwoLift p F ψ ν r t C.size
            C.positive C.sum_eq outerM hsize π (fun i => (outer i).representation) hπ houter
          have hhead : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) (H 0) :=
            (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π)
              (universeLiftEquiv.{uF} (σ 0))).mpr (hH 0)
          have htail : H 1 = ∏ j, Gt j :=
            ((IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π) et).mp
              (hH 1)).unique hIt
          refine ⟨Fin.cons (H 0) Gt, ?_, ?_⟩
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hhead
            · exact hGt j
          · have hprod : (∏ i : Fin 2, H i) =
                ∏ i : Fin (k + 2), Fin.cons (H 0) Gt i := by
              rw [Fin.prod_univ_two, Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [htail]
            rw [← hprod]
            exact (IsPadicSymmetricGammaFactor.congr_equiv
              (Representation.Equiv.refl π)
              (T.headTailProductInductionEquiv B rfl bundled)).mpr hI

end Langlands.RankinSelberg
