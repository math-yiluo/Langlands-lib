import Langlands.Shimura.Unitary.SplitProfileInvolution
import Langlands.Shimura.Unitary.SplitFactorCharts
import Langlands.Shimura.Unitary.LocalHermitianWitt
import Langlands.Shimura.Unitary.RealSignatureTwist

/-! # Global realization of odd-degree unitary local profiles -/

noncomputable section

universe u v w w'

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local
open scoped TensorProduct

variable {K : Type v} [Field K] [NumberField K]

private theorem hasCompletedBrauerInvariant_of_equiv
    {A : Type w} {B : Type w'} [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (q : Langlands.Global.FinitePlace K) {x : RationalModIntegers}
    (h : HasCompletedBrauerInvariant K B q x) : HasCompletedBrauerInvariant K A q x := by
  obtain ⟨C, ⟨f⟩, h⟩ := h
  let g : CompletedAlgebra K A q ≃ₐ[FiniteCompletion K q] CompletedAlgebra K B q :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  exact ⟨C, ⟨g.trans f⟩, h⟩

variable {E : Type u} [Field E] [NumberField E] [IsTotallyReal E]
  [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]

/-- A single realized profile on the given global CM extension, with actual
real and finite chart predicates and the prescribed signed Brauer values. -/
structure UnitaryLocalProfileWitness {n : ℕ} (hn : 0 < n)
    {s : Finset (Langlands.Global.FinitePlace E)}
    (positive : ∀ p : s, FinitePlacesAbove K p.val) (a : s → ZMod n)
    (r : (E →+* ℝ) → ℕ) where
  (carrier : Type (max u v))
  [ring : Ring carrier]
  [baseAlgebra : Algebra E carrier]
  [centerAlgebra : Algebra K carrier]
  [tower : IsScalarTower E K carrier]
  data : CentralSimpleUnitaryData E K carrier n
  signatures (τ : E →+* ℝ) : HasSignature data.toSecondKindInvolution τ n (r τ)
  maximalWitt (p : Langlands.Global.FinitePlace E) (hp : p ∉ s) :
    IsQuasiSplitAt data.toSecondKindInvolution n p
  signedBrauer (p : s) (q : FinitePlacesAbove K p.val) :
    HasCompletedBrauerInvariant K carrier q.val
      (denominatorEquiv n hn (by classical exact if q = positive p then a p else -a p))

/-- Realize the complete signed split Brauer and real signature profile in odd
rank, with maximal-Witt charts at every unselected finite place. -/
def realizeOddUnitaryLocalProfile {n : ℕ} (hn : 1 < n) (ho : Odd n)
    {s : Finset (Langlands.Global.FinitePlace E)} (hs : ∀ p : s, IsSplitPlace E K p.val)
    (positive : ∀ p : s, FinitePlacesAbove K p.val) (a : s → ZMod n)
    (r : (E →+* ℝ) → ℕ) (hr : ∀ τ, r τ ≤ n) :
    UnitaryLocalProfileWitness (lt_trans Nat.zero_lt_one hn) positive a r := by
  classical
  let hn₀ := lt_trans Nat.zero_lt_one hn
  let h := exists_csa_with_involution_for_splitProfile hn₀ hs positive a
  let B := h.choose
  have hB := h.choose_spec
  let A := ULift.{u} B
  let : Algebra E A := Algebra.compHom A (algebraMap E K)
  let : IsScalarTower E K A := IsScalarTower.of_algebraMap_eq' rfl
  let e : A ≃ₐ[K] B := ULift.algEquiv
  let τ := hB.2.1.choose
  have hτ : IsUnitaryInvolution (cmConjugation E K) τ := hB.2.1.choose_spec
  let t (x : A) := e.symm (τ (e x))
  have ht : IsUnitaryInvolution (cmConjugation E K) t := by
    refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_, fun z => ?_⟩
    · simp only [t, map_add, hτ.1]
    · simp only [t, map_mul, hτ.2.1]
    · simp only [t, AlgEquiv.apply_symm_apply, hτ.2.2.1, AlgEquiv.symm_apply_apply]
    · change e.symm (τ (e (algebraMap K A z))) = algebraMap K A (cmConjugation E K z)
      have hz : τ (algebraMap K B z) = algebraMap K B (cmConjugation E K z) := hτ.2.2.2 z
      rw [e.commutes, hz, e.symm.commutes]
  have hdim : Module.finrank K A = n ^ 2 := by
    rw [e.toLinearEquiv.finrank_eq, pow_two]
    exact hB.1
  let D : CentralSimpleUnitaryData E K A n :=
    { toSecondKindInvolution := SecondKindInvolution.ofUnitaryInvolution t ht
      rank_gt_one := hn
      central := ⟨fun x hx => by
        have hb : e x ∈ Subalgebra.center K B := (MulEquivClass.apply_mem_center_iff e).mpr hx
        obtain ⟨z, hz⟩ := (Algebra.IsCentral.mem_center_iff K).mp hb
        rw [Algebra.mem_bot]
        exact ⟨z, e.injective ((e.commutes z).trans hz.symm)⟩⟩
      simple := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
      finite := e.symm.toLinearEquiv.finiteDimensional
      dimension := hdim }
  let σ := realSignatureTwist D r hr
  let D' : CentralSimpleUnitaryData E K A n := { D with toSecondKindInvolution := σ.val }
  refine ⟨A, D', σ.property, ?_, fun p q => ?_⟩
  · intro p hp
    have hz (q : FinitePlacesAbove K p) : HasCompletedBrauerInvariant K A q.val 0 :=
      hasCompletedBrauerInvariant_of_equiv e q.val (hB.2.2.2 p hp q)
    by_cases hsplit : IsSplitPlace E K p
    · exact hsplit.some.isQuasiSplitAt_of_zeroCompletedBrauerInvariant (placeAbove K p) D'
        (hz (placeAbove K p))
    · exact isQuasiSplitAt_of_odd_nonsplit p hsplit D' ho hz
  · exact hasCompletedBrauerInvariant_of_equiv e q.val (hB.2.2.1 p q)

end Langlands.Shimura.FiniteUnitary
