import Langlands.Shimura.Unitary.OddUnitaryLocalProfile

/-! # Transport of a unitary profile to a lifted carrier -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local
open scoped TensorProduct

universe u v w

section BaseChange

variable {E : Type u} {A : Type v} {B : Type w} {S : Type*}
  [CommRing E] [Ring A] [Ring B] [Algebra E A] [Algebra E B]
  [CommRing S] [Algebra E S]

private theorem baseChange_transport (σ : AlgebraInvolution E A) (e : B ≃ₐ[E] A)
    (x : S ⊗[E] B) :
    let T := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e
    T ((σ.transport e.symm).baseChange S x) = σ.baseChange S (T x) := by
  let T := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e
  change T ((σ.transport e.symm).baseChange S x) = σ.baseChange S (T x)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    change s ⊗ₜ[E] e (e.symm (σ (e a))) = s ⊗ₜ[E] σ (e a)
    rw [e.apply_symm_apply]

end BaseChange

section Carrier

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
  {s : Finset (Langlands.Global.FinitePlace E)} (positive : ∀ p : s, FinitePlacesAbove K p.val)
  (a : s → ZMod n) (r : (E →+* ℝ) → ℕ)

set_option maxRecDepth 4096 in
/-- Transport a fully realized profile to a carrier in the joint field universe,
with the prescribed equivalences on the actual scalar extensions. -/
def unitaryLocalProfileWitnessOfAlgebra
    (hr : ∀ τ, HasSignature D.toSecondKindInvolution τ n (r τ))
    (hW : ∀ p ∉ s, IsQuasiSplitAt D.toSecondKindInvolution n p)
    (hB : ∀ (p : s) (q : FinitePlacesAbove K p.val), HasCompletedBrauerInvariant K A q.val
      (denominatorEquiv n hn (by classical exact if q = positive p then a p else -a p))) :
    UnitaryLocalProfileWitness hn positive a r := by
  classical
  let B := ULift.{u} A
  let e : B ≃ₐ[K] A := ULift.algEquiv
  let f := e.restrictScalars E
  let σ : SecondKindInvolution E K B :=
    { involution := D.involution.transport f.symm
      onCenter := fun k => by
        change e.symm (D.involution (e (algebraMap K B k))) = algebraMap K B (cmConjugation E K k)
        rw [e.commutes, D.onCenter, e.symm.commutes] }
  let : FiniteDimensional K A := D.finite
  let : Algebra.IsCentral K A := D.central
  let D' : CentralSimpleUnitaryData E K B n :=
    { toSecondKindInvolution := σ
      rank_gt_one := D.rank_gt_one
      central := ⟨fun x hx => by
        have he : e x ∈ Subalgebra.center K A := (MulEquivClass.apply_mem_center_iff e).mpr hx
        obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp he
        rw [Algebra.mem_bot]
        exact ⟨k, e.injective ((e.commutes k).trans hk.symm)⟩⟩
      simple := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv D.simple
      finite := e.symm.toLinearEquiv.finiteDimensional
      dimension := e.toLinearEquiv.finrank_eq.trans D.dimension }
  refine ⟨B, D', ?_, ?_, ?_⟩
  · intro τ
    let : Algebra E ℝ := τ.toAlgebra
    obtain ⟨hτ, g, hg⟩ := hr τ
    let T := Algebra.TensorProduct.congr (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) f
    refine ⟨hτ, T.trans g, fun x => ?_⟩
    exact (congrArg g (baseChange_transport D.involution f x)).trans (hg (T x))
  · intro p hp
    let F := FiniteCompletion E p
    let T := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) f
    obtain ⟨g, hcen, hinv⟩ := hW p hp
    refine ⟨T.trans g, fun z => ?_, fun x => ?_⟩
    · have hT (z : LocalCenter E K p) : T (localCenterMap E K B p z) = localCenterMap E K A p z := by
        induction z using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul b k =>
          change b ⊗ₜ[E] e (algebraMap K B k) = b ⊗ₜ[E] algebraMap K A k
          rw [e.commutes]
      change g (T (localCenterMap E K B p z)) = _
      rw [hT, hcen]
    · exact (congrArg g (baseChange_transport D.involution f x)).trans (hinv (T x))
  · intro p q
    obtain ⟨C, ⟨g⟩, hg⟩ := hB p q
    let T : CompletedAlgebra K B q.val ≃ₐ[FiniteCompletion K q.val] CompletedAlgebra K A q.val :=
      Algebra.TensorProduct.congr AlgEquiv.refl e
    exact ⟨C, ⟨T.trans g⟩, hg⟩

end Carrier

end Langlands.Shimura.FiniteUnitary
