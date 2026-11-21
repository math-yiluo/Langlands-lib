import Langlands.Analysis.Meromorphic.ScalarIdentity
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Meromorphic continuation of finite shift annihilators -/

universe u v

open Set
open scoped Manifold

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

variable {E : Type v} {X : Type u}

/-- A list of shift-minus-scalar factors, applied in the listed composition
order to each parameter value of a family of scalar functions. -/
def applyShiftFactors (factors : List ((X → X) × (E → ℂ)))
    (φ : E → X → ℂ) : E → X → ℂ :=
  factors.foldr (fun f ψ z x => ψ z (f.1 x) - f.2 z * ψ z x) φ

section Meromorphy

variable [NormedAddCommGroup E] [NormedSpace ℂ E]
  {D : Set E} {φ : E → X → ℂ}

/-- Finite shift factors with meromorphic scalar coefficients preserve
meromorphy of every point evaluation on the common domain. -/
theorem isMeromorphicOn_applyShiftFactors
    (hφ : ∀ x, IsMeromorphicOn 𝓘(ℂ, E) (fun z => φ z x) D)
    (factors : List ((X → X) × (E → ℂ)))
    (hcoeff : ∀ f ∈ factors, IsMeromorphicOn 𝓘(ℂ, E) f.2 D) :
    ∀ x, IsMeromorphicOn 𝓘(ℂ, E) (fun z => applyShiftFactors factors φ z x) D := by
  induction factors with
  | nil =>
    exact hφ
  | cons f tail ih =>
    intro x
    have htail := ih (fun g hg => hcoeff g (List.mem_cons_of_mem f hg))
    have hfirst := hcoeff f List.mem_cons_self
    have hproduct := hfirst.mul (htail x)
    rw [inter_self] at hproduct
    have hsum := (htail (f.1 x)).add hproduct.neg
    rw [inter_self] at hsum
    change IsMeromorphicOn 𝓘(ℂ, E) (fun z =>
      applyShiftFactors tail φ z (f.1 x) - f.2 z * applyShiftFactors tail φ z x) D
    exact hsum

end Meromorphy

/-- If each point of a nonempty open parameter patch admits an annihilator
from a countable sequence of finite shift products, some one product
annihilates the family throughout the common holomorphy domain. -/
def MeromorphicShiftAnnihilationStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) (D W : Set (Fin n → ℂ))
    (φ : (Fin n → ℂ) → X → ℂ) (factors : ℕ → List ((X → X) × ((Fin n → ℂ) → ℂ))),
    IsOpen D → Dense D → IsOpen W → W.Nonempty →
    (∀ x, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun z => φ z x) D) →
    (∀ k, ∀ f ∈ factors k, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f.2 D) →
    (∀ z ∈ W, ∃ k, applyShiftFactors (factors k) φ z = 0) →
    ∃ k, ∀ z ∈ D, applyShiftFactors (factors k) φ z = 0

theorem meromorphicShiftAnnihilation : MeromorphicShiftAnnihilationStatement.{u} := by
  intro n X D W φ factors hoD hdD hoW hnW hφ hc hpatch
  let V := W ∩ D
  have hoV : IsOpen V := hoW.inter hoD
  have hnV : V.Nonempty := hdD.inter_open_nonempty W hoW hnW
  let : Nonempty V := hnV.to_subtype
  let : BaireSpace V := hoV.baireSpace
  let Z (k : ℕ) : Set V := {z | applyShiftFactors (factors k) φ z = 0}
  have hMer (k : ℕ) (x : X) :=
    isMeromorphicOn_applyShiftFactors hφ (factors k) (hc k) x
  have hZ (k : ℕ) : IsClosed (Z k) := by
    have heq : Z k = ⋂ x : X, {z : V | applyShiftFactors (factors k) φ z x = 0} := by
      ext z
      rw [mem_iInter]
      exact ⟨fun hz x => congrFun hz x, fun hz => funext hz⟩
    rw [heq]
    apply isClosed_iInter
    intro x
    have hHol := isHolomorphicOn_iff_differentiableOn_scalar.mp (hMer k x).2.2.1
    let h := (hHol.continuousOn.mono (inter_subset_right : V ⊆ D))
    exact isClosed_eq (continuousOn_iff_continuous_domRestrict.mp h) continuous_const
  have hcover : (⋃ k, Z k) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨k, hk⟩ := hpatch z z.property.1
    exact mem_iUnion.2 ⟨k, hk⟩
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed hZ hcover
  let B : Set (Fin n → ℂ) := Subtype.val '' interior (Z k)
  have hoB : IsOpen B := hoV.isOpenMap_subtype_val _ isOpen_interior
  have hnB : B.Nonempty := hk.image Subtype.val
  refine ⟨k, fun z hz => funext fun x => ?_⟩
  have hEq : EqOn (fun t => applyShiftFactors (factors k) φ t x)
      (fun _ => (0 : ℂ)) (B ∩ (D ∩ univ)) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := ht.1
    have hy' : y ∈ Z k := interior_subset hy
    exact congrFun (show applyShiftFactors (factors k) φ (y : Fin n → ℂ) = 0 from hy') x
  exact (hMer k x).eqOn_of_eqOn_open (isMeromorphicOn_const 0) hoB hnB hEq ⟨hz, mem_univ _⟩

end Langlands.Analysis.Meromorphic
