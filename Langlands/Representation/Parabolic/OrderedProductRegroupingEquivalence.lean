import Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.Representation.Induction.BlockEquivalence

/-! Actual representation equivalences from a supplied ordered regrouping proof. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (regrouping : Parabolic.OrderedProductRegrouping.{uF,uV} F T)
variable {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
variable (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
variable (h : ∀ a, (S a.1).size a.2 = B.size (e a))
variable (hc : ∀ j k (x : Fin ((S j).size k)),
  D.index j ((S j).index k x) = B.index (e ⟨j,k⟩) (Fin.cast (h ⟨j,k⟩) x))

/-- Extract an actual invertible intertwiner from the supplied categorical regrouping. -/
def normalizedProductRegroupingEquiv
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :=
  letI := T.topology
  SmoothRep.equivOfIso (Classical.choice (regrouping n B D S e h hc σ))

/-- Compare regrouping with prescribed outer factors using actual inner equivalences. -/
def normalizedProductRegroupingToEquiv
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    {W : Fin D.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (τ : ∀ j, Representation ℂ (GeneralLinear (D.size j) F.Carrier) (W j))
    (δ : letI := T.topology
      ∀ j, Representation.Equiv
        (((T.normalizedProductInductionFunctor.{uF,uV} (S j)).obj
          (fun k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩))).representation) (τ j)) :=
  letI := T.topology
  (T.normalizedProductRegroupingEquiv regrouping B D S e h hc σ).trans
    (T.normalizedProductInducedEquiv D δ)

end Langlands.PadicField.TopologicalData
