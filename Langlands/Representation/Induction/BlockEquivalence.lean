import Langlands.Representation.Induction.BlockFactors

/-! Actual normalized induction transports a family of representation equivalences. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
  {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}

/-- Apply the block equivalences to values of the actual induced functions. -/
def productInducedOfEquiv (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (e : ∀ i, (σ i).Equiv (τ i)) :
    (B.productInducedOf χ σ).Equiv (B.productInducedOf χ τ) where
  __ := B.productInducedOfMap χ (fun i => (e i).toIntertwiningMap)
  invFun := B.productInducedOfMap χ (fun i => (e i).symm.toIntertwiningMap)
  left_inv x := by
    have h := B.productInducedOfMap_comp χ
      (fun i => (e i).toIntertwiningMap) (fun i => (e i).symm.toIntertwiningMap)
    have he : (fun i => (e i).symm.toIntertwiningMap.comp (e i).toIntertwiningMap) =
        (fun i => Representation.IntertwiningMap.id (σ i)) := by
      funext i
      ext v
      exact (e i).symm_apply_apply v
    rw [he, productInducedOfMap_id] at h
    exact congrArg (fun f => f x) h.symm
  right_inv x := by
    have h := B.productInducedOfMap_comp χ
      (fun i => (e i).symm.toIntertwiningMap) (fun i => (e i).toIntertwiningMap)
    have he : (fun i => (e i).toIntertwiningMap.comp (e i).symm.toIntertwiningMap) =
        (fun i => Representation.IntertwiningMap.id (τ i)) := by
      funext i
      ext v
      exact (e i).apply_symm_apply v
    rw [he, productInducedOfMap_id] at h
    exact congrArg (fun f => f x) h.symm

@[simp]
theorem productInducedOfEquiv_toIntertwiningMap
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (e : ∀ i, (σ i).Equiv (τ i)) :
    (B.productInducedOfEquiv χ e).toIntertwiningMap =
      B.productInducedOfMap χ (fun i => (e i).toIntertwiningMap) := rfl

@[simp]
theorem productInducedOfEquiv_symm_apply
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (e : ∀ i, (σ i).Equiv (τ i))
    (x : Induction.SmoothFunctions (B.parabolic F)
      (B.inducingRepresentation χ (B.blockTensor τ))) :
    (B.productInducedOfEquiv χ e).symm x =
      B.productInducedOfMap χ (fun i => (e i).symm.toIntertwiningMap) x := rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
  {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}

/-- Block equivalences induce an equivalence of actual normalized upper inductions. -/
def normalizedProductInducedEquiv (e : ∀ i, (σ i).Equiv (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv (T.normalizedProductInduced B τ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.productInducedOfEquiv (T.leviHalfCharacter B) e

@[simp]
theorem normalizedProductInducedEquiv_toIntertwiningMap
    (e : ∀ i, (σ i).Equiv (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInducedEquiv B e).toIntertwiningMap =
      T.normalizedProductInducedMap B (fun i => (e i).toIntertwiningMap) := rfl

end Langlands.PadicField.TopologicalData
