import Langlands.Representation.Tensor.ExternalFiltration
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual subrepresentations in an external tensor slot. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.TensorFiltration

universe uK uG uA uB

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uA} k G} (B : Rep.{uB} k G)

/-- Tensoring invariant subspaces with a nonzero vector space reflects inclusion. -/
theorem leftTensorImage_le_iff [Nontrivial B] (S T : Subrepresentation A.ρ) :
    leftTensorImage B S ≤ leftTensorImage B T ↔ S ≤ T := by
  classical
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hb
  let E : B ⊗[k] A →ₗ[k] A :=
    (TensorProduct.lid k A).toLinearMap.comp
      (TensorProduct.map φ (LinearMap.id : A →ₗ[k] A))
  have hE (a : A) : E (b ⊗ₜ[k] a) = a := by
    simp [E, hφ]
  have hET (z : B ⊗[k] T.toSubmodule) :
      E (leftTensorInclusion B T z) ∈ T := by
    change E (leftTensorInclusion B T z) ∈ T.toSubmodule
    induction z using TensorProduct.inductionOn with
    | tmul c t =>
      simpa [E] using T.toSubmodule.smul_mem (φ c) t.property
    | add x y hx hy =>
      simpa only [map_add] using T.toSubmodule.add_mem hx hy
  constructor
  · intro h a ha
    have ha' : b ⊗ₜ[k] a ∈ leftTensorImage B S :=
      ⟨b ⊗ₜ[k] (⟨a, ha⟩ : S.toSubmodule), rfl⟩
    obtain ⟨z, hz⟩ := h ha'
    change leftTensorInclusion B T z = b ⊗ₜ[k] a at hz
    have hz' := hET z
    rw [hz, hE] at hz'
    exact hz'
  · intro h
    exact leftTensorImage_mono B h

end Langlands.TensorFiltration

namespace Langlands.FiniteTensor

universe uK uI uG uV

variable {k : Type uK} [Field k] {ι : Type uI} [DecidableEq ι]
  {H : ι → Type uG} [∀ h, Group (H h)]
  {V : ι → Type uV} [∀ h, AddCommGroup (V h)] [∀ h, Module k (V h)]
  (ρ : ∀ h, Representation k (H h) (V h)) (j : ι)

private def coordinateSubrepresentation (S : Subrepresentation (ρ j)) :
    Subrepresentation ((ρ j).comp (Pi.evalMonoidHom H j)) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g := S.apply_mem_toSubmodule (g j)

/-- Tensor the original invariant slot subspace with all complementary factors,
then return it through the original slot splitting equivalence. -/
def externalSlotSubrepresentation (S : Subrepresentation (ρ j)) :
    Subrepresentation (external ρ) :=
  LengthTwo.comap
    (slotEquiv (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j).toIntertwiningMap
    (TensorFiltration.leftTensorImage
      (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j)))
      (Rep.of (action (fun h : ({j}ᶜ : Set ι) => (ρ h).comp (Pi.evalMonoidHom H h))))
      (coordinateSubrepresentation ρ j S))

@[simp]
theorem externalSlotSubrepresentation_bot :
    externalSlotSubrepresentation ρ j ⊥ = ⊥ := by
  apply SetLike.ext
  intro v
  change (slotEquiv (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j) v ∈
    TensorFiltration.leftTensorImage
      (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j)))
      (Rep.of (action (fun h : ({j}ᶜ : Set ι) => (ρ h).comp (Pi.evalMonoidHom H h))))
      ⊥ ↔ v = 0
  rw [TensorFiltration.leftTensorImage_bot]
  exact (slotEquiv (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j).map_eq_zero_iff

@[simp]
theorem externalSlotSubrepresentation_top :
    externalSlotSubrepresentation ρ j ⊤ = ⊤ := by
  apply SetLike.ext
  intro v
  change (slotEquiv (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j) v ∈
    TensorFiltration.leftTensorImage
      (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j)))
      (Rep.of (action (fun h : ({j}ᶜ : Set ι) => (ρ h).comp (Pi.evalMonoidHom H h))))
      ⊤ ↔ True
  rw [TensorFiltration.leftTensorImage_top]
  exact iff_true_intro (Submodule.mem_top)

/-- Nonzero complementary factors make the slot construction reflect the exact
inclusion relation on original invariant subspaces. -/
theorem externalSlotSubrepresentation_le_iff [Finite ι]
    (hV : ∀ h : ({j}ᶜ : Set ι), Nontrivial (V h))
    (S T : Subrepresentation (ρ j)) :
    externalSlotSubrepresentation ρ j S ≤ externalSlotSubrepresentation ρ j T ↔ S ≤ T := by
  classical
  let := hV
  let C := Rep.of (action (fun h : ({j}ᶜ : Set ι) =>
    (ρ h).comp (Pi.evalMonoidHom H h)))
  let b := fun h : ({j}ᶜ : Set ι) => Module.Basis.ofVectorSpace k (V h)
  let bt := Basis.piTensorProduct b
  let q := fun h : ({j}ᶜ : Set ι) =>
    Classical.choice (b h).index_nonempty
  let : Nontrivial C := ⟨⟨bt q, 0, bt.ne_zero q⟩⟩
  let e := slotEquiv (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
  constructor
  · intro h
    have h' : TensorFiltration.leftTensorImage (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C (coordinateSubrepresentation ρ j S) ≤
        TensorFiltration.leftTensorImage (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C (coordinateSubrepresentation ρ j T) := by
      intro z hz
      have hz' : e.symm z ∈ externalSlotSubrepresentation ρ j S := by
        change e (e.symm z) ∈ TensorFiltration.leftTensorImage
          (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C
          (coordinateSubrepresentation ρ j S)
        simpa only [Representation.Equiv.apply_symm_apply] using hz
      have ht := h hz'
      change e (e.symm z) ∈ TensorFiltration.leftTensorImage
        (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C
        (coordinateSubrepresentation ρ j T) at ht
      simpa only [Representation.Equiv.apply_symm_apply] using ht
    exact (TensorFiltration.leftTensorImage_le_iff (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C _ _).mp h'
  · intro h v hv
    exact TensorFiltration.leftTensorImage_mono (A := Rep.of ((ρ j).comp (Pi.evalMonoidHom H j))) C h hv

/-- A nonzero original slot subrepresentation remains nonzero. -/
theorem externalSlotSubrepresentation_ne_bot [Finite ι]
    (hV : ∀ h : ({j}ᶜ : Set ι), Nontrivial (V h))
    (S : Subrepresentation (ρ j)) (hS : S ≠ ⊥) :
    externalSlotSubrepresentation ρ j S ≠ ⊥ := by
  intro h
  apply hS
  apply le_antisymm _ bot_le
  apply (externalSlotSubrepresentation_le_iff ρ j hV S ⊥).mp
  rw [h, externalSlotSubrepresentation_bot]

/-- A proper original slot subrepresentation remains proper. -/
theorem externalSlotSubrepresentation_ne_top [Finite ι]
    (hV : ∀ h : ({j}ᶜ : Set ι), Nontrivial (V h))
    (S : Subrepresentation (ρ j)) (hS : S ≠ ⊤) :
    externalSlotSubrepresentation ρ j S ≠ ⊤ := by
  intro h
  apply hS
  apply le_antisymm le_top
  apply (externalSlotSubrepresentation_le_iff ρ j hV ⊤ S).mp
  rw [h, externalSlotSubrepresentation_top]

end Langlands.FiniteTensor
