import Langlands.BaseChange.TwistedCharacter.CyclicSemisimpleDescent
import Langlands.BaseChange.TwistedCharacter.FixedTraceProjection

/-! # Adjoint actions and compact frequency sets in cyclic descent -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation Set Function
open scoped SemidirectProduct

variable {F E : Type*} [CommRing E] {l n : ℕ} [NeZero l]

local notation "A" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

section Algebra

variable [Field F] [Algebra F E] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1}

local notation "H" => CyclicGLSemidirect σ hσ n
local notation "ι" => (SemidirectProduct.inl (φ := cyclicGLAction σ hσ n) : G →* H)

/-- The inverse cyclic adjoint gives inverse ambient conjugation on units. -/
theorem cyclicAdjointAlgEquiv_symm_onUnits (s : H) (g : G) :
    ι (Units.map (cyclicAdjointAlgEquiv s).symm.toMonoidHom g) = s⁻¹ * ι g * s := by
  let u := Units.map (cyclicAdjointAlgEquiv s).symm.toMonoidHom g
  have h := cyclicAdjointAlgEquiv_onUnits s u
  have heq : Units.map (cyclicAdjointAlgEquiv s).toMonoidHom u = g :=
    Units.ext ((cyclicAdjointAlgEquiv s).apply_symm_apply g.val)
  rw [heq] at h
  calc
    ι u = s⁻¹ * (s * ι u * s⁻¹) * s := by group
    _ = _ := by rw [← h]

variable [TopologicalSpace F]

/-- The regular trace bicharacter is invariant under the entire cyclic adjoint action. -/
theorem cyclicAdjoint_pairingCharacter (ψ : UnitaryAdditiveCharacter F) (s : H) (x z : A) :
    pairingCharacter ψ (Langlands.Algebra.regularTraceForm F A)
        (cyclicAdjointAlgEquiv s x) (cyclicAdjointAlgEquiv s z) =
      pairingCharacter ψ (Langlands.Algebra.regularTraceForm F A) x z :=
  congrArg (fun a : F => ψ.complex a) (regularTraceForm_automorphism (cyclicAdjointAlgEquiv s) x z)

variable [TopologicalSpace E] [IsTopologicalRing E]

/-- The full cyclic adjoint saturation of a compact set is contained in the
unit-conjugation saturation of a compact set. -/
def CyclicAdjointCompactSaturationStatement (ω : Set A) [IsTopologicalRing F] [IsModuleTopology F E] : Prop :=
  IsCompact ω → ∃ C : Set A, IsCompact C ∧
    ∀ (g : H) (x : A), x ∈ ω → cyclicAdjointAlgEquiv g x ∈ conjugationSaturation C

theorem cyclicAdjointCompactSaturation (ω : Set A) [IsTopologicalRing F] [IsModuleTopology F E] :
    CyclicAdjointCompactSaturationStatement (F := F) (σ := σ) (hσ := hσ) ω := by
  intro hω
  let a (c : CyclicComponent l) := (cyclicPowerHom σ hσ c).mapMatrix (m := Fin n)
  let C : Set A := ⋃ c : CyclicComponent l, a c '' ω
  let : IsModuleTopology F A := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  have hC : IsCompact C := isCompact_iUnion fun c =>
    hω.image (IsModuleTopology.continuous_of_linearMap (a c).toLinearMap)
  refine ⟨C, hC, fun g x hx => ?_⟩
  have hx' : a g.right x ∈ C := mem_iUnion.mpr ⟨g.right, mem_image_of_mem _ hx⟩
  exact mem_conjugationSaturation_iff.mpr ⟨g.left, a g.right x, hx', rfl⟩

end Algebra

section Slice

variable [Field F] [Algebra F E] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1}
  (s : CyclicGLSemidirect σ hσ n)

local notation "H" => CyclicGLSemidirect σ hσ n
local notation "ι" => (SemidirectProduct.inl (φ := cyclicGLAction σ hσ n) : G →* H)

local notation "α" => cyclicAdjointAlgEquiv s
local notation "S" => adjointFixedAlgebra (cyclicAdjointAlgEquiv s)

/-- The ambient adjoint at a translated slice unit is the fixed-unit adjoint
used in the transverse displacement estimate. -/
theorem cyclicAdjointAlgEquiv_mul_fixedUnit (m : Sˣ) (x : A) :
    cyclicAdjointAlgEquiv (s * ι (Units.map (S).val.toMonoidHom m)) x =
      (m.val : A) * α x * ((m⁻¹ : Sˣ).val : A) := by
  let u := Units.map (S).val.toMonoidHom m
  have hu : Units.map (α).toMonoidHom u = u := Units.ext m.val.property
  have heq : ι u = s * ι u * s⁻¹ := by
    simpa only [hu] using cyclicAdjointAlgEquiv_onUnits s u
  have hcomm : s * ι u = ι u * s := calc
    _ = (s * ι u * s⁻¹) * s := by group
    _ = _ := congrArg (· * s) heq.symm
  calc
    cyclicAdjointAlgEquiv (s * ι u) x = cyclicGLAdjointHom (ι u * s) x := by rw [← hcomm]; rfl
    _ = cyclicAdjointAlgEquiv (ι u) (cyclicAdjointAlgEquiv s x) := by rw [map_mul]; rfl
    _ = (m.val : A) * α x * ((m⁻¹ : Sˣ).val : A) := by
      change u.val * ((cyclicPowerHom σ hσ (ι u).right).mapMatrix (cyclicAdjointAlgEquiv s x)) *
        (u⁻¹ : G).val = (m.val : A) * cyclicAdjointAlgEquiv s x * ((m⁻¹ : Sˣ).val : A)
      rw [show (ι u).right = 1 from rfl, map_one]
      rfl

end Slice

end Langlands.BaseChange
