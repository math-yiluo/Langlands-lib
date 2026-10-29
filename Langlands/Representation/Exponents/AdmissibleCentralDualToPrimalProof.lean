import Langlands.LinearAlgebra.EigenvectorDefect
import Langlands.Representation.Exponents.AdmissibleCentralDualToPrimalStatement
import Langlands.Representation.Exponents.FiniteActionSpectrumProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Local central dual-to-primal conversion

A derived algebraic proof of the published local interface.
Adapted by Worker 51 from Worker 429's implementation; the finite-fixed-space
route follows discussions among Workers 84, 728 and 429.
-/

noncomputable section

namespace Langlands

universe uG uA uV

private theorem finite_central_dual_to_primal
    (A : Type uA) [CommGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ A V) (χ : A →* ℂˣ)
    (φ : Module.Dual ℂ V) (hφne : φ ≠ 0)
    (hφeig : ∀ a, commutativeTranspose ρ a φ = (χ a : ℂ) • φ) :
    IsGeneralizedEigencharacter ρ χ := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hfin : Module.Finite ℂ (Submodule.span ℂ (Set.range ρ)) := inferInstance
  have htop := (finiteActionCommutativeSpectrum A V ρ hfin
    (IsLocallyConstant.of_discrete _)).2.2
  obtain ⟨ψ, -, w, hw, hφw⟩ : ∃ ψ : A →* ℂˣ,
      (IsOpen (ψ.ker : Set A) ∧ commutativeCharacterSpace ρ ψ 1 ≠ ⊥) ∧
      ∃ w, w ∈ generalizedCommutativeCharacterSpace ρ ψ ∧ φ w ≠ 0 := by
    by_contra! h
    apply hφne
    have hle : (⨆ (ψ : A →* ℂˣ)
        (_ : IsOpen (ψ.ker : Set A) ∧ commutativeCharacterSpace ρ ψ 1 ≠ ⊥),
        (generalizedCommutativeCharacterSpace ρ ψ).toSubmodule) ≤ LinearMap.ker φ :=
      iSup₂_le fun ψ hψ w hw => h ψ hψ w hw
    rw [htop, top_le_iff] at hle
    exact LinearMap.ker_eq_top.mp hle
  obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace _ _ _).mp hw
  have hχψ : ∀ a, (χ a : ℂ) = (ψ a : ℂ) := by
    intro a
    have h1 := commutativeTranspose_defect_pow_apply ρ a (ψ a : ℂ) k φ w
    rw [hk a, map_zero] at h1
    have h2 : ((commutativeTranspose ρ a - (ψ a : ℂ) • 1) ^ k) φ =
        ((χ a : ℂ) - ψ a) ^ k • φ :=
      ScalarLayer.pow_sub_smul_apply_of_eigen _ (hφeig a) _ _
    rw [h2, LinearMap.smul_apply, smul_eq_mul] at h1
    have h3 := (mul_eq_zero.mp h1).resolve_right hφw
    exact sub_eq_zero.mp (pow_eq_zero_iff'.mp h3).1
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, w, ?_, fun a => ?_⟩
  · rintro rfl
    exact hφw (map_zero φ)
  · rw [hχψ a]
    exact hk a

private theorem centralDualToPrimal_defect_pow_coe
    (A : Type uA) [CommGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V) (S : Subrepresentation ρ)
    (a : A) (c : ℂ) (k : ℕ) (v : S.toSubmodule) :
    ((((S.toRepresentation a - c • 1) ^ k) v : S.toSubmodule) : V) =
      ((ρ a - c • 1) ^ k) (v : V) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change ρ a ↑(((S.toRepresentation a - c • 1) ^ k) v) -
        c • ↑(((S.toRepresentation a - c • 1) ^ k) v) = _
      rw [ih]
      rfl

/-- A nonzero central transpose eigenfunctional on an admissible representation
yields a primal uniform-power generalized eigenvector for the same character. -/
theorem admissibleCentralDualToPrimal :
    AdmissibleCentralDualToPrimalStatement.{uG,uA,uV} := by
  classical
  intro G _ _ _ hcofinal A _ V _ _ ρ c hadm χ hχ
  let f : A →* G := (Subgroup.center G).subtype.comp c
  obtain ⟨φ, hφ, hφne⟩ := FiniteActionSpectrum.subrepresentation_exists_ne_zero hχ
  have hφeig := (mem_commutativeCharacterSpace_one _ χ φ).mp hφ
  obtain ⟨v, hv⟩ : ∃ v : V, φ v ≠ 0 := by
    by_contra! h
    apply hφne
    ext v
    exact h v
  obtain ⟨H, hH⟩ := hadm.1 v
  obtain ⟨K, -, hKH⟩ := hcofinal H
  have hKv : v ∈ fixedVectors ρ K.toSubgroup :=
    fun k => hH ⟨k, hKH k.property⟩
  let S : Subrepresentation (ρ.comp f) :=
    { toSubmodule := fixedVectors ρ K.toSubgroup
      apply_mem_toSubmodule := fun a v hv k => by
        change ρ (k : G) (ρ (c a : G) v) = ρ (c a : G) v
        calc
          _ = ρ (c a : G) (ρ (k : G) v) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
              Subgroup.mem_center_iff.mp (c a).property (k : G)]
          _ = _ := congrArg (ρ (c a : G)) (hv k) }
  let : Module.Finite ℂ S.toSubmodule := hadm.2 K
  let φ₀ : Module.Dual ℂ S.toSubmodule := φ.comp S.toSubmodule.subtype
  have hφ₀ne : φ₀ ≠ 0 := by
    intro h
    exact hv (congrArg (fun ℓ : Module.Dual ℂ S.toSubmodule => ℓ ⟨v, hKv⟩) h)
  have hφ₀eig (a : A) :
      commutativeTranspose S.toRepresentation a φ₀ = (χ a : ℂ) • φ₀ := by
    ext w
    have h := congrArg (fun ℓ : Module.Dual ℂ V => ℓ (w : V)) (hφeig a)
    exact h
  have hgen := finite_central_dual_to_primal A S.toSubmodule S.toRepresentation χ
    φ₀ hφ₀ne hφ₀eig
  obtain ⟨k, w, hwne, hw⟩ := (isGeneralizedEigencharacter_iff _ _).mp hgen
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, (w : V), ?_, fun a => ?_⟩
  · intro h
    exact hwne (Subtype.ext h)
  · rw [← centralDualToPrimal_defect_pow_coe A V (ρ.comp f) S a (χ a : ℂ) k w, hw a]
    rfl

end Langlands
