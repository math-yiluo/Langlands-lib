import Langlands.Representation.Archimedean.BanachOrbitSmoothing
import Langlands.Representation.Archimedean.SmoothHilbert
import Langlands.Representation.Archimedean.TransposeHaar
import Langlands.Representation.Character.SeparationProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Character

/-! # Inverse-transpose pairings for finite-dimensional Hilbert representations -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section FiniteRepresentation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

/-- The ordinary trace character of a finite-dimensional complex representation. -/
def finiteDimensionalCharacter [FiniteDimensional ℂ V] (g : G) : ℂ :=
  ρ.character g

variable [FiniteDimensional ℂ V]

/-- Conjugating a group element leaves its finite-dimensional character unchanged. -/
theorem finiteDimensionalCharacter_conjugation (g a : G) :
    finiteDimensionalCharacter ρ (a * g * a⁻¹) = finiteDimensionalCharacter ρ g :=
  ρ.char_conj g a

omit [FiniteDimensional ℂ V] in
private theorem isIrreducible_of_stable_submodules (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ (g : G) (v : V), v ∈ U → ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    ρ.IsIrreducible := by
  have : Nontrivial V := hV
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain hU | hU := h U.toSubmodule fun g v hv => U.apply_mem_toSubmodule g hv
  · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
  · exact Or.inr (Subrepresentation.toSubmodule_injective hU)

private theorem isIrreducible_dual_of_finiteDimensional (hρ : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  have : Nontrivial V := Langlands.CharacterSeparation.nontrivial_of_isIrreducible hρ
  apply isIrreducible_of_stable_submodules ρ.dual inferInstance
  intro U hU
  let V₀ : Subrepresentation ρ :=
    ⟨U.dualCoannihilator, fun g v hv => by
      apply (Submodule.mem_dualCoannihilator _).mpr
      intro L hL
      have hLg := hU g⁻¹ L hL
      have hf := (Submodule.mem_dualCoannihilator _).mp hv _ hLg
      change L (ρ (g⁻¹)⁻¹ v) = 0 at hf
      simpa only [inv_inv] using hf⟩
  obtain h₀ | h₀ := hρ.eq_bot_or_eq_top V₀
  · right
    have he : U.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule h₀
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U), he,
      Submodule.dualAnnihilator_bot]
  · left
    have he : U.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule h₀
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U), he,
      Submodule.dualAnnihilator_top]

omit [FiniteDimensional ℂ V] in
private theorem trace_asModule (a : ℂ[G]) :
    LinearMap.trace ℂ ρ.asModule (DistribSMul.toLinearMap ℂ ρ.asModule a) =
      LinearMap.trace ℂ V (ρ.asAlgebraHom a) := by
  have he : ρ.asModuleEquiv.symm.conj (ρ.asAlgebraHom a) =
      DistribSMul.toLinearMap ℂ ρ.asModule a := by
    ext x
    rfl
  rw [← he, LinearMap.trace_conj']

private theorem nonempty_equiv_of_finiteDimensionalCharacter_eq [FiniteDimensional ℂ W]
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (h : ∀ g : G, finiteDimensionalCharacter ρ g = finiteDimensionalCharacter σ g) :
    Nonempty (ρ.Equiv σ) := by
  let _ := hρ
  let _ := hσ
  have htr (a : ℂ[G]) : LinearMap.trace ℂ V (ρ.asAlgebraHom a) =
      LinearMap.trace ℂ W (σ.asAlgebraHom a) := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g z =>
        have hg := h g
        unfold finiteDimensionalCharacter Representation.character at hg
        simp only [Representation.asAlgebraHom_single, map_smul, hg]
  obtain ⟨e⟩ := Langlands.CharacterSeparation.nonempty_linearEquiv_of_trace_eq
    (A := ℂ[G]) (M := ρ.asModule) (N := σ.asModule) (fun a => by
      rw [trace_asModule, trace_asModule]
      exact htr a)
  let T := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm e.toLinearMap
  have hT : (T : V → W) = σ.asModuleEquiv ∘ e ∘ ρ.asModuleEquiv.symm := rfl
  refine ⟨T.ofBijective ?_⟩
  rw [hT]
  exact σ.asModuleEquiv.bijective.comp (e.bijective.comp ρ.asModuleEquiv.symm.bijective)

end FiniteRepresentation

section Hilbert

open Langlands.HarmonicAnalysis.Distribution (transposeHomeomorph transposeHomeomorph_apply)

variable (F : Type) [RCLike F] (n : ℕ)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H] (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

local notation "GL" => Langlands.GeneralLinear n F
local notation "I" => matrixModel F n
local notation "D" => DerivativeSmoothVectors I R
local notation "ε" => DerivativeSmoothVectors.derivativeCLM I R []
local notation "θ" => Langlands.GeneralLinear.inverseTranspose n F

private theorem mem_smoothVectors_of_finiteDimensional (hR : IsContinuousRepresentation R) (v : H) :
    v ∈ smoothVectors I R := by
  let : MeasurableSpace GL := borel GL
  let : BorelSpace GL := ⟨rfl⟩
  let : LocallyCompactSpace GL := Units.isOpenEmbedding_val.locallyCompactSpace
  have hd := dense_smoothVectors_units R (Measure.haar : Measure GL) hR
  have hc := (smoothVectors I R).closed_of_finiteDimensional
  change v ∈ (smoothVectors I R : Set H)
  rw [← hc.closure_eq]
  exact hd v

/-- Every irreducible continuous finite-dimensional complex Hilbert representation of actual
archimedean GL has a nonzero smooth inverse-transpose pairing. -/
theorem hasNonzeroSmoothHilbertTransposePairing_of_finiteDimensional
    (hR : IsContinuousRepresentation R) (hirr : IsTopologicallyIrreducible R) :
    HasNonzeroSmoothHilbertTransposePairing F n R := by
  let ρ : Representation ℂ GL H := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R
  let σ : Representation ℂ GL (Module.Dual ℂ H) := ρ.dual.comp (θ).toMonoidHom
  have hρ : ρ.IsIrreducible := by
    apply isIrreducible_of_stable_submodules ρ hirr.1
    intro U hU
    exact hirr.2 U U.closed_of_finiteDimensional hU
  have hσ : σ.IsIrreducible := by
    apply (Langlands.CuspidalSupport.isIrreducible_comp_iff
      ρ.dual (θ).toMonoidHom (θ).surjective).mpr
    exact isIrreducible_dual_of_finiteDimensional ρ hρ
  have htrace (g : GL) : finiteDimensionalCharacter ρ g = finiteDimensionalCharacter σ g := by
    unfold finiteDimensionalCharacter Representation.character
    change LinearMap.trace ℂ H (ρ g) = LinearMap.trace ℂ (Module.Dual ℂ H) (ρ.dual (θ g))
    rw [Representation.dual_apply, LinearMap.trace_transpose']
    have hθ : (θ g)⁻¹ = transposeHomeomorph n F g := by
      rw [transposeHomeomorph_apply, map_inv]
    obtain ⟨a, ha⟩ := isConj_iff.mp (isConj_transpose F n g)
    rw [hθ, ← ha]
    exact (finiteDimensionalCharacter_conjugation ρ g a).symm
  obtain ⟨T⟩ := nonempty_equiv_of_finiteDimensionalCharacter_eq ρ σ hρ hσ htrace
  let C : H →ₗ[ℂ] H →ₗ[ℂ] ℂ := T.toLinearEquiv.toLinearMap.flip
  let B : D →ₗ[ℂ] D →ₗ[ℂ] ℂ := C.compl₁₂ ((ε).toLinearMap) ((ε).toLinearMap)
  refine ⟨B, ⟨fun x => ?_, fun y => ?_, fun g y x => ?_⟩, ?_⟩
  · exact (C.flip (ε x)).continuous_of_finiteDimensional.comp (ε).continuous
  · exact (C (ε y)).continuous_of_finiteDimensional.comp (ε).continuous
  · change T (R (θ g) (ε x)) (R g (ε y)) = T (ε x) (ε y)
    have ht := T.toIntertwiningMap.isIntertwining ρ σ (θ g) (ε x)
    change T (R (θ g) (ε x)) = ρ.dual (θ (θ g)) (T (ε x)) at ht
    rw [ht, Langlands.GeneralLinear.inverseTranspose_involutive, Representation.dual_apply]
    change T (ε x) (R g⁻¹ (R g (ε y))) = _
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  · intro hB
    let lift (v : H) : D := (DerivativeSmoothVectors.toSmooth I R).symm
      ⟨v, mem_smoothVectors_of_finiteDimensional F n R hR v⟩
    have : Nontrivial H := hirr.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    apply hx
    apply T.toLinearEquiv.injective
    rw [map_zero]
    ext y
    exact congrArg (fun Q : D →ₗ[ℂ] D →ₗ[ℂ] ℂ => Q (lift y) (lift x)) hB

end Hilbert

end Langlands.Archimedean
