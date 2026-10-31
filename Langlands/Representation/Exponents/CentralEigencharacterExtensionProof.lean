import Langlands.Representation.Exponents.CentralEigencharacterExtensionStatement
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Analysis.EndomorphismPowerBound

/-!
# Proof of the extension of generalized eigencharacters of a central action

The generalized character space of the restricted action, cut down to the
fixed vectors of one open subgroup, is finite-dimensional by admissibility and
stable under the central action. A common eigenvector there gives the
extension.
-/

noncomputable section

namespace Langlands

universe uG uA uB uX

section Extension

variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- An eigenvector of `T` with eigenvalue `c` lies in a generalized eigenspace
of `T` only for the eigenvalue `c`. -/
theorem eq_of_eigen_of_mem_genEigenspace (T : Module.End ℂ X) {u : X} (hu : u ≠ 0)
    {c μ : ℂ} (hc : T u = c • u) {k : ℕ} (hk : ((T - μ • 1) ^ k) u = 0) : c = μ := by
  have hpow : ∀ j : ℕ, ((T - μ • 1) ^ j) u = (c - μ) ^ j • u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, hc,
        LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, map_smul, ih,
        smul_smul, pow_succ, mul_comm]
  rw [hpow k] at hk
  have h0 : (c - μ) ^ k = 0 := by
    by_contra h
    exact hu ((smul_eq_zero.mp hk).resolve_left h)
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)

/-- A central action of a commutative group on an admissible representation:
a generalized eigencharacter of a further pullback extends to a smooth
eigencharacter of the central action.  The proof restricts to the generalized
eigenspace cut down to the fixed vectors of one open subgroup, which is
finite-dimensional by admissibility, and takes a common eigenvector there. -/
theorem exists_eigencharacter_extension {G : Type uG} [Group G] [TopologicalSpace G]
    {A : Type uA} [CommGroup A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    {A' : Type uB} [Monoid A'] (π : Representation ℂ G X) (hπ : IsAdmissible π)
    (φ : A →* G) (hφ : Continuous φ) (hcent : ∀ a g, Commute (φ a) g)
    (β : A' →* A) (χ : A' →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter ((π.comp φ).comp β) χ) :
    ∃ ψ : A →* ℂˣ, IsOpen (ψ.ker : Set A) ∧
      IsGeneralizedEigencharacter (π.comp φ) ψ ∧ ψ.comp β = χ := by
  obtain ⟨k, hk⟩ := hχ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
  obtain ⟨K, hK⟩ := hπ.1 v
  let W : Submodule ℂ X :=
    characterSpace ((π.comp φ).comp β) χ k ⊓ fixedVectors π K.toSubgroup
  have : Module.Finite ℂ (fixedVectors π K.toSubgroup) := hπ.2 K
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have hvW : v ∈ W := ⟨hv, hK⟩
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hcomm : ∀ a g, π (φ a) * π g = π g * π (φ a) := by
    intro a g
    rw [← map_mul, ← map_mul, (hcent a g).eq]
  have hmaps : ∀ a, ∀ w ∈ W, π (φ a) w ∈ W := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · let f : Representation.IntertwiningMap ((π.comp φ).comp β) ((π.comp φ).comp β) :=
        { toLinearMap := π (φ a)
          isIntertwining' := fun b => hcomm a (φ (β b)) }
      exact map_mem_characterSpace_of_intertwiningMap f χ k hw.1
    · intro x
      change π (x : G) (π (φ a) w) = π (φ a) w
      rw [← Module.End.mul_apply, ← hcomm a (x : G), Module.End.mul_apply]
      exact congrArg (π (φ a)) (hw.2 x)
  let f : A → Module.End ℂ W := fun a => (π (φ a)).restrict (hmaps a)
  have hfc : ∀ a b, Commute (f a) (f b) := by
    intro a b
    refine LinearMap.ext fun w => Subtype.ext ?_
    change π (φ a) (π (φ b) w) = π (φ b) (π (φ a) w)
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm a b, map_mul, map_mul,
      Module.End.mul_apply]
  obtain ⟨w, hw0, hw⟩ := EndomorphismBound.exists_common_eigenvector f hfc
  have hw0' : (w : X) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hw' : ∀ a, ∃ c : ℂ, (π.comp φ) a (w : X) = c • (w : X) := by
    intro a
    obtain ⟨c, hc⟩ := hw a
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨ψ, hψ⟩ := EndomorphismBound.exists_character_of_forall_eigen (π.comp φ) hw0' hw'
  refine ⟨ψ, ?_, isGeneralizedEigencharacter_of_eigenvector _ ψ hw0' hψ, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (OpenSubgroup.comap φ hφ K).toSubgroup) ?_
      (OpenSubgroup.comap φ hφ K).isOpen
    intro a ha
    rw [MonoidHom.mem_ker]
    have hfix : π (φ a) (w : X) = (w : X) := (w.2.2 ⟨φ a, ha⟩)
    have h1 : ((ψ a : ℂ) - 1) • (w : X) = 0 := by
      rw [sub_smul, one_smul, ← hψ a]
      exact sub_eq_zero.mpr hfix
    have h2 : (ψ a : ℂ) = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hw0')
    exact Units.ext h2
  · ext b
    have hmem := (mem_characterSpace _ χ k (w : X)).mp w.2.1 b
    exact eq_of_eigen_of_mem_genEigenspace (π (φ (β b))) hw0' (hψ (β b)) hmem

end Extension

/-- The extension of generalized eigencharacters of a central action on an
admissible representation. -/
theorem centralEigencharacterExtension :
    CentralEigencharacterExtensionStatement.{uG, uA, uB, uX} :=
  by
  intro _ _ _ _ _ _ _ _ _ _ _ _ π hπ φ hφ hcent β χ hχ
  exact exists_eigencharacter_extension π hπ φ hφ hcent β χ hχ

end Langlands
