import Langlands.Representation.Exponents.SplitComponentDecomposition

/-! # Exponent comparisons for continuous central actions -/

noncomputable section

namespace Langlands

universe uR uA uB uM uN uV uW

variable {R : Type uR} [Field R] {A : Type uA} [Group A] {B : Type uB} [Group B]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {V : Type uV} [AddCommGroup V] [Module R V]
  (π : Representation R M V) (ι : A →* M)
  (hι : ∀ t : A, ι t ∈ Subgroup.center M)

/-- Restriction preserves the common nilpotence exponent. -/
theorem generalizedWeightSpace_le_comp (hπ : IsSmooth π)
    (e : B →* A) (ψ : A →* Rˣ) :
    (generalizedWeightSpace π ι ψ hι).toSubmodule ≤
      (generalizedWeightSpace π (ι.comp e) (ψ.comp e) (fun t => hι (e t))).toSubmodule := by
  intro v hv
  obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth ι ψ hι hπ v).mp hv
  exact (mem_generalizedWeightSpace_of_isSmooth _ _ _ hπ v).mpr ⟨d, fun t => hd (e t)⟩

/-- Every generalized character in a restriction comes from an actual
nonzero weight before restriction, provided those weights span. -/
theorem exists_generalizedWeight_comp [IsAlgClosed R] [TopologicalSpace A]
    (hιc : Continuous ι) (hπ : IsAdmissible π) (e : B →* A) (χ : B →* Rˣ)
    (hχ : IsGeneralizedEigencharacter (π.comp (ι.comp e)) χ) :
    ∃ ψ : A →* Rˣ, IsGeneralizedWeight π ι ψ hι ∧ ψ.comp e = χ := by
  classical
  by_contra hn
  have hne : ∀ ψ : {ψ : A →* Rˣ | IsGeneralizedWeight π ι ψ hι},
      ψ.val.comp e ≠ χ := by
    intro ψ h
    exact hn ⟨ψ, ψ.property, h⟩
  let Q := fun φ : B →* Rˣ =>
    (generalizedWeightSpace π (ι.comp e) φ (fun t => hι (e t))).toSubmodule
  have hspan := (generalizedWeightSpace_decomposition π ι hι hιc hπ).2
  have htop : (⊤ : Submodule R V) ≤ ⨆ (φ : B →* Rˣ) (_ : φ ≠ χ), Q φ := by
    rw [← hspan]
    refine iSup_le fun ψ => ?_
    exact (generalizedWeightSpace_le_comp π ι hι hπ.1 e ψ).trans
      (le_iSup_of_le (ψ.val.comp e) (le_iSup_of_le (hne ψ) le_rfl))
  have hi := generalizedWeightSpace_independent π (ι.comp e) (fun t => hι (e t)) hπ.1
  have hb : Q χ = ⊥ :=
    (disjoint_self.mp ((iSupIndep_def.mp hi χ).mono_right
      (le_top.trans htop)))
  exact ((generalizedWeightSpace_ne_bot_iff _ χ _ hπ.1).mpr hχ)
    (Subrepresentation.toSubmodule_injective hb)

variable {N : Type uN} [Group N] [TopologicalSpace N] [NonarchimedeanGroup N]
  [WeaklyLocallyCompactSpace N] {W : Type uW} [AddCommGroup W] [Module R W]
  (σ : Representation R N W) (κ : A →* N)
  (hκ : ∀ t : A, κ t ∈ Subgroup.center N)

/-- A linear map commuting with the two central actions preserves weights,
even if the ambient groups are different. -/
theorem map_mem_generalizedWeightSpace_of_comp
    (hπ : IsSmooth π) (hσ : IsSmooth σ) (f : V →ₗ[R] W)
    (hf : ∀ t : A, (σ (κ t)).comp f = f.comp (π (ι t)))
    (χ : A →* Rˣ) {v : V} (hv : v ∈ generalizedWeightSpace π ι χ hι) :
    f v ∈ generalizedWeightSpace σ κ χ hκ := by
  obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mp hv
  have hmap := map_mem_characterSpace_of_intertwining
    (π := π.comp ι) (σ := σ.comp κ) f hf χ d
    ((mem_characterSpace (π.comp ι) χ d v).mpr hd)
  exact (mem_generalizedWeightSpace_of_isSmooth κ χ hκ hσ _).mpr
    ⟨d, (mem_characterSpace (σ.comp κ) χ d (f v)).mp hmap⟩

/-- If the source central weights span, an onto central intertwiner reflects
every target generalized character. -/
def GeneralizedWeightReflectionStatement : Prop :=
  ∀ χ : A →* Rˣ, generalizedWeightSpace σ κ χ hκ ≠ ⊥ →
    generalizedWeightSpace π ι χ hι ≠ ⊥

/-- If the source central weights span, an onto central intertwiner reflects
every target generalized character. No target admissibility is needed. -/
theorem generalizedWeightSpace_ne_bot_of_surjective
    (hπ : IsSmooth π) (hσ : IsSmooth σ)
    (hspan : (⨆ χ : A →* Rˣ, (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤)
    (f : V →ₗ[R] W) (hf : ∀ t : A, (σ (κ t)).comp f = f.comp (π (ι t)))
    (honto : Function.Surjective f) :
    GeneralizedWeightReflectionStatement π ι hι σ κ hκ := by
  intro χ hχ
  intro hbot
  let Q := fun ψ : A →* Rˣ => (generalizedWeightSpace σ κ ψ hκ).toSubmodule
  have htop : (⊤ : Submodule R W) ≤ ⨆ (ψ : A →* Rˣ) (_ : ψ ≠ χ), Q ψ := by
    rw [← LinearMap.range_eq_top.mpr honto, ← Submodule.map_top, ← hspan, Submodule.map_iSup]
    refine iSup_le fun ψ => ?_
    by_cases heq : ψ = χ
    · subst ψ
      rw [hbot]
      change Submodule.map f ⊥ ≤ _
      simp
    · refine (Submodule.map_le_iff_le_comap.mpr ?_).trans
        (le_iSup_of_le ψ (le_iSup_of_le heq le_rfl))
      intro v hv
      exact map_mem_generalizedWeightSpace_of_comp π ι hι σ κ hκ hπ hσ f hf ψ hv
  have hi := generalizedWeightSpace_independent σ κ hκ hσ
  have hb : Q χ = ⊥ :=
    disjoint_self.mp ((iSupIndep_def.mp hi χ).mono_right (le_top.trans htop))
  exact hχ (Subrepresentation.toSubmodule_injective hb)

end Langlands
