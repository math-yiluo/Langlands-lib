import Langlands.Representation.Filtration.IsolatedCentralCharacter
import Langlands.Representation.Exponents.OppositeJacquetCentralAction

/-! Retraction from a single isolated irreducible central grade. -/

noncomputable section

namespace Langlands.FilteredCentralRetraction

universe uG uV uW

variable {G : Type uG} [Group G] {E : Rep.{uV} ℂ G}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G W} {n : ℕ}

/-- The scalar character of a nonzero generalized central vector is unique. -/
theorem scalar_character_unique (χ₀ χ : Subgroup.center G →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center G) (v : W), ρ (z : G) v = (χ₀ z : ℂ) • v)
    (hχ : IsGeneralizedEigencharacter (ρ.comp (Subgroup.center G).subtype) χ) :
    χ = χ₀ := by
  obtain ⟨m, hm⟩ := hχ
  obtain ⟨v, hv, hv₀⟩ := (Submodule.ne_bot_iff _).mp hm
  apply MonoidHom.ext
  intro z
  apply Units.ext
  by_contra hne
  have hvχ := (mem_characterSpace _ χ m v).mp hv z
  have hv₀' := (mem_centralCharacterSpace ρ χ₀ 1 v).mp
    ((mem_centralCharacterSpace_one ρ χ₀ v).mpr (fun z => hscalar z v)) z
  exact hv₀ (FiniteActionSpectrum.eq_zero_of_pow_sub_smul
    (T := ρ (z : G)) hne hvχ hv₀')

/-- Finite-filtration detection eliminates every qualifying central character
other than the scalar character of the unique possible grade. -/
theorem character_unique_of_filtration (s : ObjectRepFiltration E n)
    (χ₀ : Subgroup.center G →* ℂˣ) (j₀ : Fin n)
    (P : (Subgroup.center G →* ℂˣ) → Prop)
    (hother : ∀ χ, P χ → ∀ j : Fin n, j ≠ j₀ →
      ¬ IsGeneralizedEigencharacter
        ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ)
    (hscalar : ∀ (z : Subgroup.center G) (v : s.gradedRepresentation j₀),
      (s.gradedRepresentation j₀).ρ (z : G) v = (χ₀ z : ℂ) • v)
    (χ : Subgroup.center G →* ℂˣ) (hP : P χ)
    (hχ : IsGeneralizedEigencharacter (E.ρ.comp (Subgroup.center G).subtype) χ) :
    χ = χ₀ := by
  obtain ⟨j, hj⟩ := s.exists_graded_isGeneralizedEigencharacter
    (CategoryTheory.Discrete.mk PUnit.unit) (Subgroup.center G).subtype χ hχ
  by_cases h : j = j₀
  · subst j
    exact scalar_character_unique χ₀ χ hscalar hj
  · exact (hother χ hP j h hj).elim

/-- A singleton group of central characters is the actual generalized space. -/
theorem grouped_singleton (σ : Representation ℂ G W) (χ : Subgroup.center G →* ℂˣ) :
    groupedCentralCharacterSpace σ (fun ψ => ψ = χ) =
      generalizedCentralCharacterSpace σ χ := by
  apply Subrepresentation.toSubmodule_injective
  change (⨆ ψ : {ψ : Subgroup.center G →* ℂˣ // ψ = χ},
      (generalizedCentralCharacterSpace σ ψ.val).toSubmodule) = _
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    rw [ψ.property]
  · exact le_iSup_of_le ⟨χ, rfl⟩ le_rfl

/-- The finite-central projector and the isolated-block
construction give one whole-ambient retraction fixing all qualifying blocks. -/
theorem retractionOfIsolatedGrade
    (hfin : Module.Finite ℂ (Submodule.span ℂ
      (Set.range (fun z : Subgroup.center G => E.ρ (z : G)))))
    (s : ObjectRepFiltration E n) (χ₀ : Subgroup.center G →* ℂˣ) (j₀ : Fin n)
    (P : (Subgroup.center G →* ℂˣ) → Prop) (hP₀ : P χ₀)
    (hother : ∀ χ, P χ → ∀ j : Fin n, j ≠ j₀ →
      ¬ IsGeneralizedEigencharacter
        ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ)
    (hgrade : Representation.IsIrreducible (s.gradedRepresentation j₀).ρ)
    (hscalar : ∀ (z : Subgroup.center G) (v : s.gradedRepresentation j₀),
      (s.gradedRepresentation j₀).ρ (z : G) v = (χ₀ z : ℂ) • v)
    (hρ : ∀ (z : Subgroup.center G) (w : W), ρ (z : G) w = (χ₀ z : ℂ) • w)
    (i : ρ.IntertwiningMap E.ρ) (hi : Function.Injective i) (hi₀ : i ≠ 0) :
    ∃ r : E.ρ.IntertwiningMap ρ,
      (∀ w, r (i w) = w) ∧
      ∀ χ, P χ → ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ →
        i (r v) = v := by
  classical
  let e := ObjectRepFiltration.isolatedCentralCharacterEquiv s χ₀ j₀
    (hother χ₀ hP₀) hgrade hρ i hi hi₀
  obtain ⟨rP, hrP, -⟩ := groupedCentralCharacterRetraction
    G E E.ρ hfin (fun ψ => ψ = χ₀)
  have heq := grouped_singleton E.ρ χ₀
  let val := (groupedCentralCharacterSpace E.ρ (fun ψ => ψ = χ₀)).toSubmodule.subtype
  let r₀ : E.ρ.IntertwiningMap (generalizedCentralCharacterSpace E.ρ χ₀).toRepresentation :=
    { toFun := fun v => ⟨rP v, heq ▸ (rP v).property⟩
      map_add' := fun v w => Subtype.ext (congrArg val (map_add rP v w))
      map_smul' := fun c v => Subtype.ext (congrArg val (map_smul rP c v))
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg val
          (Representation.IntertwiningMap.isIntertwining _ _ rP g v) }
  have hr₀ : ∀ v : generalizedCentralCharacterSpace E.ρ χ₀, r₀ v = v := by
    intro v
    apply Subtype.ext
    exact congrArg val (hrP ⟨v, heq.symm ▸ v.property⟩)
  let r := e.symm.toIntertwiningMap.comp r₀
  refine ⟨r, ?_, ?_⟩
  · intro w
    change e.symm (r₀ (i w)) = w
    have h : r₀ (i w) = e w := by
      exact hr₀ (e w)
    rw [h, e.symm_apply_apply]
  · intro χ hP v hv
    by_cases hv₀ : v = 0
    · simp [hv₀]
    have hχ : IsGeneralizedEigencharacter (E.ρ.comp (Subgroup.center G).subtype) χ := by
      obtain ⟨m, hm⟩ := (mem_generalizedCentralCharacterSpace E.ρ χ v).mp hv
      exact ⟨m, (Submodule.ne_bot_iff _).mpr
        ⟨v, (mem_characterSpace _ χ m v).mpr hm, hv₀⟩⟩
    have heχ := character_unique_of_filtration s χ₀ j₀ P hother hscalar χ hP hχ
    subst χ
    have hrfix : (r₀ v : E) = v := congrArg Subtype.val (hr₀ ⟨v, hv⟩)
    calc
      i (r v) = (e (e.symm (r₀ v)) : E) := rfl
      _ = (r₀ v : E) := congrArg Subtype.val (e.apply_symm_apply (r₀ v))
      _ = v := hrfix

end Langlands.FilteredCentralRetraction
