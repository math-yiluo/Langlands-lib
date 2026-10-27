import Langlands.Representation.Filtration.GeneralizedEigencharacterStatement

/-! # Generalized eigencharacter detection in actual graded quotients -/

open CategoryTheory

namespace Langlands

universe uR uG uH uV uW uC vC

section CharacterSpaces

variable {R : Type uR} [CommRing R] {H : Type uH} [Monoid H]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {π : Representation R H V} {σ : Representation R H W}

/-- An intertwiner retains every finite uniform character-space exponent. -/
theorem map_mem_characterSpace_of_intertwiningMap (f : π.IntertwiningMap σ)
    (χ : H →* Rˣ) (k : ℕ) {v : V} (hv : v ∈ characterSpace π χ k) :
    f v ∈ characterSpace σ χ k := by
  simp only [characterSpace, Submodule.mem_iInf] at hv ⊢
  intro h
  exact Module.End.mapsTo_genEigenspace_of_comp f.toLinearMap
    (f.isIntertwining' h).symm (χ h : R) k (hv h)

/-- A nonzero image of a generalized eigenvector detects the same character. -/
theorem isGeneralizedEigencharacter_of_map_ne_zero (f : π.IntertwiningMap σ)
    (χ : H →* Rˣ) (k : ℕ) {v : V} (hv : v ∈ characterSpace π χ k)
    (hf : f v ≠ 0) : IsGeneralizedEigencharacter σ χ := by
  exact ⟨k, (Submodule.ne_bot_iff _).mpr
    ⟨f v, map_mem_characterSpace_of_intertwiningMap f χ k hv, hf⟩⟩

/-- Actual representation equivalences preserve generalized eigencharacters. -/
theorem isGeneralizedEigencharacter_iff_of_equiv (e : π.Equiv σ)
    (χ : H →* Rˣ) :
    IsGeneralizedEigencharacter π χ ↔ IsGeneralizedEigencharacter σ χ := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
    apply isGeneralizedEigencharacter_of_map_ne_zero e.toIntertwiningMap χ k hv
    intro h
    exact hv0 (e.injective (by simpa using h))
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
    apply isGeneralizedEigencharacter_of_map_ne_zero e.symm.toIntertwiningMap χ k hv
    intro h
    exact hv0 (e.symm.injective (by simpa using h))

end CharacterSpaces

section Restriction

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
variable {H : Type uH} [Monoid H]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- Restriction to an invariant submodule reflects the same uniform equations,
also after restriction of the monoid action. -/
theorem mem_characterSpace_subrepresentation_comp
    (π : Representation R G V) (S : Subrepresentation π)
    (ι : H →* G) (χ : H →* Rˣ) (k : ℕ) (v : S.toSubmodule) :
    v ∈ characterSpace (S.toRepresentation.comp ι) χ k ↔
      (v : V) ∈ characterSpace (π.comp ι) χ k := by
  simp only [characterSpace, Submodule.mem_iInf]
  apply forall_congr'
  intro h
  change v ∈ Module.End.genEigenspace
      ((π (ι h)).restrict (S.apply_mem_toSubmodule (ι h))) (χ h : R) k ↔
    (v : V) ∈ Module.End.genEigenspace (π (ι h)) (χ h : R) k
  rw [Module.End.genEigenspace_restrict]
  rfl

end Restriction

/-- Detection in an actual finite graded quotient, retaining the common power. -/
theorem generalizedEigencharacterFiltration :
    GeneralizedEigencharacterFiltrationStatement.{uR, uG, uH, uV, uC, vC} := by
  intro R _ G _ H _ C _ F n s X ι χ k hk
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
  let P (j : Fin (n + 1)) : Prop := v ∈ (s.step j).obj X
  have hzero : ¬ P 0 := by
    intro h
    change v ∈ (s.step 0).obj X at h
    rw [s.zero X] at h
    exact hv0 ((Submodule.mem_bot R).mp h)
  have hlast : P (Fin.last n) := by
    change v ∈ (s.step (Fin.last n)).obj X
    rw [s.top X]
    exact Submodule.mem_top
  have hstep : ∃ i : Fin n, ¬ P i.castSucc ∧ P i.succ := by
    by_contra h
    have hnext : ∀ i : Fin n, ¬ P i.castSucc → ¬ P i.succ := by
      intro i hi hi'
      exact h ⟨i, hi, hi'⟩
    have hnlast : ¬ P (Fin.last n) := Fin.induction hzero hnext (Fin.last n)
    exact hnlast hlast
  obtain ⟨i, hlower, hupper⟩ := hstep
  let w : (s.step i.succ).representation X := ⟨v, hupper⟩
  have hw : w ∈ characterSpace
      (((s.step i.succ).representation X).ρ.comp ι) χ k :=
    (mem_characterSpace_subrepresentation_comp
      (F.obj X).ρ ((s.step i.succ).obj X) ι χ k w).mpr hv
  let q : Representation.IntertwiningMap
      (((s.step i.succ).representation X).ρ.comp ι)
      (((s.graded i).obj X).ρ.comp ι) :=
    { toLinearMap :=
        ((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom.toLinearMap
      isIntertwining' h :=
        ((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom.isIntertwining'
          (ι h) }
  have hqw : q w ≠ 0 := by
    intro h
    apply hlower
    change w ∈ ((s.step i.castSucc).lowerInUpper (s.step i.succ) X).toSubmodule
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  exact ⟨i, (Submodule.ne_bot_iff _).mpr
    ⟨q w, map_mem_characterSpace_of_intertwiningMap q χ k hw, hqw⟩⟩

/-- Every generalized eigencharacter occurs in one actual graded quotient,
after restricting all actions along the supplied monoid homomorphism. -/
theorem RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter
    {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    {H : Type uH} [Monoid H] {C : Type uC} [Category.{vC} C]
    {F : C ⥤ Rep.{uV} R G} {n : ℕ} (s : RepFunctorFiltration F n) (X : C)
    (ι : H →* G) (χ : H →* Rˣ)
    (hχ : IsGeneralizedEigencharacter ((F.obj X).ρ.comp ι) χ) :
    ∃ i : Fin n, IsGeneralizedEigencharacter (((s.graded i).obj X).ρ.comp ι) χ := by
  obtain ⟨k, hk⟩ := hχ
  obtain ⟨i, hi⟩ := generalizedEigencharacterFiltration R G H C F n s X ι χ k hk
  exact ⟨i, k, hi⟩

end Langlands
