import Langlands.Representation.Filtration.IrreducibleEmbedding
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Exponents.Central

/-! A single isolated generalized central block in an actual finite filtration. -/

noncomputable section

namespace Langlands.ObjectRepFiltration

universe uK uG uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {E : Rep.{uV} k G} {W : Type uW} [AddCommGroup W] [Module k W]
  {ρ : Representation k G W} {n : ℕ}

private theorem mem_lower_of_excluded (s : ObjectRepFiltration E n)
    (χ : Subgroup.center G →* kˣ) (j : Fin n)
    (hex : ¬ IsGeneralizedEigencharacter
      ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ)
    {v : E} (hv : v ∈ generalizedCentralCharacterSpace E.ρ χ)
    (hstep : v ∈ s.subrepresentation j.succ) :
    v ∈ s.subrepresentation j.castSucc := by
  obtain ⟨m, hm⟩ := (mem_generalizedCentralCharacterSpace E.ρ χ v).mp hv
  have hchar : v ∈ characterSpace (E.ρ.comp (Subgroup.center G).subtype) χ m :=
    (mem_characterSpace _ χ m v).mpr hm
  let q : Representation.IntertwiningMap
      ((s.subrepresentation j.succ).toRepresentation.comp (Subgroup.center G).subtype)
      ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) :=
    { toLinearMap := (s.gradedProjection j).hom.toLinearMap
      isIntertwining' z := (s.gradedProjection j).hom.isIntertwining' (z : G) }
  have hw : (⟨v, hstep⟩ : (s.subrepresentation j.succ).toSubmodule) ∈
      characterSpace
        ((s.subrepresentation j.succ).toRepresentation.comp (Subgroup.center G).subtype)
        χ m :=
    (mem_characterSpace_subrepresentation_comp E.ρ (s.subrepresentation j.succ)
      (Subgroup.center G).subtype χ m ⟨v, hstep⟩).mpr hchar
  have hq : q ⟨v, hstep⟩ = 0 := by
    by_contra hq
    exact hex (isGeneralizedEigencharacter_of_map_ne_zero q χ m hw hq)
  exact (s.gradedProjection_eq_zero_iff j ⟨v, hstep⟩).mp hq

/-- A central character excluded from every grade except one has no vector
in the lower step and all its generalized vectors in the upper step. -/
theorem isolatedCentralCharacter_steps (s : ObjectRepFiltration E n)
    (χ : Subgroup.center G →* kˣ) (j₀ : Fin n)
    (hex : ∀ j : Fin n, j ≠ j₀ → ¬ IsGeneralizedEigencharacter
      ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ) :
    (∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ →
      v ∈ s.subrepresentation j₀.castSucc → v = 0) ∧
    generalizedCentralCharacterSpace E.ρ χ ≤ s.subrepresentation j₀.succ := by
  have hlow : ∀ j : Fin (n + 1), j.val ≤ j₀.val →
      ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ →
        v ∈ s.subrepresentation j → v = 0 := by
    intro j
    induction j using Fin.induction with
    | zero =>
        intro _ v _ hv
        rw [s.subrepresentation_zero] at hv
        exact (Submodule.mem_bot k).mp hv
    | succ j ih =>
        intro hj v hv hstep
        simp only [Fin.val_succ, Fin.val_castSucc] at hj ih
        apply ih (by omega) v hv
        exact mem_lower_of_excluded s χ j (hex j (by intro h; subst j; omega)) hv hstep
  have hupp : ∀ j : Fin (n + 1), j₀.val < j.val →
      generalizedCentralCharacterSpace E.ρ χ ≤ s.subrepresentation j := by
    intro j
    induction j using Fin.reverseInduction with
    | last =>
        intro _ v _
        rw [s.subrepresentation_last]
        exact Submodule.mem_top
    | cast j ih =>
        intro hj v hv
        simp only [Fin.val_succ, Fin.val_castSucc] at hj ih
        exact mem_lower_of_excluded s χ j (hex j (by intro h; subst j; omega)) hv
          (ih (by omega) hv)
  exact ⟨hlow j₀.castSucc (by simp), hupp j₀.succ (by simp)⟩

/-- A nonzero embedding of a scalar-central source identifies its entire
uniform generalized central block when the only possible grade is irreducible.
The resulting equivalence has the supplied embedding as its underlying map. -/
def isolatedCentralCharacterEquiv (s : ObjectRepFiltration E n)
    (χ : Subgroup.center G →* kˣ) (j₀ : Fin n)
    (hex : ∀ j : Fin n, j ≠ j₀ → ¬ IsGeneralizedEigencharacter
      ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ)
    (hgrade : Representation.IsIrreducible (s.gradedRepresentation j₀).ρ)
    (hρ : ∀ (z : Subgroup.center G) (w : W), ρ (z : G) w = (χ z : k) • w)
    (i : ρ.IntertwiningMap E.ρ) (hi : Function.Injective i) (hi₀ : i ≠ 0) :
    ρ.Equiv (generalizedCentralCharacterSpace E.ρ χ).toRepresentation := by
  classical
  let P := generalizedCentralCharacterSpace E.ρ χ
  have hsteps := isolatedCentralCharacter_steps s χ j₀ hex
  let inc : P.toRepresentation.IntertwiningMap E.ρ :=
    { toLinearMap := P.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let hupper : ∀ v : P, inc v ∈ s.subrepresentation j₀.succ :=
    fun v => hsteps.2 v.property
  let q := s.mapToGraded inc j₀ hupper
  have hqinj : Function.Injective q := by
    refine (injective_iff_map_eq_zero q).mpr fun v hv => ?_
    apply Subtype.ext
    exact hsteps.1 v v.property
      ((s.mapToGraded_eq_zero_iff inc j₀ hupper v).mp hv)
  have himem : ∀ w : W, i w ∈ P := by
    intro w
    exact map_mem_generalizedCentralCharacterSpace i χ
      ((mem_generalizedCentralCharacterSpace ρ χ w).mpr
        ⟨1, (mem_centralCharacterSpace ρ χ 1 w).mp
          ((mem_centralCharacterSpace_one ρ χ w).mpr (fun z => hρ z w))⟩)
  let ic : ρ.IntertwiningMap P.toRepresentation :=
    { toLinearMap := i.toLinearMap.codRestrict P.toSubmodule himem
      isIntertwining' g := by
        ext w
        exact Representation.IntertwiningMap.isIntertwining _ _ i g w }
  have hicinj : Function.Injective ic := by
    intro v w hvw
    exact hi (congrArg Subtype.val hvw)
  have hqic : q.comp ic ≠ 0 := by
    intro hzero
    apply hi₀
    ext w
    have hw : ic w = 0 := hqinj (by
      change (q.comp ic) w = q 0
      rw [hzero, map_zero]
      rfl)
    exact congrArg Subtype.val hw
  letI := hgrade
  have hqsurj : Function.Surjective (q.comp ic) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (q.comp ic)).resolve_right hqic
  have hicsurj : Function.Surjective ic := by
    intro v
    obtain ⟨w, hw⟩ := hqsurj (q v)
    exact ⟨w, hqinj hw⟩
  exact ic.ofBijective ⟨hicinj, hicsurj⟩

@[simp]
theorem isolatedCentralCharacterEquiv_apply_coe (s : ObjectRepFiltration E n)
    (χ : Subgroup.center G →* kˣ) (j₀ : Fin n)
    (hex : ∀ j : Fin n, j ≠ j₀ → ¬ IsGeneralizedEigencharacter
      ((s.gradedRepresentation j).ρ.comp (Subgroup.center G).subtype) χ)
    (hgrade : Representation.IsIrreducible (s.gradedRepresentation j₀).ρ)
    (hρ : ∀ (z : Subgroup.center G) (w : W), ρ (z : G) w = (χ z : k) • w)
    (i : ρ.IntertwiningMap E.ρ) (hi : Function.Injective i) (hi₀ : i ≠ 0) (w : W) :
    (isolatedCentralCharacterEquiv s χ j₀ hex hgrade hρ i hi hi₀ w : E) = i w := rfl

end Langlands.ObjectRepFiltration
