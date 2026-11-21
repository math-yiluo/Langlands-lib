import Langlands.Geometry.FormalGroup.Copies

/-! # Projections and inclusions of finite copies of a formal module -/

noncomputable section

namespace Langlands.FormalGroup.ModuleLaw.Hom

universe u v

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable (M : ModuleLaw O R Unit) {I : Type} [Finite I]

/-- The coordinate projection of a finite product is scalar-linear. -/
def copyProjection (i : I) : Hom (M.copies I) M where
  toHom := CommLaw.Hom.copyProjection i
  commutes a := CommLaw.Hom.copyProjection_comp_diagonal (fun _ => M.action a) i

variable [DecidableEq I]

/-- Include a line into one component of its finite product. -/
def copyInclusion (i : I) : Hom M (M.copies I) := by
  let f (j : I) : CommLaw.Hom M.groupLaw M.groupLaw :=
    if j = i then CommLaw.Hom.id M.groupLaw else 0
  refine ⟨CommLaw.Hom.toCopies f, ?_⟩
  intro a
  apply CommLaw.Hom.ext_copyProjection
  intro j
  change (CommLaw.Hom.copyProjection j).comp ((CommLaw.Hom.toCopies f).comp (M.action a)) =
    (CommLaw.Hom.copyProjection j).comp
      ((CommLaw.Hom.diagonal (fun _ : I => M.action a)).comp (CommLaw.Hom.toCopies f))
  rw [← CommLaw.Hom.comp_assoc, CommLaw.Hom.copyProjection_comp_toCopies,
    ← CommLaw.Hom.comp_assoc, CommLaw.Hom.copyProjection_comp_diagonal,
    CommLaw.Hom.comp_assoc, CommLaw.Hom.copyProjection_comp_toCopies]
  by_cases h : j = i <;> simp [f, h]

@[simp]
theorem copyProjection_comp_copyInclusion (i j : I) :
    (copyProjection M i).comp (copyInclusion M j) = if i = j then id M else 0 := by
  apply Hom.ext
  change (CommLaw.Hom.copyProjection i).comp (CommLaw.Hom.toCopies fun k : I =>
    if k = j then CommLaw.Hom.id M.groupLaw else 0) = _
  rw [CommLaw.Hom.copyProjection_comp_toCopies]
  split_ifs <;> rfl

omit [DecidableEq I] in
/-- Equality of scalar-linear maps into a product is detected by the projections. -/
theorem ext_copyProjection {σ : Type} [Finite σ] {N : ModuleLaw O R σ} {f g : Hom N (M.copies I)}
    (h : ∀ i : I, (copyProjection M i).comp f = (copyProjection M i).comp g) : f = g := by
  apply Hom.ext
  apply CommLaw.Hom.ext_copyProjection
  intro i
  exact congrArg Hom.toHom (h i)

/-- The finite sum of the projections followed by their inclusions is the identity. -/
theorem sum_copyInclusion_comp_copyProjection [Fintype I] :
    (∑ i : I, (copyInclusion M i).comp (copyProjection M i)) = id (M.copies I) := by
  apply ext_copyProjection (I := I) M
  intro j
  let b := compLinear (M := M.copies I) (copyProjection M j)
  change b (∑ i : I, (copyInclusion M i).comp (copyProjection M i)) = _
  rw [map_sum, comp_id]
  calc
    _ = b ((copyInclusion M j).comp (copyProjection M j)) := by
      rw [Finset.sum_eq_single j]
      · intro i _ hi
        change (copyProjection M j).comp ((copyInclusion M i).comp (copyProjection M i)) = 0
        rw [← comp_assoc, copyProjection_comp_copyInclusion]
        simp [hi.symm]
      · simp
    _ = _ := by
      change (copyProjection M j).comp ((copyInclusion M j).comp (copyProjection M j)) = _
      rw [← comp_assoc, copyProjection_comp_copyInclusion]
      simp

end Langlands.FormalGroup.ModuleLaw.Hom
