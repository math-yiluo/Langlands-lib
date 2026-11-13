import Langlands.Representation.Filtration.Definitions

/-! # The vanishing filtration on maps out of a filtered functor value

For a natural finite filtration `0 = F₀ X ⊆ ⋯ ⊆ Fₙ X = F X` and a target `Y`, the maps
`F X ⟶ Y` vanishing on `Fᵢ X` form a decreasing filtration of `Hom(F X, Y)`. A map vanishing
on `Fⱼ X` descends to the graded piece `Fⱼ₊₁ X / Fⱼ X`; it vanishes on `Fⱼ₊₁ X` exactly when
the descended map is zero, and descent commutes with precomposition by `F.map a`. When every
graded projection has a section, every map out of a graded piece is such a descent.
-/

noncomputable section

open CategoryTheory

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G] {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} R G} {n : ℕ}

/-- Maps out of `F X` vanishing on the `i`-th step of the filtration. -/
def homVanishing (s : RepFunctorFiltration F n) (X : C) (Y : Rep.{uV} R G)
    (i : Fin (n + 1)) : AddSubgroup (F.obj X ⟶ Y) where
  carrier := {f | ∀ v ∈ (s.step i).obj X, f.hom v = 0}
  add_mem' := by
    intro f g hf hg v hv
    simp [Rep.add_hom, hf v hv, hg v hv]
  zero_mem' := by
    intro _ _
    rfl
  neg_mem' := by
    intro f hf v hv
    simp [Rep.neg_hom, hf v hv]

variable (s : RepFunctorFiltration F n) (X : C) (Y : Rep.{uV} R G)

theorem mem_homVanishing {i : Fin (n + 1)} {f : F.obj X ⟶ Y} :
    f ∈ s.homVanishing X Y i ↔ ∀ v ∈ (s.step i).obj X, f.hom v = 0 :=
  Iff.rfl

theorem homVanishing_zero : s.homVanishing X Y 0 = ⊤ := by
  refine eq_top_iff.mpr fun f _ v hv => ?_
  rw [s.zero X] at hv
  have hv' : v = 0 := hv
  rw [hv', map_zero]

theorem homVanishing_last : s.homVanishing X Y (Fin.last n) = ⊥ := by
  refine eq_bot_iff.mpr fun f hf => ?_
  rw [AddSubgroup.mem_bot]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv : v ∈ (s.step (Fin.last n)).obj X := by
    rw [s.top X]
    exact trivial
  exact hf v hv

theorem homVanishing_succ_le (j : Fin n) :
    s.homVanishing X Y j.succ ≤ s.homVanishing X Y j.castSucc :=
  fun _ hf v hv => hf v (s.step_le_next X j hv)

variable {X Y} in
theorem map_comp_mem_homVanishing {X' : C} (a : X' ⟶ X) {i : Fin (n + 1)}
    {f : F.obj X ⟶ Y} (hf : f ∈ s.homVanishing X Y i) :
    F.map a ≫ f ∈ s.homVanishing X' Y i :=
  fun _ hv => hf _ ((s.step i).map_mem a hv)

/-- The projection of step `j + 1` onto the graded piece `Fⱼ₊₁ X / Fⱼ X`, typed with the
graded functor as codomain. -/
def gradedProjection (j : Fin n) :
    (s.step j.succ).representation X ⟶ (s.graded j).obj X :=
  (s.step j.castSucc).quotientProjection (s.step j.succ) X

theorem gradedProjection_surjective (j : Fin n) :
    Function.Surjective (s.gradedProjection X j).hom :=
  (s.step j.castSucc).quotientProjection_surjective (s.step j.succ) X

theorem gradedProjection_eq_zero_iff (j : Fin n) (w : (s.step j.succ).representation X) :
    (s.gradedProjection X j).hom w = 0 ↔ w.1 ∈ (s.step j.castSucc).obj X :=
  Submodule.Quotient.mk_eq_zero _

/-- A map vanishing on `Fⱼ X` descended to the graded piece `Fⱼ₊₁ X / Fⱼ X`. -/
def gradedDescent (j : Fin n) (f : F.obj X ⟶ Y) (hf : f ∈ s.homVanishing X Y j.castSucc) :
    (s.graded j).obj X ⟶ Y :=
  Rep.ofHom
    { toLinearMap := ((s.step j.castSucc).lowerInUpper (s.step j.succ) X).toSubmodule.liftQ
        (f.hom.toLinearMap ∘ₗ ((s.step j.succ).obj X).toSubmodule.subtype)
        (fun v hv => hf v.1 hv)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
        exact Rep.hom_comm_apply f g v.1 }

theorem gradedDescent_projection (j : Fin n) (f : F.obj X ⟶ Y)
    (hf : f ∈ s.homVanishing X Y j.castSucc) (v : (s.step j.succ).representation X) :
    (s.gradedDescent X Y j f hf).hom ((s.gradedProjection X j).hom v) = f.hom v.1 :=
  rfl

theorem gradedDescent_ext (j : Fin n) {g g' : (s.graded j).obj X ⟶ Y}
    (h : ∀ v : (s.step j.succ).representation X,
      g.hom ((s.gradedProjection X j).hom v) = g'.hom ((s.gradedProjection X j).hom v)) :
    g = g' := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := s.gradedProjection_surjective X j q
  exact h v

theorem gradedDescent_eq_zero_iff (j : Fin n) (f : F.obj X ⟶ Y)
    (hf : f ∈ s.homVanishing X Y j.castSucc) :
    s.gradedDescent X Y j f hf = 0 ↔ f ∈ s.homVanishing X Y j.succ := by
  constructor
  · intro h v hv
    have := congrArg (fun t : (s.graded j).obj X ⟶ Y => t.hom
      ((s.gradedProjection X j).hom ⟨v, hv⟩)) h
    exact this
  · intro h
    exact s.gradedDescent_ext X Y j fun v => h v.1 v.2

theorem gradedDescent_sub (j : Fin n) (f g : F.obj X ⟶ Y)
    (hf : f ∈ s.homVanishing X Y j.castSucc) (hg : g ∈ s.homVanishing X Y j.castSucc) :
    s.gradedDescent X Y j (f - g) (sub_mem hf hg) =
      s.gradedDescent X Y j f hf - s.gradedDescent X Y j g hg :=
  s.gradedDescent_ext X Y j fun _ => rfl

variable {X Y} in
theorem gradedDescent_map_comp {X' : C} (a : X' ⟶ X) (j : Fin n) (f : F.obj X ⟶ Y)
    (hf : f ∈ s.homVanishing X Y j.castSucc) :
    s.gradedDescent X' Y j (F.map a ≫ f) (s.map_comp_mem_homVanishing a hf) =
      (s.graded j).map a ≫ s.gradedDescent X Y j f hf :=
  s.gradedDescent_ext X' Y j fun _ => rfl

/-- The last step of the filtration is everything: the identification of `F X` with it. -/
def toLastStep : F.obj X ⟶ (s.step (Fin.last n)).representation X :=
  Rep.ofHom
    { toLinearMap := LinearMap.codRestrict ((s.step (Fin.last n)).obj X).toSubmodule
        LinearMap.id (fun v => by
          have hv : v ∈ (s.step (Fin.last n)).obj X := by
            rw [s.top X]
            exact trivial
          exact hv)
      isIntertwining' := fun _ => rfl }

variable {X} in
/-- Given a section `σ` of the graded projection at step `k`, the retraction of step `k + 1`
onto step `k` sending `w` to `w - σ (p w)`. -/
def stepRetraction (k : Fin n)
    (σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X)
    (hσ : σ ≫ s.gradedProjection X k = 𝟙 _) :
    (s.step k.succ).representation X ⟶ (s.step k.castSucc).representation X :=
  Rep.ofHom
    { toLinearMap := LinearMap.codRestrict ((s.step k.castSucc).obj X).toSubmodule
        (((s.step k.succ).obj X).toSubmodule.subtype ∘ₗ
          (LinearMap.id - σ.hom.toLinearMap ∘ₗ (s.gradedProjection X k).hom.toLinearMap))
        (fun w => by
          have hp : (s.gradedProjection X k).hom
              (w - σ.hom ((s.gradedProjection X k).hom w)) = 0 := by
            rw [map_sub]
            have h := congrArg (fun t => t.hom ((s.gradedProjection X k).hom w)) hσ
            simp only [Rep.hom_comp] at h
            erw [h]
            exact sub_self _
          exact (s.gradedProjection_eq_zero_iff X k _).mp hp)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        show Subtype.val (((s.step k.succ).representation X).ρ g w -
            σ.hom ((s.gradedProjection X k).hom (((s.step k.succ).representation X).ρ g w))) =
          Subtype.val (((s.step k.succ).representation X).ρ g
            (w - σ.hom ((s.gradedProjection X k).hom w)))
        rw [Rep.hom_comm_apply, Rep.hom_comm_apply, map_sub] }

variable {X} in
theorem stepRetraction_apply_of_mem (k : Fin n)
    (σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X)
    (hσ : σ ≫ s.gradedProjection X k = 𝟙 _)
    (v : (s.step k.castSucc).representation X) :
    (s.stepRetraction k σ hσ).hom ⟨v.1, s.step_le_next X k v.2⟩ = v := by
  apply Subtype.ext
  have hp : (s.gradedProjection X k).hom ⟨v.1, s.step_le_next X k v.2⟩ = 0 :=
    (s.gradedProjection_eq_zero_iff X k _).mpr v.2
  change v.1 - (σ.hom ((s.gradedProjection X k).hom ⟨v.1, s.step_le_next X k v.2⟩)).1 = v.1
  rw [hp, map_zero]
  exact sub_zero _

/-- If every graded projection has a section, every map out of a step of the filtration
extends to a map out of `F X`. -/
theorem exists_extension_of_sections
    (hsec : ∀ k : Fin n, ∃ σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X,
      σ ≫ s.gradedProjection X k = 𝟙 _)
    (m : Fin (n + 1)) (h : (s.step m).representation X ⟶ Y) :
    ∃ f : F.obj X ⟶ Y, ∀ v : (s.step m).representation X, f.hom v.1 = h.hom v := by
  induction m using Fin.reverseInduction with
  | last =>
    exact ⟨s.toLastStep X ≫ h, fun v => rfl⟩
  | cast k ih =>
    obtain ⟨σ, hσ⟩ := hsec k
    obtain ⟨f, hf⟩ := ih (s.stepRetraction k σ hσ ≫ h)
    refine ⟨f, fun v => ?_⟩
    have h1 := hf ⟨v.1, s.step_le_next X k v.2⟩
    rw [Rep.hom_comp] at h1
    erw [h1]
    change h.hom ((s.stepRetraction k σ hσ).hom ⟨v.1, s.step_le_next X k v.2⟩) = h.hom v
    rw [s.stepRetraction_apply_of_mem k σ hσ v]

/-- If every graded projection has a section, every map out of a graded piece is the descent
of a map out of `F X` vanishing on the previous step. -/
theorem exists_gradedDescent_eq_of_sections
    (hsec : ∀ k : Fin n, ∃ σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X,
      σ ≫ s.gradedProjection X k = 𝟙 _)
    (j : Fin n) (g : (s.graded j).obj X ⟶ Y) :
    ∃ (f : F.obj X ⟶ Y) (hf : f ∈ s.homVanishing X Y j.castSucc),
      s.gradedDescent X Y j f hf = g := by
  obtain ⟨f, hf⟩ := s.exists_extension_of_sections X Y hsec j.succ (s.gradedProjection X j ≫ g)
  have hvan : f ∈ s.homVanishing X Y j.castSucc := by
    intro v hv
    refine (hf ⟨v, s.step_le_next X j hv⟩).trans ?_
    have hp : (s.gradedProjection X j).hom ⟨v, s.step_le_next X j hv⟩ = 0 :=
      (s.gradedProjection_eq_zero_iff X j _).mpr hv
    change g.hom ((s.gradedProjection X j).hom ⟨v, s.step_le_next X j hv⟩) = 0
    rw [hp, map_zero]
  refine ⟨f, hvan, s.gradedDescent_ext X Y j fun w => ?_⟩
  rw [gradedDescent_projection, hf w]
  rfl

end Langlands.RepFunctorFiltration
