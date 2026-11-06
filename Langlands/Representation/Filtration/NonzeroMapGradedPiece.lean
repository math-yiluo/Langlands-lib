import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! Nonzero maps out of a finitely filtered representation factor through a graded piece. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uW uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {W : Type uW} [AddCommGroup W] [Module R W] {σ : Representation R G W} {n : ℕ}

namespace ObjectRepFiltration

variable {A : Rep.{uV} R G}

/-- Restrict the domain of an intertwiner to a filtration step. -/
def restrictToStep (s : ObjectRepFiltration A n) (f : A.ρ.IntertwiningMap σ)
    (i : Fin (n + 1)) :
    (s.subrepresentation i).toRepresentation.IntertwiningMap σ where
  toLinearMap := f.toLinearMap.comp (s.subrepresentation i).toSubmodule.subtype
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v

@[simp]
theorem restrictToStep_apply (s : ObjectRepFiltration A n) (f : A.ρ.IntertwiningMap σ)
    (i : Fin (n + 1)) (v : (s.subrepresentation i).toSubmodule) :
    s.restrictToStep f i v = f v := rfl

/-- An intertwiner vanishing on the lower step descends from the upper step to the
actual graded quotient. -/
def mapFromGraded (s : ObjectRepFiltration A n) (f : A.ρ.IntertwiningMap σ) (i : Fin n)
    (h : ∀ v ∈ s.subrepresentation i.castSucc, f v = 0) :
    (s.gradedRepresentation i).ρ.IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (s.restrictToStep f i.succ).toLinearMap
    (fun (v : (s.subrepresentation i.succ).toSubmodule) hv => h v hv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v

@[simp]
theorem mapFromGraded_projection (s : ObjectRepFiltration A n) (f : A.ρ.IntertwiningMap σ)
    (i : Fin n) (h : ∀ v ∈ s.subrepresentation i.castSucc, f v = 0)
    (v : (s.subrepresentation i.succ).toSubmodule) :
    s.mapFromGraded f i h ((s.gradedProjection i).hom v) = f v := rfl

/-- A nonzero map out of a finitely filtered representation induces a nonzero map
out of an actual graded piece: take the first step on which it does not vanish. -/
theorem exists_mapFromGraded_ne_zero (s : ObjectRepFiltration A n)
    (f : A.ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ∀ v ∈ s.subrepresentation i.castSucc, f v = 0),
      s.mapFromGraded f i h ≠ 0 := by
  classical
  let P (i : Fin (n + 1)) : Prop := ∀ v ∈ s.subrepresentation i, f v = 0
  have hzero : P 0 := by
    intro v hv
    rw [s.subrepresentation_zero] at hv
    rw [(Submodule.mem_bot R).mp hv, map_zero]
  have hlast : ¬ P (Fin.last n) := by
    intro h
    apply hf
    ext v
    exact h v (by rw [s.subrepresentation_last]; exact Submodule.mem_top)
  have hstep : ∃ i : Fin n, P i.castSucc ∧ ¬ P i.succ := by
    by_contra h
    push Not at h
    exact hlast (Fin.induction hzero h (Fin.last n))
  obtain ⟨i, hlower, hupper⟩ := hstep
  refine ⟨i, hlower, ?_⟩
  intro hz
  apply hupper
  intro v hv
  have := s.mapFromGraded_projection f i hlower ⟨v, hv⟩
  rw [hz] at this
  exact this.symm

end ObjectRepFiltration

namespace RepFunctorFiltration

variable {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

/-- At every input, a nonzero map out of the filtered functor's value induces a
nonzero map out of the value of an actual graded quotient functor. -/
theorem exists_graded_intertwiningMap_ne_zero (s : RepFunctorFiltration F n) (X : C)
    (f : (F.obj X).ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ((s.graded i).obj X).ρ.IntertwiningMap σ), h ≠ 0 := by
  obtain ⟨i, h, hi⟩ := (s.atObject X).exists_mapFromGraded_ne_zero f hf
  exact ⟨i, _, hi⟩

/-- The same conclusion for any supplied functors isomorphic to the graded quotients. -/
theorem exists_piece_intertwiningMap_ne_zero (s : RepFunctorFiltration F n)
    {pieces : Fin n → C ⥤ Rep.{uV} R G} (hs : s.HasGradedPieces pieces) (X : C)
    (f : (F.obj X).ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ((pieces i).obj X).ρ.IntertwiningMap σ), h ≠ 0 := by
  obtain ⟨i, h, hi⟩ := s.exists_graded_intertwiningMap_ne_zero X f hf
  obtain ⟨φ⟩ := hs i
  refine ⟨i, h.comp (φ.inv.app X).hom, ?_⟩
  intro hz
  apply hi
  ext v
  have := congrArg (fun t => t ((φ.hom.app X).hom v)) hz
  simpa [Representation.IntertwiningMap.comp_apply, Rep.inv_hom_apply (e := φ.app X)] using this

end RepFunctorFiltration

/-- If a functor is glued from a finite list of pieces, a nonzero map out of one of
its values induces a nonzero map out of the value of some piece. -/
theorem IsGluedFrom.exists_piece_intertwiningMap_ne_zero {C : Type uC} [Category.{vC} C]
    {F : C ⥤ Rep.{uV} R G} {pieces : Fin n → C ⥤ Rep.{uV} R G}
    (hF : IsGluedFrom F pieces) (X : C)
    (f : (F.obj X).ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ((pieces i).obj X).ρ.IntertwiningMap σ), h ≠ 0 := by
  obtain ⟨e, s, hs⟩ := hF
  obtain ⟨i, h, hi⟩ := s.exists_piece_intertwiningMap_ne_zero hs X f hf
  exact ⟨e i, h, hi⟩

end Langlands
