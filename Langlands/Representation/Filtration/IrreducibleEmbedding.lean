import Langlands.Representation.Filtration.SubsingletonProof

/-! Irreducible embeddings into actual graded pieces of a supplied filtration. -/

namespace Langlands.ObjectRepFiltration

universe uR uG uV uW

section Ring

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {A : Rep.{uV} R G} {W : Type uW} [AddCommGroup W] [Module R W]
  {ρ : Representation R G W} {n : ℕ}

/-- Restrict the codomain of an intertwiner to a filtration step containing its image. -/
def mapToStep (s : ObjectRepFiltration A n) (f : ρ.IntertwiningMap A.ρ)
    (i : Fin (n + 1)) (h : ∀ v, f v ∈ s.subrepresentation i) :
    ρ.IntertwiningMap (s.subrepresentation i).toRepresentation where
  toLinearMap := f.toLinearMap.codRestrict _ h
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v

@[simp]
theorem mapToStep_apply_coe (s : ObjectRepFiltration A n)
    (f : ρ.IntertwiningMap A.ρ) (i : Fin (n + 1))
    (h : ∀ v, f v ∈ s.subrepresentation i) (v : W) :
    (s.mapToStep f i h v : A) = f v := rfl

/-- Compose codomain restriction to the upper step with the actual graded projection. -/
def mapToGraded (s : ObjectRepFiltration A n) (f : ρ.IntertwiningMap A.ρ)
    (i : Fin n) (h : ∀ v, f v ∈ s.subrepresentation i.succ) :
    ρ.IntertwiningMap (s.gradedRepresentation i).ρ :=
  (s.gradedProjection i).hom.comp (s.mapToStep f i.succ h)

/-- The induced graded map kills precisely the vectors mapped into the lower step. -/
theorem mapToGraded_eq_zero_iff (s : ObjectRepFiltration A n)
    (f : ρ.IntertwiningMap A.ρ) (i : Fin n)
    (h : ∀ v, f v ∈ s.subrepresentation i.succ) (v : W) :
    s.mapToGraded f i h v = 0 ↔ f v ∈ s.subrepresentation i.castSucc :=
  s.gradedProjection_eq_zero_iff i (s.mapToStep f i.succ h v)

/-- A nonzero map into a supplied finite filtered representation induces a
nonzero map to an actual graded piece. No simplicity of any piece is required. -/
theorem exists_mapToGraded_ne_zero (s : ObjectRepFiltration A n)
    (f : ρ.IntertwiningMap A.ρ) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ∀ v, f v ∈ s.subrepresentation i.succ),
      s.mapToGraded f i h ≠ 0 := by
  classical
  let P (i : Fin (n + 1)) : Prop := ∀ v, f v ∈ s.subrepresentation i
  have hzero : ¬ P 0 := by
    intro h
    apply hf
    ext v
    have hv := h v
    rw [s.subrepresentation_zero] at hv
    exact (Submodule.mem_bot R).mp hv
  have hlast : P (Fin.last n) := by
    intro v
    rw [s.subrepresentation_last]
    exact Submodule.mem_top
  have hstep : ∃ i : Fin n, ¬ P i.castSucc ∧ P i.succ := by
    by_contra h
    have hnext : ∀ i : Fin n, ¬ P i.castSucc → ¬ P i.succ := by
      intro i hi hi'
      exact h ⟨i, hi, hi'⟩
    have hnlast : ¬ P (Fin.last n) := Fin.induction hzero hnext (Fin.last n)
    exact hnlast hlast
  obtain ⟨i, hlower, hupper⟩ := hstep
  refine ⟨i, hupper, ?_⟩
  intro hz
  apply hlower
  intro v
  apply (s.mapToGraded_eq_zero_iff f i hupper v).mp
  rw [hz]
  rfl

end Ring

section Field

variable {k : Type uR} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uV} k G} {W : Type uW} [AddCommGroup W] [Module k W]
  {ρ : Representation k G W} {n : ℕ}

/-- A nonzero map from an irreducible representation embeds it into an actual
graded piece, through the specified original map and the actual quotient projection. -/
theorem exists_injective_mapToGraded (s : ObjectRepFiltration A n)
    (f : ρ.IntertwiningMap A.ρ) (hρ : ρ.IsIrreducible) (hf : f ≠ 0) :
    ∃ (i : Fin n) (h : ∀ v, f v ∈ s.subrepresentation i.succ),
      Function.Injective (s.mapToGraded f i h) := by
  let := hρ
  obtain ⟨i, h, hi⟩ := s.exists_mapToGraded_ne_zero f hf
  exact ⟨i, h,
    (Representation.IsIrreducible.injective_or_eq_zero (s.mapToGraded f i h)).resolve_right hi⟩

/-- A supplied actual embedding of an irreducible representation into the
filtered ambient representation yields an actual embedding into a graded piece. -/
theorem exists_injective_graded (s : ObjectRepFiltration A n)
    (f : ρ.IntertwiningMap A.ρ) (hρ : ρ.IsIrreducible) (hf : Function.Injective f) :
    ∃ i : Fin n, ∃ g : ρ.IntertwiningMap (s.gradedRepresentation i).ρ,
      Function.Injective g := by
  let := hρ
  let : Nontrivial W :=
    IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  have hf0 : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    apply hf
    rw [hz]
    rfl
  obtain ⟨i, h, hi⟩ := s.exists_injective_mapToGraded f hρ hf0
  exact ⟨i, s.mapToGraded f i h, hi⟩

end Field

end Langlands.ObjectRepFiltration
