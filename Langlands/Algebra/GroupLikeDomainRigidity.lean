import Langlands.Algebra.GroupLikeBaseChange

/-! # Rigidity of coalgebra maps after integral scalar extension -/

noncomputable section

open TensorProduct

universe u v w

namespace Langlands.GroupLike

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [IsDomain R]
    [Algebra k R] {C : Type w} [AddCommGroup C] [Module k C] [Coalgebra k C]

omit [IsDomain R] in
/-- Integral scalar extension preserves group-like elements. -/
theorem isGroupLikeElem_one_tmul_domain {c : C} (hc : IsGroupLikeElem k c) :
    IsGroupLikeElem R ((1 : R) ⊗ₜ[k] c) where
  counit_eq_one := by simp [hc]
  comul_eq_tmul_self := by simp [hc]

/-- The canonical scalar-extension map over an integral parameter algebra. -/
def domainBaseChange (g : GroupLike k C) : GroupLike R (R ⊗[k] C) :=
  ⟨1 ⊗ₜ[k] (g : C), isGroupLikeElem_one_tmul_domain g.isGroupLikeElem_val⟩

omit [IsDomain R] in
@[simp]
theorem domainBaseChange_val (g : GroupLike k C) :
    (domainBaseChange (R := R) g : R ⊗[k] C) = 1 ⊗ₜ[k] (g : C) := rfl

/-- A spanning group-like basis acquires no new group-like elements after
extension from a field to an integral algebra. -/
theorem domainBaseChange_bijective
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    Function.Bijective (domainBaseChange (k := k) (R := R) (C := C)) := by
  classical
  let b := (basisOfSpan hspan).baseChange R
  have hb (g : GroupLike k C) : b g = (domainBaseChange (R := R) g : R ⊗[k] C) := by
    simp [b]
  constructor
  · intro g h heq
    apply b.injective
    simpa only [hb] using congrArg GroupLike.val heq
  · intro g
    have hmem : (g : R ⊗[k] C) ∈ Set.range
        (fun h : GroupLike k C => (domainBaseChange (R := R) h : R ⊗[k] C)) := by
      by_contra hnmem
      have hli : LinearIndepOn R id (insert (g : R ⊗[k] C)
          (Set.range fun h : GroupLike k C =>
            (domainBaseChange (R := R) h : R ⊗[k] C))) :=
        linearIndepOn_isGroupLikeElem.mono (by
          rintro x (rfl | ⟨h, rfl⟩)
          · exact g.isGroupLikeElem_val
          · exact (domainBaseChange h).isGroupLikeElem_val)
      apply hli.notMem_span_of_insert hnmem
      have hrange : (Set.range fun h : GroupLike k C =>
          (domainBaseChange (R := R) h : R ⊗[k] C)) = Set.range b := by
        ext x
        simp only [Set.mem_range, hb]
      have hm : (g : R ⊗[k] C) ∈ Submodule.span R
          (Set.range fun h : GroupLike k C =>
            (domainBaseChange (R := R) h : R ⊗[k] C)) := by
        rw [hrange, b.span_eq]
        exact Submodule.mem_top
      exact Submodule.span_mono (by intro x hx; exact ⟨x, hx, rfl⟩) hm
    obtain ⟨h, hh⟩ := hmem
    exact ⟨h, GroupLike.val_injective hh⟩

/-- Specializing the parameter algebra along a rational point. -/
def specialize (ε : R →ₐ[k] k) : R ⊗[k] C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ
    TensorProduct.map ε.toLinearMap LinearMap.id

omit [IsDomain R] [Coalgebra k C] in
@[simp]
theorem specialize_tmul (ε : R →ₐ[k] k) (r : R) (c : C) :
    specialize (C := C) ε (r ⊗ₜ[k] c) = ε r • c := by
  simp [specialize]

/-- A coalgebra endomorphism of an integral scalar extension of a group-like
spanned coalgebra is determined by any one rational specialization. -/
theorem endomorphism_eq_id_of_specialize
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (ε : R →ₐ[k] k) (f : R ⊗[k] C →ₗc[R] R ⊗[k] C)
    (hf : ∀ c : C, specialize ε (f (1 ⊗ₜ[k] c)) = c) :
    f = CoalgHom.id R (R ⊗[k] C) := by
  have hg (g : GroupLike k C) :
      f (1 ⊗ₜ[k] (g : C)) = 1 ⊗ₜ[k] (g : C) := by
    let g' : GroupLike R (R ⊗[k] C) :=
      ⟨f (1 ⊗ₜ[k] (g : C)),
        (isGroupLikeElem_one_tmul_domain g.isGroupLikeElem_val).map f⟩
    obtain ⟨d, hd⟩ := (domainBaseChange_bijective hspan).2 g'
    have hd' : (1 : R) ⊗ₜ[k] (d : C) = f (1 ⊗ₜ[k] (g : C)) :=
      congrArg GroupLike.val hd
    have hdc : (d : C) = (g : C) := by
      have he := congrArg (specialize ε) hd'
      simpa only [specialize_tmul, map_one, one_smul, hf] using he
    exact hd'.symm.trans (congrArg (fun c : C => (1 : R) ⊗ₜ[k] c) hdc)
  apply CoalgHom.linearMapOfClass_injective
  apply ((basisOfSpan hspan).baseChange R).ext
  intro g
  simpa using hg g

end Langlands.GroupLike
