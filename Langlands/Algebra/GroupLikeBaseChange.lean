import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

open TensorProduct

universe u v w

namespace Langlands.GroupLike

variable {k : Type u} {K : Type v} {C : Type w}
  [Field k] [Field K] [Algebra k K]

section Coalgebra

variable [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Scalar extension sends a group-like element to its pure tensor with one. -/
theorem isGroupLikeElem_one_tmul {c : C} (hc : IsGroupLikeElem k c) :
    IsGroupLikeElem K ((1 : K) ⊗ₜ[k] c) where
  counit_eq_one := by simp [hc]
  comul_eq_tmul_self := by simp [hc]

/-- The canonical scalar-extension map on group-like elements. -/
def baseChange (g : GroupLike k C) : GroupLike K (K ⊗[k] C) :=
  ⟨1 ⊗ₜ[k] (g : C), isGroupLikeElem_one_tmul g.isGroupLikeElem_val⟩

@[simp]
theorem baseChange_val (g : GroupLike k C) :
    (baseChange (K := K) g : K ⊗[k] C) = 1 ⊗ₜ[k] (g : C) := rfl

private theorem range_val :
    Set.range (GroupLike.val (R := k) (A := C)) = {c : C | IsGroupLikeElem k c} := by
  ext c
  constructor
  · rintro ⟨g, rfl⟩
    exact g.isGroupLikeElem_val
  · intro hc
    exact ⟨⟨c, hc⟩, rfl⟩

/-- The group-like elements of a coalgebra form a basis when they span. -/
def basisOfSpan
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    Module.Basis (GroupLike k C) k C :=
  Module.Basis.mk linearIndep_groupLikeVal (by rw [range_val, hspan])

@[simp]
theorem basisOfSpan_apply
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (g : GroupLike k C) :
    basisOfSpan hspan g = (g : C) :=
  Module.Basis.mk_apply _ _ _

/-- Group-like elements already spanning a coalgebra remain a spanning family
after scalar extension. -/
theorem span_range_baseChange_val
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    Submodule.span K
      (Set.range fun g : GroupLike k C => (baseChange (K := K) g : K ⊗[k] C)) = ⊤ := by
  have hb : (fun g : GroupLike k C => (baseChange (K := K) g : K ⊗[k] C)) =
      ((basisOfSpan hspan).baseChange K : GroupLike k C → K ⊗[k] C) := by
    funext g
    simp
  rw [hb]
  exact ((basisOfSpan hspan).baseChange K).span_eq

/-- If group-like elements span, scalar extension introduces no new ones. -/
theorem baseChange_bijective
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    Function.Bijective (baseChange (k := k) (K := K) (C := C)) := by
  constructor
  · intro g h heq
    apply ((basisOfSpan hspan).baseChange K).injective
    simpa using congrArg GroupLike.val heq
  · intro g
    have hmem : (g : K ⊗[k] C) ∈
        Set.range fun h : GroupLike k C => (baseChange (K := K) h : K ⊗[k] C) := by
      by_contra hnmem
      have hli : LinearIndepOn K id
          (insert (g : K ⊗[k] C)
            (Set.range fun h : GroupLike k C => (baseChange (K := K) h : K ⊗[k] C))) :=
        linearIndepOn_isGroupLikeElem.mono (by
          rintro x (rfl | ⟨h, rfl⟩)
          · exact g.isGroupLikeElem_val
          · exact (baseChange (K := K) h).isGroupLikeElem_val)
      have hnot := hli.notMem_span_of_insert hnmem
      apply hnot
      have hm : (g : K ⊗[k] C) ∈ Submodule.span K
          (Set.range fun h : GroupLike k C => (baseChange (K := K) h : K ⊗[k] C)) := by
        rw [span_range_baseChange_val hspan]
        exact Submodule.mem_top
      exact Submodule.span_mono (by intro x hx; exact ⟨x, hx, rfl⟩) hm
    obtain ⟨h, hh⟩ := hmem
    exact ⟨h, GroupLike.val_injective hh⟩

/-- The canonical equivalence on group-like elements for a spanning coalgebra. -/
def baseChangeEquivOfSpan
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    GroupLike k C ≃ GroupLike K (K ⊗[k] C) :=
  Equiv.ofBijective baseChange (baseChange_bijective hspan)

end Coalgebra

section Bialgebra

variable [Ring C] [Bialgebra k C]

/-- The scalar-extension map on group-like elements preserves multiplication. -/
def baseChangeMonoidHom : GroupLike k C →* GroupLike K (K ⊗[k] C) where
  toFun := baseChange
  map_one' := by
    apply GroupLike.val_injective
    simp [Algebra.TensorProduct.one_def]
  map_mul' g h := by
    apply GroupLike.val_injective
    simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- For a bialgebra spanned by group-like elements, scalar extension induces a
multiplicative equivalence on group-like elements. -/
def baseChangeMulEquivOfSpan
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    GroupLike k C ≃* GroupLike K (K ⊗[k] C) :=
  MulEquiv.ofBijective baseChangeMonoidHom (baseChange_bijective hspan)

@[simp]
theorem baseChangeMulEquivOfSpan_apply
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (g : GroupLike k C) :
    baseChangeMulEquivOfSpan (K := K) hspan g = baseChange (K := K) g := rfl

end Bialgebra

end Langlands.GroupLike
