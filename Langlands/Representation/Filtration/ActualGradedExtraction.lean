import Langlands.Representation.Filtration.SmoothGradedObject
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Filtration.SubsingletonProof

/-! Actual smooth graded quotients and extraction of an irreducible subquotient
from an arbitrary finite filtration. -/

noncomputable section

open CategoryTheory

namespace Langlands.ObjectRepFiltration

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{uK, uG, uV} k G} {r : ℕ}

/-- The actual smooth quotient of the next step by the current step, using the
same invariant subspaces and quotient action as `gradedRepresentation`. -/
abbrev smoothGradedObject (s : ObjectRepFiltration A.obj r) (j : Fin r) :
    SmoothRep.{uK, uG, uV} k G :=
  SmoothRep.IrreducibleGrothendieckProof.gradedSmooth s j

@[simp]
theorem smoothGradedObject_representation
    (s : ObjectRepFiltration A.obj r) (j : Fin r) :
    (s.smoothGradedObject j).representation = (s.gradedRepresentation j).ρ := rfl

/-- Descend an actual smooth intertwiner across its supplied invariant kernel. -/
private def quotientLift {X Y : SmoothRep.{uK, uG, uV} k G}
    (S : Subrepresentation X.representation) (f : X ⟶ Y)
    (h : S.toSubmodule ≤ (SmoothRep.hom f).toLinearMap.ker) :
    SmoothRep.quotient X S ⟶ Y :=
  SmoothRep.ofHom {
    toLinearMap := S.toSubmodule.liftQ (SmoothRep.hom f).toLinearMap h
    isIntertwining' g := by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g v }

/-- An irreducible actual smooth subquotient of a finite filtered object is an
actual subquotient of one actual smooth graded quotient. The graded quotients
need not be simple, nonzero, admissible or of finite length. -/
theorem exists_smoothGradedObject_subquotient
    (s : ObjectRepFiltration A.obj r) {D : SmoothRep.{uK, uG, uV} k G}
    (hD : D.IsIrreducible) (hDA : SmoothRep.IsSubquotient D A) :
    ∃ j : Fin r, SmoothRep.IsSubquotient D (s.smoothGradedObject j) := by
  classical
  let : D.representation.IsIrreducible := hD
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra k G) D.representation.asModule
  obtain ⟨S, U, ⟨e⟩⟩ := hDA
  let f : SmoothRep.subrepresentation A S ⟶ D :=
    SmoothRep.mkQ (SmoothRep.subrepresentation A S) U ≫ e.inv
  have hf : Function.Surjective (SmoothRep.hom f) :=
    (SmoothRep.hom_hom_surjective e.symm).comp (SmoothRep.mkQ_surjective _ U)
  let P (i : Fin (r + 1)) : Prop :=
    ∀ x : S.toSubmodule, (x : A) ∈ s.subrepresentation i →
      SmoothRep.hom f x = 0
  have hzero : P 0 := by
    intro x hx
    rw [s.subrepresentation_zero] at hx
    have hx0 : x = 0 := Subtype.ext hx
    rw [hx0]
    exact (SmoothRep.hom f).toLinearMap.map_zero
  have hlast : ¬ P (Fin.last r) := by
    intro h
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨x, rfl⟩ := hf d
    exact hd (h x (by rw [s.subrepresentation_last]; trivial))
  have hstep : ∃ j : Fin r, P j.castSucc ∧ ¬ P j.succ := by
    by_contra h
    have hnext : ∀ j : Fin r, P j.castSucc → P j.succ := by
      intro j hj
      by_contra hj'
      exact h ⟨j, hj, hj'⟩
    exact hlast (Fin.induction hzero hnext (Fin.last r))
  obtain ⟨j, hj, hj'⟩ := hstep
  change ¬ (∀ x : S.toSubmodule, (x : A) ∈ s.subrepresentation j.succ →
    SmoothRep.hom f x = 0) at hj'
  push Not at hj'
  obtain ⟨x, hx, hfx⟩ := hj'
  let X : Subrepresentation A.representation := S ⊓ s.subrepresentation j.succ
  let iS : SmoothRep.subrepresentation A X ⟶ SmoothRep.subrepresentation A S :=
    SmoothRep.ofHom {
      toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.1⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let iT : SmoothRep.subrepresentation A X ⟶
      SmoothRep.subrepresentation A (s.subrepresentation j.succ) :=
    SmoothRep.ofHom {
      toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let q : SmoothRep.subrepresentation A X ⟶ s.smoothGradedObject j :=
    iT ≫ SmoothRep.mkQ _ _
  let fX : SmoothRep.subrepresentation A X ⟶ D := iS ≫ f
  have hker : (SmoothRep.hom q).toLinearMap.ker ≤
      (SmoothRep.hom fX).toLinearMap.ker := by
    intro v hv
    exact hj (SmoothRep.hom iS v)
      ((s.gradedProjection_eq_zero_iff j (SmoothRep.hom iT v)).mp hv)
  let v : X.toSubmodule := ⟨x.val, x.property, hx⟩
  have hfv : SmoothRep.hom fX v ≠ 0 := hfx
  have hfn : SmoothRep.hom fX ≠ 0 := by
    intro hz
    apply hfv
    rw [hz]
    rfl
  have hfs : Function.Surjective (SmoothRep.hom fX) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom fX)).resolve_right hfn
  let K := (SmoothRep.hom q).ker
  let q' := quotientLift K q le_rfl
  let f' := quotientLift K fX hker
  refine ⟨j, SmoothRep.isSubquotient_iff_exists.mpr
    ⟨SmoothRep.quotient (SmoothRep.subrepresentation A X) K, q', f', ?_, ?_⟩⟩
  · change Function.Injective (K.toSubmodule.liftQ (SmoothRep.hom q).toLinearMap le_rfl)
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  · intro d
    obtain ⟨y, hy⟩ := hfs d
    exact ⟨SmoothRep.hom (SmoothRep.mkQ _ K) y, hy⟩

end Langlands.ObjectRepFiltration
