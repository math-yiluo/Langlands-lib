import Langlands.VirtualRepresentation.Weil.ExactRealization
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Representation.Filtration.ObjectDefinitions

/-! # Exact classes of actual continuous representation filtrations -/

noncomputable section

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual graded quotient of a finite filtration of a continuous object,
with continuity inherited from the upper invariant subspace. -/
def continuousFiltrationGraded (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (i : Fin n) :
    ContinuousObjects.{uG, uV} G := by
  have : Module.Finite ℂ (s.gradedRepresentation i) :=
    Module.Finite.of_surjective (s.gradedProjection i).hom.toLinearMap
      (s.gradedProjection_surjective i)
  exact ⟨of (s.gradedRepresentation i).ρ,
    isContinuous_of_surjective_intertwiner (s.gradedProjection i).hom
      (s.gradedProjection_surjective i)
      (isContinuous_subrepresentation A.property (s.subrepresentation i.succ))⟩

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A zero continuous object has zero class in the actual exact quotient. -/
theorem exactClass_eq_zero_of_subsingleton (A : ContinuousObjects.{uG, uV} G)
    [Subsingleton A.val] :
    ExactGrothendieckGroup.ofRepresentation _ A = 0 := by
  let f : A.val.representation.IntertwiningMap A.val.representation := 0
  have h : IsShortExact f f := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    ext a
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
  have hadd := ExactGrothendieckGroup.ofRepresentation_shortExact
    (fun B : FiniteRepresentation.{0, uG, uV} ℂ G => B.IsContinuous)
    (A := A) (B := A) (C := A) h
  exact add_eq_left.mp hadd.symm

/-- The upper object is the sum of an actual invariant subrepresentation and
its actual quotient, with all three objects retaining continuity. -/
theorem exactClass_eq_subrepresentation_add_quotient
    (A : ContinuousObjects.{uG, uV} G)
    (S : Subrepresentation A.val.representation) :
    ExactGrothendieckGroup.ofRepresentation _ A =
      ExactGrothendieckGroup.ofRepresentation _ (continuousSubrepresentation A S) +
      ExactGrothendieckGroup.ofRepresentation _ (continuousQuotient A S) := by
  let f : (continuousSubrepresentation A S).val.representation.IntertwiningMap
      A.val.representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let q : A.val.representation.IntertwiningMap
      (continuousQuotient A S).val.representation :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  apply ExactGrothendieckGroup.ofRepresentation_shortExact _ (f := f) (g := q)
  refine ⟨Submodule.injective_subtype _, Submodule.mkQ_surjective _, ?_⟩
  change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

/-- The zero step has zero exact class. -/
theorem exactClass_subrepresentation_bot (A : ContinuousObjects.{uG, uV} G) :
    ExactGrothendieckGroup.ofRepresentation _
      (continuousSubrepresentation A ⊥) = 0 := by
  let : Subsingleton (continuousSubrepresentation A ⊥).val :=
    ⟨by
      rintro ⟨v, hv⟩ ⟨w, hw⟩
      exact Subtype.ext ((show v = 0 from hv).trans (show w = 0 from hw).symm)⟩
  exact exactClass_eq_zero_of_subsingleton _

/-- The full invariant subspace is genuinely equivalent to the original object. -/
theorem exactClass_subrepresentation_top (A : ContinuousObjects.{uG, uV} G) :
    ExactGrothendieckGroup.ofRepresentation _
      (continuousSubrepresentation A ⊤) =
      ExactGrothendieckGroup.ofRepresentation _ A := by
  apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact
    { toLinearMap := (⊤ : Subrepresentation A.val.representation).toSubmodule.subtype
      isIntertwining' _ := rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Each actual filtration quotient gives the defining exact-class identity. -/
theorem exactClass_filtration_step (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (i : Fin n) :
    ExactGrothendieckGroup.ofRepresentation _
      (continuousSubrepresentation A (s.subrepresentation i.succ)) =
      ExactGrothendieckGroup.ofRepresentation _
        (continuousSubrepresentation A (s.subrepresentation i.castSucc)) +
      ExactGrothendieckGroup.ofRepresentation _ (continuousFiltrationGraded A s i) := by
  have hle : s.subrepresentation i.castSucc ≤ s.subrepresentation i.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ i)
  let f : (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
      (s.subrepresentation i.succ).toRepresentation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' _ := rfl }
  let q := (s.gradedProjection i).hom
  apply ExactGrothendieckGroup.ofRepresentation_shortExact _ (f := f) (g := q)
  refine ⟨Submodule.inclusion_injective hle, s.gradedProjection_surjective i, ?_⟩
  ext ⟨v, hv⟩
  constructor
  · rintro ⟨⟨w, hw⟩, hwv⟩
    have hvw : v = w := (congrArg Subtype.val hwv).symm
    subst hvw
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  · intro hq
    change Submodule.Quotient.mk _ = 0 at hq
    have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨⟨v, hq'⟩, rfl⟩

/-- Every finite zero-to-full filtration expresses the actual exact class as
the sum of the classes of its actual continuous graded quotients. -/
theorem exactClass_eq_sum_of_filtration (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) :
    ExactGrothendieckGroup.ofRepresentation _ A =
      ∑ i : Fin n,
        ExactGrothendieckGroup.ofRepresentation _ (continuousFiltrationGraded A s i) := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      ExactGrothendieckGroup.ofRepresentation _
        (continuousSubrepresentation A
          (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩)) =
        ∑ i : Fin j, ExactGrothendieckGroup.ofRepresentation _
          (continuousFiltrationGraded A s ⟨i, lt_of_lt_of_le i.isLt hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0]
      exact exactClass_subrepresentation_bot A
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← ih hjn.le]
      exact exactClass_filtration_step A s ⟨j, hjn⟩
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, exactClass_subrepresentation_top] at h
  exact h

end Langlands.VirtualRepresentation.Weil
