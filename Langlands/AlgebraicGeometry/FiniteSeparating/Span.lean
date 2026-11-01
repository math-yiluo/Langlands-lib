import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation

/-! # `K`-linear spans of finite sets of sections

For a scheme `X` over a field `K` and a line bundle `L`, a section is in the span of a finite
set `S` of global sections when it is a `K`-linear combination of the elements of `S`, with
`K` acting through `scalarsFromBase p`. The span of `S` agrees with the span of the family
`enum S : Fin (S.card + 1) → GlobalSections L.obj`, which lists the zero section followed by
the elements of `S`. `SeparatesAt p L S x` says that the span of `S` separates the rational
point `x` from every other rational point and from every nonzero tangent vector at `x`.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteSeparating

variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
  (L : LineBundle X)

/-- `σ` is a `K`-linear combination of the sections in the finite set `S`. -/
def InSpan (S : Finset (GlobalSections L.obj)) (σ : GlobalSections L.obj) : Prop :=
  ∃ c : GlobalSections L.obj → K, σ = ∑ s ∈ S, Scheme.Modules.scalarsFromBase p (c s) • s

variable {p L}

lemma InSpan.mono {S S' : Finset (GlobalSections L.obj)} (h : S ⊆ S')
    {σ : GlobalSections L.obj} (hσ : InSpan p L S σ) : InSpan p L S' σ := by
  classical
  obtain ⟨c, rfl⟩ := hσ
  refine ⟨fun s ↦ if s ∈ S then c s else 0, ?_⟩
  rw [← Finset.sum_subset h fun s _ hs ↦ by dsimp only; rw [ite_eq_right hs, map_zero, zero_smul]]
  exact Finset.sum_congr rfl fun s hs ↦ by dsimp only; rw [ite_eq_left hs]

lemma inSpan_of_mem {S : Finset (GlobalSections L.obj)} {σ : GlobalSections L.obj}
    (h : σ ∈ S) : InSpan p L S σ := by
  classical
  refine ⟨fun s ↦ if s = σ then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single σ]
  · dsimp only
    rw [ite_eq_left rfl, map_one, one_smul]
  · intro s _ hs
    dsimp only
    rw [ite_eq_right hs, map_zero, zero_smul]
  · intro hσ
    exact absurd h hσ

/-- The zero section followed by an enumeration of `S`. -/
def enum (S : Finset (GlobalSections L.obj)) : Fin (S.card + 1) → GlobalSections L.obj :=
  Fin.cons 0 fun i ↦ (S.equivFin.symm i : GlobalSections L.obj)

lemma enum_zero (S : Finset (GlobalSections L.obj)) : enum S 0 = 0 :=
  Fin.cons_zero _ _

lemma enum_succ (S : Finset (GlobalSections L.obj)) (i : Fin S.card) :
    enum S i.succ = S.equivFin.symm i :=
  Fin.cons_succ _ _ _

lemma exists_enum_eq {S : Finset (GlobalSections L.obj)} {σ : GlobalSections L.obj}
    (h : σ ∈ S) : ∃ i, enum S i = σ :=
  ⟨(S.equivFin ⟨σ, h⟩).succ, by rw [enum_succ, Equiv.symm_apply_apply]⟩

lemma sum_eq_sum_equivFin {M : Type*} [AddCommMonoid M] (S : Finset (GlobalSections L.obj))
    (f : GlobalSections L.obj → M) :
    ∑ s ∈ S, f s = ∑ i : Fin S.card, f (S.equivFin.symm i) :=
  (Finset.sum_coe_sort S f).symm.trans (Equiv.sum_comp S.equivFin.symm fun s : S ↦ f s).symm

lemma sum_enum (S : Finset (GlobalSections L.obj)) (a : Fin (S.card + 1) → K) :
    ∑ i, Scheme.Modules.scalarsFromBase p (a i) • enum S i =
      ∑ i : Fin S.card, Scheme.Modules.scalarsFromBase p (a i.succ) •
        (S.equivFin.symm i : GlobalSections L.obj) := by
  rw [Fin.sum_univ_succ, enum_zero, smul_zero, zero_add]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [enum_succ]

/-- The span of `S` is the set of `K`-linear combinations of `enum S`. -/
lemma inSpan_iff (S : Finset (GlobalSections L.obj)) (σ : GlobalSections L.obj) :
    InSpan p L S σ ↔
      ∃ a : Fin (S.card + 1) → K, σ = ∑ i, Scheme.Modules.scalarsFromBase p (a i) • enum S i := by
  classical
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Fin.cons 0 fun i ↦ c (S.equivFin.symm i), ?_⟩
    rw [sum_enum, sum_eq_sum_equivFin]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Fin.cons_succ]
  · rintro ⟨a, rfl⟩
    refine ⟨fun s ↦ if h : s ∈ S then a (S.equivFin ⟨s, h⟩).succ else 0, ?_⟩
    rw [sum_enum, sum_eq_sum_equivFin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [dite_eq_left (S.equivFin.symm i).2, Subtype.coe_eta, Equiv.apply_symm_apply]

variable (p L) in
/-- The span of `S` separates the rational point `x` from every other rational point and
from every nonzero rational tangent vector at `x`. -/
def SeparatesAt (S : Finset (GlobalSections L.obj)) (x : Spec (CommRingCat.of K) ⟶ X) : Prop :=
  (∀ y : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p y → x ≠ y →
      ∃ σ, InSpan p L S σ ∧ VanishesAlong L x σ ∧ ¬ VanishesAlong L y σ) ∧
    (∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ X, IsNonzeroTangentVectorAt p x t →
      ∃ σ, InSpan p L S σ ∧ VanishesAlong L x σ ∧ ¬ VanishesAlong L t σ)

lemma SeparatesAt.mono {S S' : Finset (GlobalSections L.obj)} (h : S ⊆ S')
    {x : Spec (CommRingCat.of K) ⟶ X} (hS : SeparatesAt p L S x) : SeparatesAt p L S' x :=
  ⟨fun y hy hne ↦
      let ⟨σ, h₁, h₂, h₃⟩ := hS.1 y hy hne
      ⟨σ, h₁.mono h, h₂, h₃⟩,
    fun t ht ↦
      let ⟨σ, h₁, h₂, h₃⟩ := hS.2 t ht
      ⟨σ, h₁.mono h, h₂, h₃⟩⟩

end Langlands.AlgebraicGeometry.FiniteSeparating
