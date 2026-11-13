import Langlands.Representation.Filtration.HomVanishingFiltration
import Langlands.Algebra.FilteredRankOneExpansion
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # A basis of maps out of a filtered functor value, from rank-one graded pieces

Let `F : C ⥤ Rep R G` be an additive functor on a preadditive category with a natural finite
filtration `s`, and fix objects `X` of `C` and `Y` of `Rep R G`. The ring `(End X)ᵐᵒᵖ` acts on
`F X ⟶ Y` by precomposition with `F.map`. Assume that every graded projection of `s` at `X` has
a section, and that each graded piece is either rank one or invisible: for `j ∈ S` there is a
map `θ j` out of the `j`th graded piece such that `a ↦ (s.graded j).map a ≫ θ j` is a bijection
from `End X` onto the maps from the graded piece to `Y`, and for `j ∉ S` every map from the
graded piece to `Y` is zero. Then `F X ⟶ Y` is free over `(End X)ᵐᵒᵖ` with a basis indexed
by `S`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G] {C : Type uC} [Category.{vC} C]
  [Preadditive C] (F : C ⥤ Rep.{uV} R G) [F.Additive]

/-- The left `(End X)ᵐᵒᵖ`-module structure on `F X ⟶ Y` given by precomposition with `F.map`:
`op a • f = F.map a ≫ f`. -/
@[instance_reducible]
def precompModule (X : C) (Y : Rep.{uV} R G) : Module (End X)ᵐᵒᵖ (F.obj X ⟶ Y) where
  smul a f := F.map a.unop ≫ f
  one_smul f := by
    change F.map (𝟙 X) ≫ f = f
    rw [F.map_id, Category.id_comp]
  mul_smul a b f := by
    change F.map (b.unop * a.unop) ≫ f = F.map a.unop ≫ F.map b.unop ≫ f
    rw [End.mul_def, F.map_comp, Category.assoc]
  smul_zero _ := comp_zero
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  add_smul a b f := by
    change F.map (a.unop + b.unop) ≫ f = F.map a.unop ≫ f + F.map b.unop ≫ f
    rw [F.map_add, Preadditive.add_comp]
  zero_smul f := by
    change F.map (0 : X ⟶ X) ≫ f = 0
    rw [F.map_zero, zero_comp]

theorem precompModule_smul (X : C) (Y : Rep.{uV} R G) (a : (End X)ᵐᵒᵖ) (f : F.obj X ⟶ Y) :
    letI := precompModule F X Y
    a • f = F.map a.unop ≫ f :=
  rfl

variable {F} {n : ℕ}

/-- The vanishing filtration `homVanishing` as a filtration by `(End X)ᵐᵒᵖ`-submodules. -/
def homVanishingSubmodule (s : RepFunctorFiltration F n) (X : C) (Y : Rep.{uV} R G)
    (i : Fin (n + 1)) :
    letI := precompModule F X Y
    Submodule (End X)ᵐᵒᵖ (F.obj X ⟶ Y) :=
  letI := precompModule F X Y
  { carrier := s.homVanishing X Y i
    add_mem' := fun hf hg => add_mem hf hg
    zero_mem' := zero_mem _
    smul_mem' := fun a _ hf => s.map_comp_mem_homVanishing a.unop hf }

theorem mem_homVanishingSubmodule (s : RepFunctorFiltration F n) (X : C) (Y : Rep.{uV} R G)
    (i : Fin (n + 1)) (f : F.obj X ⟶ Y) :
    f ∈ s.homVanishingSubmodule X Y i ↔ f ∈ s.homVanishing X Y i :=
  Iff.rfl

section Basis

variable (s : RepFunctorFiltration F n) (X : C) (Y : Rep.{uV} R G)
  (hsec : ∀ k : Fin n, ∃ σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X,
    σ ≫ s.gradedProjection X k = 𝟙 _)
  (θ : ∀ j : Fin n, (s.graded j).obj X ⟶ Y)

/-- A lift of `θ j`: a map `F X ⟶ Y` vanishing on step `j` whose graded descent is `θ j`. -/
def gradedLift (j : Fin n) : F.obj X ⟶ Y :=
  Classical.choose (s.exists_gradedDescent_eq_of_sections X Y hsec j (θ j))

omit [Preadditive C] [F.Additive] in
theorem gradedLift_mem (j : Fin n) :
    s.gradedLift X Y hsec θ j ∈ s.homVanishing X Y j.castSucc :=
  (Classical.choose_spec (s.exists_gradedDescent_eq_of_sections X Y hsec j (θ j))).1

omit [Preadditive C] [F.Additive] in
theorem gradedDescent_gradedLift (j : Fin n) :
    s.gradedDescent X Y j (s.gradedLift X Y hsec θ j) (s.gradedLift_mem X Y hsec θ j) = θ j :=
  (Classical.choose_spec (s.exists_gradedDescent_eq_of_sections X Y hsec j (θ j))).2

variable (S : Finset (Fin n))
  (hθ : ∀ j ∈ S, Function.Bijective (fun a : X ⟶ X => (s.graded j).map a ≫ θ j))
  (hzero : ∀ j ∉ S, ∀ g : (s.graded j).obj X ⟶ Y, g = 0)

include hθ in
/-- On a rank-one step, each element of step `j` of the vanishing filtration has a unique
coefficient. -/
theorem existsUnique_sub_smul_gradedLift_mem (j : Fin n) (hj : j ∈ S) (x : F.obj X ⟶ Y)
    (hx : x ∈ s.homVanishing X Y j.castSucc) :
    letI := precompModule F X Y
    ∃! a : (End X)ᵐᵒᵖ, x - a • s.gradedLift X Y hsec θ j ∈ s.homVanishing X Y j.succ := by
  let _ := precompModule F X Y
  have hv := s.gradedLift_mem X Y hsec θ j
  have hdesc := s.gradedDescent_gradedLift X Y hsec θ j
  -- the descent of `x - a • v`
  have key : ∀ a : (End X)ᵐᵒᵖ,
      x - a • s.gradedLift X Y hsec θ j ∈ s.homVanishing X Y j.succ ↔
        (s.graded j).map a.unop ≫ θ j = s.gradedDescent X Y j x hx := by
    intro a
    have hmem : F.map a.unop ≫ s.gradedLift X Y hsec θ j ∈ s.homVanishing X Y j.castSucc :=
      s.map_comp_mem_homVanishing a.unop hv
    rw [precompModule_smul, ← s.gradedDescent_eq_zero_iff X Y j _ (sub_mem hx hmem),
      s.gradedDescent_sub X Y j _ _ hx hmem, s.gradedDescent_map_comp a.unop j _ hv, hdesc,
      sub_eq_zero, eq_comm]
  obtain ⟨a₀, ha₀⟩ := (hθ j hj).2 (s.gradedDescent X Y j x hx)
  refine ⟨MulOpposite.op a₀, (key _).mpr ha₀, fun b hb => ?_⟩
  have hb' := (key b).mp hb
  apply MulOpposite.unop_injective
  exact (hθ j hj).1 (hb'.trans ha₀.symm)

omit [Preadditive C] [F.Additive] in
include hzero in
/-- On an invisible step, the vanishing filtration does not drop. -/
theorem homVanishing_castSucc_le_succ (j : Fin n) (hj : j ∉ S) :
    s.homVanishing X Y j.castSucc ≤ s.homVanishing X Y j.succ := fun x hx =>
  (s.gradedDescent_eq_zero_iff X Y j x hx).mp (hzero j hj _)

include hθ hzero in
/-- **The basis.** Under the section, rank-one and invisibility hypotheses, the lifts of the
`θ j` for `j ∈ S` form a basis of `F X ⟶ Y` over `(End X)ᵐᵒᵖ` acting by precomposition. -/
def homVanishingBasis :
    letI := precompModule F X Y
    Module.Basis S (End X)ᵐᵒᵖ (F.obj X ⟶ Y) :=
  letI := precompModule F X Y
  FilteredModule.basisOfFilteredRankOne (s.homVanishingSubmodule X Y) S
    (s.gradedLift X Y hsec θ)
    (fun j => s.homVanishing_succ_le X Y j)
    (by
      refine eq_top_iff.mpr fun f _ => ?_
      rw [mem_homVanishingSubmodule, s.homVanishing_zero X Y]
      exact AddSubgroup.mem_top f)
    (by
      refine eq_bot_iff.mpr fun f hf => ?_
      rw [mem_homVanishingSubmodule, s.homVanishing_last X Y] at hf
      exact (Submodule.mem_bot _).mpr ((AddSubgroup.mem_bot).mp hf))
    (fun j _ => s.gradedLift_mem X Y hsec θ j)
    (fun j hj x hx => s.existsUnique_sub_smul_gradedLift_mem X Y hsec θ S hθ j hj x hx)
    (fun j hj => s.homVanishing_castSucc_le_succ X Y S hzero j hj)

theorem homVanishingBasis_apply (j : S) :
    letI := precompModule F X Y
    s.homVanishingBasis X Y hsec θ S hθ hzero j = s.gradedLift X Y hsec θ j :=
  letI := precompModule F X Y
  FilteredModule.basisOfFilteredRankOne_apply _ _ _ _ _ _ _ _ _ j

/-- Every map `F X ⟶ Y` is uniquely `∑_{j ∈ S} F.map (a j) ≫ v j`, where `v j` is the basis
vector `homVanishingBasis … j`. -/
theorem existsUnique_precomp_expansion (f : F.obj X ⟶ Y) :
    ∃! a : S → (X ⟶ X),
      f = ∑ j : S, F.map (a j) ≫ s.homVanishingBasis X Y hsec θ S hθ hzero j := by
  let _ := precompModule F X Y
  let b := s.homVanishingBasis X Y hsec θ S hθ hzero
  have hsum : ∀ c : S → (End X)ᵐᵒᵖ, b.equivFun.symm c = ∑ j : S, F.map (c j).unop ≫ b j :=
    fun c => b.equivFun_symm_apply c
  refine ⟨fun j => (b.equivFun f j).unop, ?_, fun a ha => ?_⟩
  · change f = ∑ j : S, F.map (MulOpposite.op (b.equivFun f j).unop).unop ≫ b j
    simp only [MulOpposite.op_unop]
    rw [← hsum, LinearEquiv.symm_apply_apply]
  · funext j
    have h : b.equivFun.symm (fun j => MulOpposite.op (a j)) = f := by
      rw [hsum]
      exact ha.symm
    rw [← h, LinearEquiv.apply_symm_apply]
    rfl

end Basis

end Langlands.RepFunctorFiltration
