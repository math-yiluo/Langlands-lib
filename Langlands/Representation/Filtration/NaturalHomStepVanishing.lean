import Langlands.Representation.Filtration.HomVanishingFiltration

/-! # Vanishing of a natural map on the steps of a functor filtration -/

open CategoryTheory

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {F D : C ⥤ Rep.{uV} R G} {n : ℕ}

/-- The restriction of `h` to the step `i.succ`, descended to the graded piece `i`, provided
that `h` vanishes on the step `i.castSucc`. -/
def stepDescent (s : RepFunctorFiltration F n) (X : C) (h : F.obj X ⟶ D.obj X) (i : Fin n)
    (hi : ∀ v ∈ (s.step i.castSucc).obj X, h.hom v = 0) :
    (s.graded i).obj X ⟶ D.obj X :=
  s.gradedDescent X (D.obj X) i h hi

theorem stepDescent_projection (s : RepFunctorFiltration F n) (X : C)
    (h : F.obj X ⟶ D.obj X) (i : Fin n)
    (hi : ∀ v ∈ (s.step i.castSucc).obj X, h.hom v = 0)
    (v : (s.step i.succ).representation X) :
    (s.stepDescent X h i hi).hom
        (((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom v) =
      h.hom v.1 :=
  rfl

/-- The descent of a map commuting with all endomorphisms of `X` commutes with them on the
graded piece. -/
theorem stepDescent_natural (s : RepFunctorFiltration F n) (X : C)
    (h : F.obj X ⟶ D.obj X) (hh : ∀ a : X ⟶ X, F.map a ≫ h = h ≫ D.map a) (i : Fin n)
    (hi : ∀ v ∈ (s.step i.castSucc).obj X, h.hom v = 0) (a : X ⟶ X) :
    (s.graded i).map a ≫ s.stepDescent X h i hi = s.stepDescent X h i hi ≫ D.map a := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ :=
    (s.step i.castSucc).quotientProjection_surjective (s.step i.succ) X v
  have := congrArg (fun f => f.hom v.1) (hh a)
  change h.hom ((F.map a).hom v.1) = (D.map a).hom (h.hom v.1)
  exact this

/-- Let `h : F X ⟶ D X` commute with every endomorphism of `X`. If, on every graded piece
below `k`, each map to `D X` commuting with all endomorphisms of `X` is zero, then `h`
vanishes on the step `k`. -/
theorem hom_apply_eq_zero_of_mem_step (s : RepFunctorFiltration F n) (X : C)
    (h : F.obj X ⟶ D.obj X) (hh : ∀ a : X ⟶ X, F.map a ≫ h = h ≫ D.map a)
    (hg : ∀ i : Fin n, ∀ g : (s.graded i).obj X ⟶ D.obj X,
      (∀ a : X ⟶ X, (s.graded i).map a ≫ g = g ≫ D.map a) → g = 0) :
    ∀ k : Fin (n + 1), ∀ v ∈ (s.step k).obj X, h.hom v = 0 := by
  intro k
  induction k using Fin.induction with
  | zero =>
    intro v hv
    rw [s.zero X] at hv
    have hv0 : v = 0 := (Submodule.mem_bot R).mp hv
    rw [hv0, map_zero]
  | succ i ih =>
    intro v hv
    have hz := hg i (s.stepDescent X h i ih) (s.stepDescent_natural X h hh i ih)
    exact (s.stepDescent_projection X h i ih ⟨v, hv⟩).symm.trans (by rw [hz]; rfl)

/-- Variant of `hom_apply_eq_zero_of_mem_step` that only uses the graded pieces strictly
below `k`. -/
theorem hom_apply_eq_zero_of_mem_step_of_lt (s : RepFunctorFiltration F n) (X : C)
    (h : F.obj X ⟶ D.obj X) (hh : ∀ a : X ⟶ X, F.map a ≫ h = h ≫ D.map a)
    (k : Fin (n + 1))
    (hg : ∀ i : Fin n, i.val < k.val → ∀ g : (s.graded i).obj X ⟶ D.obj X,
      (∀ a : X ⟶ X, (s.graded i).map a ≫ g = g ≫ D.map a) → g = 0) :
    ∀ v ∈ (s.step k).obj X, h.hom v = 0 := by
  have key : ∀ j : ℕ, ∀ hj : j < n + 1, j ≤ k.val →
      ∀ v ∈ (s.step ⟨j, hj⟩).obj X, h.hom v = 0 := by
    intro j
    induction j with
    | zero =>
      intro hj _ v hv
      have h0 : (⟨0, hj⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, s.zero X] at hv
      have hv0 : v = 0 := (Submodule.mem_bot R).mp hv
      rw [hv0, map_zero]
    | succ j ih =>
      intro hj hjk v hv
      let i : Fin n := ⟨j, by omega⟩
      have ih' : ∀ w ∈ (s.step i.castSucc).obj X, h.hom w = 0 :=
        ih (by omega) (by omega)
      have hz := hg i (by change j < k.val; omega) (s.stepDescent X h i ih')
        (s.stepDescent_natural X h hh i ih')
      have hsucc : (⟨j + 1, hj⟩ : Fin (n + 1)) = i.succ := rfl
      rw [hsucc] at hv
      exact (s.stepDescent_projection X h i ih' ⟨v, hv⟩).symm.trans (by rw [hz]; rfl)
  exact key k.val k.isLt le_rfl

end Langlands.RepFunctorFiltration
