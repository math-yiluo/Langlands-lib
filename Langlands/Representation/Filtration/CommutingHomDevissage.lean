import Langlands.Representation.Filtration.HomVanishingFiltration

/-! # Commutation of all maps out of a filtered functor value, piece by piece

Let `0 = F₀ X ⊆ ⋯ ⊆ Fₙ X = F X` be a natural finite filtration, `z : X ⟶ X` and
`z_Y : Y ⟶ Y`. Suppose that every map from a graded piece `grᵢ X` to `Y` intertwines
`grᵢ(z)` with `z_Y`, and that the pieces are separated: for `j < k`, a map `d : gr_k X ⟶ Y` is
zero as soon as `gr_k(a) ≫ d = d ≫ β` for every pair `(a, β)` of endomorphisms commuting with
`z` and `z_Y` such that every map `gr_j X ⟶ Y` intertwines `gr_j(a)` with `β`. Then every map
`h : F X ⟶ Y` satisfies `F(z) ≫ h = h ≫ z_Y`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G] {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} R G} {n : ℕ}

variable (s : RepFunctorFiltration F n) {X : C} {Y : Rep.{uV} R G}

theorem comp_mem_homVanishing {i : Fin (n + 1)} {h : F.obj X ⟶ Y}
    (hh : h ∈ s.homVanishing X Y i) (β : Y ⟶ Y) : h ≫ β ∈ s.homVanishing X Y i := by
  intro v hv
  rw [Rep.hom_comp]
  change β.hom (h.hom v) = 0
  rw [hh v hv, map_zero]

theorem commutator_mem_homVanishing {i : Fin (n + 1)} {h : F.obj X ⟶ Y}
    (hh : h ∈ s.homVanishing X Y i) (a : X ⟶ X) (β : Y ⟶ Y) :
    F.map a ≫ h - h ≫ β ∈ s.homVanishing X Y i :=
  sub_mem (s.map_comp_mem_homVanishing a hh) (s.comp_mem_homVanishing hh β)

theorem gradedDescent_commutator (j : Fin n) {h : F.obj X ⟶ Y}
    (hh : h ∈ s.homVanishing X Y j.castSucc) (a : X ⟶ X) (β : Y ⟶ Y) :
    s.gradedDescent X Y j (F.map a ≫ h - h ≫ β) (s.commutator_mem_homVanishing hh a β) =
      (s.graded j).map a ≫ s.gradedDescent X Y j h hh -
        s.gradedDescent X Y j h hh ≫ β :=
  s.gradedDescent_ext X Y j fun _ => rfl

/-- The commutator `F(z) ≫ h - h ≫ z_Y` of a commutator `F(a) ≫ h - h ≫ β` is the commutator
of `F(z) ≫ h - h ≫ z_Y`, when `a` commutes with `z` and `β` with `z_Y`. -/
theorem commutator_commutator {z a : X ⟶ X} {zY β : Y ⟶ Y} (hza : a ≫ z = z ≫ a)
    (hzβ : β ≫ zY = zY ≫ β) (h : F.obj X ⟶ Y) :
    F.map z ≫ (F.map a ≫ h - h ≫ β) - (F.map a ≫ h - h ≫ β) ≫ zY =
      F.map a ≫ (F.map z ≫ h - h ≫ zY) - (F.map z ≫ h - h ≫ zY) ≫ β := by
  have h1 : F.map z ≫ F.map a = F.map a ≫ F.map z := by
    rw [← F.map_comp, ← F.map_comp, hza]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  rw [reassoc_of% h1, hzβ]
  abel

/-- **Dévissage of commutation.** Let `z : X ⟶ X` and `z_Y : Y ⟶ Y`. Suppose that every map
from a graded piece to `Y` intertwines `z` with `z_Y` (`hA`), and that for `j < k` a map
`d : gr_k X ⟶ Y` vanishes once it intertwines every pair `(a, β)` of endomorphisms commuting
with `z` and `z_Y` that is intertwined by all maps `gr_j X ⟶ Y` (`hB`). Then every map
`h : F X ⟶ Y` intertwines `F(z)` with `z_Y`. -/
theorem map_comp_eq_comp_of_graded (z : X ⟶ X) (zY : Y ⟶ Y)
    (hA : ∀ (i : Fin n) (g : (s.graded i).obj X ⟶ Y), (s.graded i).map z ≫ g = g ≫ zY)
    (hB : ∀ j k : Fin n, j < k → ∀ d : (s.graded k).obj X ⟶ Y,
      (∀ (a : X ⟶ X) (β : Y ⟶ Y), a ≫ z = z ≫ a → β ≫ zY = zY ≫ β →
        (∀ g : (s.graded j).obj X ⟶ Y, (s.graded j).map a ≫ g = g ≫ β) →
          (s.graded k).map a ≫ d = d ≫ β) → d = 0)
    (h : F.obj X ⟶ Y) : F.map z ≫ h = h ≫ zY := by
  -- `P k`: every commutator vanishes on the `k`-th step.
  have P : ∀ k : Fin (n + 1), ∀ h : F.obj X ⟶ Y,
      F.map z ≫ h - h ≫ zY ∈ s.homVanishing X Y k := by
    intro k
    induction k using Fin.induction with
    | zero => intro h; rw [s.homVanishing_zero]; trivial
    | succ k ih =>
      -- `C m`: commutators of maps vanishing on step `m ≤ k` vanish on step `k + 1`.
      have C : ∀ m : ℕ, ∀ hm : m ≤ k.val, ∀ h : F.obj X ⟶ Y,
          h ∈ s.homVanishing X Y ⟨k.val - m, by omega⟩ →
            F.map z ≫ h - h ≫ zY ∈ s.homVanishing X Y k.succ := by
        intro m
        induction m with
        | zero =>
          intro _ h hh
          have hh' : h ∈ s.homVanishing X Y k.castSucc := hh
          have hδ := s.commutator_mem_homVanishing hh' z zY
          rw [← s.gradedDescent_eq_zero_iff X Y k _ hδ, s.gradedDescent_commutator k hh' z zY,
            hA k, sub_self]
        | succ m ihm =>
          intro hm h hh
          let jj : Fin n := ⟨k.val - (m + 1), by omega⟩
          have hjk : jj < k := by
            change k.val - (m + 1) < k.val
            omega
          have hh' : h ∈ s.homVanishing X Y jj.castSucc := hh
          have hδ := ih h
          have hδ' : F.map z ≫ h - h ≫ zY ∈ s.homVanishing X Y k.castSucc := hδ
          rw [← s.gradedDescent_eq_zero_iff X Y k _ hδ']
          refine hB jj k hjk _ fun a β hza hzβ hj => ?_
          -- The commutator of `h` with `(a, β)` vanishes on step `jj + 1`.
          have hcomm : F.map a ≫ h - h ≫ β ∈ s.homVanishing X Y ⟨k.val - m, by omega⟩ := by
            have hc := s.commutator_mem_homVanishing hh' a β
            have hsucc : (⟨k.val - m, by omega⟩ : Fin (n + 1)) = jj.succ := by
              ext
              change k.val - m = k.val - (m + 1) + 1
              omega
            rw [hsucc, ← s.gradedDescent_eq_zero_iff X Y jj _ hc,
              s.gradedDescent_commutator jj hh' a β, hj, sub_self]
          have h2 := ihm (by omega) _ hcomm
          rw [commutator_commutator hza hzβ h] at h2
          have h3 := s.commutator_mem_homVanishing hδ' a β
          rw [← s.gradedDescent_eq_zero_iff X Y k _ h3,
            s.gradedDescent_commutator k hδ' a β] at h2
          exact sub_eq_zero.mp h2
      intro h
      exact C k.val le_rfl h (by
        have h0 : (⟨k.val - k.val, by omega⟩ : Fin (n + 1)) = 0 := by
          ext
          simp
        rw [h0, s.homVanishing_zero]
        trivial)
  have hlast := P (Fin.last n) h
  rw [s.homVanishing_last] at hlast
  exact sub_eq_zero.mp hlast

end Langlands.RepFunctorFiltration
