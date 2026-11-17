import Langlands.GroupScheme.Torus.LocalCoefficientReindexing

/-! # Pullback and composition of locally reindexed coefficients -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalCoefficientReindexing

variable {S T : Scheme.{u}} {I J K : Type u}

/-- Pairwise intersections of two open covers still cover the scheme. -/
theorem intersection_covers {α β : Type u} (U : α → S.Opens) (V : β → S.Opens)
    (hU : (⨆ a, U a) = ⊤) (hV : (⨆ b, V b) = ⊤) :
    (⨆ p : α × β, U p.1 ⊓ V p.2) = ⊤ := by
  apply top_unique
  intro s _
  have hsU : s ∈ ⨆ a, U a := by rw [hU]; trivial
  have hsV : s ∈ ⨆ b, V b := by rw [hV]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hsU
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hsV
  exact (le_iSup (fun p : α × β => U p.1 ⊓ V p.2) (a, b)) ⟨ha, hb⟩

namespace Datum

/-- Pullback of local coefficient permutations along an arbitrary morphism. -/
def pullback (D : Datum S I J) (f : T ⟶ S) : Datum T I J where
  Index := D.Index
  opens a := f ⁻¹ᵁ D.opens a
  covers := by rw [← f.preimage_iSup, D.covers]; rfl
  permutation := D.permutation
  agree a b h := D.agree a b (by
    obtain ⟨t⟩ := h
    exact ⟨⟨f t.1, t.2⟩⟩)

/-- Restriction of a pulled-back global section is the pullback of its
restriction. -/
theorem restrict_appTop (f : T ⟶ S) (U : S.Opens) (z : Γ(S, ⊤)) :
    restrict (show f ⁻¹ᵁ U ≤ ⊤ from le_top) (f.appTop.hom z) =
      (f.app U).hom (restrict (show U ≤ ⊤ from le_top) z) := by
  exact (congrArg (fun k : Γ(S, ⊤) ⟶ Γ(T, f ⁻¹ᵁ U) => k.hom z)
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)).symm

/-- The coefficient equivalence commutes with pullback of global sections. -/
theorem equiv_pullback (D : Datum S I J) (f : T ⟶ S)
    (z : I → Γ(S, ⊤)) (j : J) :
    (D.pullback f).equiv (fun i => f.appTop.hom (z i)) j =
      f.appTop.hom (D.equiv z j) := by
  apply (D.pullback f).sections_ext
  intro a
  rw [equiv_restrict]
  change restrict (show f ⁻¹ᵁ D.opens a ≤ ⊤ from le_top)
      (f.appTop.hom (z (D.permutation a j))) =
    restrict (show f ⁻¹ᵁ D.opens a ≤ ⊤ from le_top) (f.appTop.hom (D.equiv z j))
  rw [restrict_appTop, restrict_appTop, D.equiv_restrict]

/-- Composition uses the intersection cover and composite local permutations. -/
def comp (D : Datum S I J) (E : Datum S J K) : Datum S I K where
  Index := D.Index × E.Index
  opens p := D.opens p.1 ⊓ E.opens p.2
  covers := intersection_covers D.opens E.opens D.covers E.covers
  permutation p := (E.permutation p.2).trans (D.permutation p.1)
  agree p q h := by
    obtain ⟨s⟩ := h
    have hD : D.permutation p.1 = D.permutation q.1 :=
      D.agree p.1 q.1 ⟨⟨s.1, s.2.1.1, s.2.2.1⟩⟩
    have hE : E.permutation p.2 = E.permutation q.2 :=
      E.agree p.2 q.2 ⟨⟨s.1, s.2.1.2, s.2.2.2⟩⟩
    rw [hD, hE]

/-- The composite global map has the expected formula on each intersection. -/
theorem comp_restrict (D : Datum S I J) (E : Datum S J K)
    (z : I → Γ(S, ⊤)) (k : K) (a : D.Index) (b : E.Index) :
    restrict (show D.opens a ⊓ E.opens b ≤ ⊤ from le_top) (E.equiv (D.equiv z) k) =
      restrict le_top (z (D.permutation a (E.permutation b k))) := by
  calc
    _ = restrict inf_le_right
        (restrict (show E.opens b ≤ ⊤ from le_top) (E.equiv (D.equiv z) k)) :=
      (restrict_restrict _ _ _).symm
    _ = restrict inf_le_right
        (restrict (show E.opens b ≤ ⊤ from le_top) (D.equiv z (E.permutation b k))) := by
      rw [E.equiv_restrict]
    _ = restrict inf_le_left
        (restrict (show D.opens a ≤ ⊤ from le_top) (D.equiv z (E.permutation b k))) := by
      rw [restrict_restrict, restrict_restrict]
    _ = restrict inf_le_left
        (restrict (show D.opens a ≤ ⊤ from le_top)
          (z (D.permutation a (E.permutation b k)))) := by
      rw [D.equiv_restrict]
    _ = _ := restrict_restrict _ _ _

/-- Gluing respects composition of local permutations. -/
theorem equiv_comp (D : Datum S I J) (E : Datum S J K) :
    (D.comp E).equiv = D.equiv.trans E.equiv := by
  ext z k
  apply (D.comp E).sections_ext
  intro p
  exact ((D.comp E).equiv_restrict z k p).trans (D.comp_restrict E z k p.1 p.2).symm

/-- The glued map depends only on local permutations wherever their opens meet. -/
theorem equiv_eq_of_agree (D E : Datum S I J)
    (h : ∀ a b, Nonempty ((D.opens a ⊓ E.opens b : S.Opens) : Scheme.{u}) →
      D.permutation a = E.permutation b) : D.equiv = E.equiv := by
  ext z j
  apply S.sheaf.eq_of_locally_eq'
    (fun p : D.Index × E.Index => D.opens p.1 ⊓ E.opens p.2) ⊤
    (fun _ => homOfLE le_top)
    (intersection_covers D.opens E.opens D.covers E.covers).ge
  intro p
  change restrict (show D.opens p.1 ⊓ E.opens p.2 ≤ ⊤ from le_top) (D.equiv z j) =
    restrict le_top (E.equiv z j)
  cases isEmpty_or_nonempty ((D.opens p.1 ⊓ E.opens p.2 : S.Opens) : Scheme.{u}) with
  | inl he =>
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    exact (he.false ⟨x, hx⟩).elim
  | inr hn =>
    calc
      _ = restrict inf_le_left
          (restrict (show D.opens p.1 ≤ ⊤ from le_top) (D.equiv z j)) :=
        (restrict_restrict _ _ _).symm
      _ = restrict le_top (z (D.permutation p.1 j)) := by
        rw [D.equiv_restrict, restrict_restrict]
      _ = restrict le_top (z (E.permutation p.2 j)) := by rw [h p.1 p.2 hn]
      _ = restrict inf_le_right
          (restrict (show E.opens p.2 ≤ ⊤ from le_top) (E.equiv z j)) := by
        rw [E.equiv_restrict, restrict_restrict]
      _ = _ := restrict_restrict _ _ _

/-- A single transformation on unit families determines its glued coefficient
map, independently of the chosen cover and local permutations. -/
theorem equiv_eq_of_unitTransform (D E : Datum S I J)
    (F : ∀ T : Over S, (I → (Γ(T.left, ⊤))ˣ) → (J → (Γ(T.left, ⊤))ˣ))
    (hD : ∀ a (T : Over S), Set.range T.hom ⊆ D.opens a →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (D.permutation a j))
    (hE : ∀ b (T : Over S), Set.range T.hom ⊆ E.opens b →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (E.permutation b j)) :
    D.equiv = E.equiv :=
  D.equiv_eq_of_agree E (fun a b =>
    permutation_eq_of_unitTests F (D.permutation a) (E.permutation b) (hD a) (hE b))

end Datum
end Langlands.GroupScheme.LocalCoefficientReindexing
