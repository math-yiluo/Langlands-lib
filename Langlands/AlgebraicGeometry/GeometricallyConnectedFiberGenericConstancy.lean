import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberNoetherianReduction
import Mathlib.Topology.NoetherianSpace

/-! # Generic constancy and geometric-connectedness constructibility -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Boolean generic constancy on irreducible closed subsets implies
constructibility in an arbitrary Noetherian topological space. -/
theorem isConstructible_of_irreducibleClosed_genericConstancy
    {A : Type v} [TopologicalSpace A] [NoetherianSpace A] (S : Set A)
    (h : ∀ Z : Set A, IsClosed Z → IsIrreducible Z →
      ∃ U : Set A, IsOpen U ∧ (Z ∩ U).Nonempty ∧
        (Z ∩ U ⊆ S ∨ Disjoint (Z ∩ U) S)) :
    IsConstructible S := by
  classical
  have hclosed (Z : Set A) (hZ : IsClosed Z) : IsConstructible Z := by
    simpa using ((NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).compl
  have hind (Z : TopologicalSpace.Closeds A) : IsConstructible ((Z : Set A) ∩ S) := by
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih
    rcases eq_or_ne Z ⊥ with rfl | hne
    · simp
    · by_cases hirr : IsPreirreducible (Z : Set A)
      · obtain ⟨U, hU, hnonempty, hconst⟩ :=
          h Z Z.isClosed ⟨TopologicalSpace.Closeds.coe_nonempty.mpr hne, hirr⟩
        let W : TopologicalSpace.Closeds A := ⟨(Z : Set A) \ U, Z.isClosed.sdiff hU⟩
        have hlt : W < Z := by
          refine lt_iff_le_not_ge.mpr ⟨Set.sdiff_subset, ?_⟩
          intro hZW
          obtain ⟨x, hxZ, hxU⟩ := hnonempty
          exact (hZW hxZ).2 hxU
        have hW := ih W hlt
        rcases hconst with hsub | hdis
        · have heq : (Z : Set A) ∩ S =
              ((W : Set A) ∩ S) ∪ ((Z : Set A) ∩ U) := by
            ext x
            change (x ∈ (Z : Set A) ∧ x ∈ S) ↔
              ((x ∈ (Z : Set A) ∧ x ∉ U) ∧ x ∈ S) ∨
                (x ∈ (Z : Set A) ∧ x ∈ U)
            constructor
            · rintro ⟨hxZ, hxS⟩
              by_cases hxU : x ∈ U
              · exact Or.inr ⟨hxZ, hxU⟩
              · exact Or.inl ⟨⟨hxZ, hxU⟩, hxS⟩
            · rintro (⟨⟨hxZ, _⟩, hxS⟩ | ⟨hxZ, hxU⟩)
              · exact ⟨hxZ, hxS⟩
              · exact ⟨hxZ, hsub ⟨hxZ, hxU⟩⟩
          rw [heq]
          exact hW.union
            ((hclosed Z Z.isClosed).inter ((NoetherianSpace.isCompact U).isConstructible hU))
        · have heq : (Z : Set A) ∩ S = (W : Set A) ∩ S := by
            ext x
            change (x ∈ (Z : Set A) ∧ x ∈ S) ↔
              ((x ∈ (Z : Set A) ∧ x ∉ U) ∧ x ∈ S)
            constructor
            · rintro ⟨hxZ, hxS⟩
              exact ⟨⟨hxZ, fun hxU =>
                Set.disjoint_left.mp hdis ⟨hxZ, hxU⟩ hxS⟩, hxS⟩
            · rintro ⟨⟨hxZ, _⟩, hxS⟩
              exact ⟨hxZ, hxS⟩
          rw [heq]
          exact hW
      · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hirr
        obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hcover, hnot₁, hnot₂⟩ := hirr
        lift Z₁ to TopologicalSpace.Closeds A using hZ₁
        lift Z₂ to TopologicalSpace.Closeds A using hZ₂
        have h₁ := ih (Z ⊓ Z₁) (inf_lt_left.mpr hnot₁)
        have h₂ := ih (Z ⊓ Z₂) (inf_lt_left.mpr hnot₂)
        have heq : (Z : Set A) ∩ S =
            (((Z ⊓ Z₁ : TopologicalSpace.Closeds A) : Set A) ∩ S) ∪
              (((Z ⊓ Z₂ : TopologicalSpace.Closeds A) : Set A) ∩ S) := by
          ext x
          change (x ∈ (Z : Set A) ∧ x ∈ S) ↔
            ((x ∈ (Z : Set A) ∧ x ∈ (Z₁ : Set A)) ∧ x ∈ S) ∨
              ((x ∈ (Z : Set A) ∧ x ∈ (Z₂ : Set A)) ∧ x ∈ S)
          constructor
          · rintro ⟨hxZ, hxS⟩
            rcases hcover hxZ with hx₁ | hx₂
            · exact Or.inl ⟨⟨hxZ, hx₁⟩, hxS⟩
            · exact Or.inr ⟨⟨hxZ, hx₂⟩, hxS⟩
          · rintro (⟨⟨hxZ, _⟩, hxS⟩ | ⟨⟨hxZ, _⟩, hxS⟩)
            all_goals exact ⟨hxZ, hxS⟩
        rw [heq]
        exact h₁.union h₂
  simpa using hind ⊤

/-- The geometric-component-count-one consequence of Stacks Lemma 37.28.5,
expressed on each irreducible closed subset of the actual target. -/
def FiniteTypeGeometricallyConnectedFiberGenericConstancy : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set Y), IsClosed Z → IsIrreducible Z →
      ∃ U : Set Y, IsOpen U ∧ (Z ∩ U).Nonempty ∧
        (Z ∩ U ⊆ geometricallyConnectedFiberLocus f ∨
          Disjoint (Z ∩ U) (geometricallyConnectedFiberLocus f))

/-- Generic constancy supplies constructibility over every Noetherian target. -/
theorem isConstructible_geometricallyConnectedFiberLocus_of_genericConstancy
    (h : FiniteTypeGeometricallyConnectedFiberGenericConstancy.{u})
    {X Y : Scheme.{u}} [NoetherianSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    IsConstructible (geometricallyConnectedFiberLocus f) :=
  isConstructible_of_irreducibleClosed_genericConstancy _ (h f)

/-- The Noetherian affine assertion follows conditionally from generic constancy. -/
theorem noetherianAffineGeometricallyConnectedFiberConstructibility_of_genericConstancy
    (h : FiniteTypeGeometricallyConnectedFiberGenericConstancy.{u}) :
    NoetherianAffineGeometricallyConnectedFiberConstructibility.{u} := by
  intro R _ _ X f _ _ _
  exact isConstructible_geometricallyConnectedFiberLocus_of_genericConstancy h f

/-- The general finite-presentation target follows conditionally from generic constancy. -/
theorem geometricallyConnectedFiberLocalConstructibility_of_genericConstancy
    (h : FiniteTypeGeometricallyConnectedFiberGenericConstancy.{u}) :
    GeometricallyConnectedFiberLocalConstructibility.{u} :=
  geometricallyConnectedFiberLocalConstructibility_iff_noetherianAffine.mpr
    (noetherianAffineGeometricallyConnectedFiberConstructibility_of_genericConstancy h)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
