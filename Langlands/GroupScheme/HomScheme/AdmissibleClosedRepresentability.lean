import Langlands.GroupScheme.HomScheme.AdmissibleSchemeLocality
import Langlands.GroupScheme.HomScheme.AdmissibleSheaf

/-! # Closed scheme representatives of actual subgroup membership -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- An actual scheme morphism represents the subgroup's absolute membership
condition on every test scheme. -/
def IsSchemeRepresentedBy {Z : Scheme.{u}} (j : Z ⟶ G.X.left) : Prop :=
  ∀ (Y : Scheme.{u}) (x : Y ⟶ G.X.left),
    F.schemeCondition x ↔ ∃ b : Y ⟶ Z, b ≫ j = x

/-- Local admissible subgroups give closed representatives of the absolute
membership condition over the induced cover of the ambient scheme. -/
theorem exists_localClosedSubscheme (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, TorusSubgroupModuli.IsAdmissible (F.baseChange (𝒰.f i)))
    (i : 𝒰.I₀) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ (𝒰.pullback₁ G.X.hom).X i),
      IsClosedImmersion j ∧ ∀ (Y : Scheme.{u}) (a : Y ⟶ (𝒰.pullback₁ G.X.hom).X i),
        F.schemeCondition (a ≫ (𝒰.pullback₁ G.X.hom).f i) ↔
          ∃ b : Y ⟶ Z, b ≫ j = a := by
  let r := TorusSubgroupModuli.admissibleRepresentative ⟨F.baseChange (𝒰.f i), h i⟩
  refine ⟨r.group.X.left, r.hom.hom.hom.left, r.closed, ?_⟩
  intro Y a
  exact (F.schemeCondition_baseChange_iff (𝒰.f i) a).trans
    (schemeCondition_iff_exists_of_isRepresentedBy
      (G := (GroupScheme.baseChange (𝒰.f i)).obj G) (F.baseChange (𝒰.f i)) r.represents a)

/-- A closed scheme representative of the absolute membership condition
constructs the actual representing closed group subscheme. -/
theorem isClosedRepresentable_of_schemeCondition
    {Z : Scheme.{u}} (j : Z ⟶ G.X.left) [IsClosedImmersion j]
    (h : F.IsSchemeRepresentedBy j) : F.IsClosedRepresentable := by
  let W : Over S := Over.mk (j ≫ G.X.hom)
  let a : W ⟶ G.X := Over.homMk j rfl
  have : IsClosedImmersion a.left := ‹IsClosedImmersion j›
  apply F.isClosedRepresentable_of_scheme a
  intro T x
  rw [← F.schemeCondition_iff_mem x, h T.left x.left]
  constructor
  · rintro ⟨b, hb⟩
    let b' : T ⟶ W := Over.homMk b (by
      change b ≫ (j ≫ G.X.hom) = T.hom
      rw [← Category.assoc, hb]
      exact Over.w x)
    exact ⟨b', Over.OverMorphism.ext hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.left, congrArg (fun f => f.left) hb⟩

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {T : Over S}

/-- Closed representability is the remaining geometric step in effective
admissible descent; the torus property then follows from the local families. -/
theorem isAdmissible_matchingSubgroup_of_isClosedRepresentable
    (𝒰 : Scheme.OpenCover.{u} T.left)
    (F : ∀ i, AdmissibleSubgroup
      ((baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G))
    (hF : IsMatchingAdmissible 𝒰 F)
    (hc : (matchingSubgroup 𝒰 F).IsClosedRepresentable) :
    IsAdmissible (matchingSubgroup 𝒰 F) := by
  apply isAdmissible_of_isClosedRepresentable_of_openCover hc 𝒰
  intro i
  rw [baseChange_matchingSubgroup 𝒰 F hF i]
  exact (coverSubgroup 𝒰 F i).property

end Langlands.GroupScheme.TorusSubgroupModuli
