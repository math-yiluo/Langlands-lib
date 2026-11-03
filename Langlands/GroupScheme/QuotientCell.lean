import Langlands.GroupScheme.SubgroupFunctor
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Open cells in actual subgroup quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientCell

variable {S : Scheme.{u}} {G H : GroupScheme S} {X Q : Over S}
    (i : H ⟶ G) (j : X ⟶ G.X) (q : G.X ⟶ Q)

/-- Multiplication of a cell point by a point of the subgroup. -/
def multiplication : X ⊗ H.X ⟶ G.X :=
  (fst X H.X ≫ j) * (snd X H.X ≫ i.hom.hom)

@[simp] theorem lift_multiplication {T : Over S} (x : T ⟶ X) (h : T ⟶ H.X) :
    lift x h ≫ multiplication i j = (x ≫ j) * (h ≫ i.hom.hom) := by
  simp [multiplication, MonObj.comp_mul]

variable
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hf

private theorem exists_factor {T : Over S} (x : T ⟶ X) (g : T ⟶ G.X)
    (he : x ≫ j ≫ q = g ≫ q) :
    ∃ h : T ⟶ H.X, (x ≫ j) * (h ≫ i.hom.hom) = g := by
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp ((hf T (x ≫ j) g).mp
    (by simpa only [Category.assoc] using he))
  exact ⟨h, by rw [hh, mul_inv_cancel_left]⟩

/-- The inverse image of a cell in a subgroup quotient is its product with the
subgroup, using the exact fiber relation on every test scheme. -/
theorem multiplication_isPullback [Mono i.hom.hom] :
    IsPullback (multiplication i j) (fst X H.X) q (j ≫ q) := by
  have hc : multiplication i j ≫ q = fst X H.X ≫ (j ≫ q) := by
    symm
    rw [← Category.assoc]
    apply (hf (X ⊗ H.X) _ _).mpr
    rw [multiplication]
    rw [inv_mul_cancel_left]
    exact SubgroupFunctor.mem_range.mpr ⟨snd X H.X, rfl⟩
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift c.snd (Classical.choose (exists_factor i j q hf c.snd c.fst
      c.condition.symm))) ?_ ?_ ?_⟩⟩
  · intro c
    simpa only [lift_multiplication] using Classical.choose_spec
      (exists_factor i j q hf c.snd c.fst c.condition.symm)
  · intro c
    exact lift_fst _ _
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [lift_fst] using hn
    · apply (cancel_mono i.hom.hom).mp
      apply mul_left_cancel (a := c.snd ≫ j)
      have hprod : (c.snd ≫ j) * ((m ≫ snd X H.X) ≫ i.hom.hom) = c.fst := by
        simpa only [multiplication, MonObj.comp_mul, ← Category.assoc, hn] using hm
      simpa only [lift_snd, Category.assoc] using hprod.trans
        (Classical.choose_spec
          (exists_factor i j q hf c.snd c.fst c.condition.symm)).symm

/-- An open multiplication cell descends to an open immersion in an fpqc
subgroup quotient. -/
theorem isOpenImmersion [Mono i.hom.hom]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    [IsOpenImmersion (multiplication i j).left] :
    IsOpenImmersion (j ≫ q).left := by
  have hpb := (multiplication_isPullback i j q hf).map (Over.forget S)
  change IsPullback (multiplication i j).left (fst X H.X).left q.left (j ≫ q).left
    at hpb
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hpb
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

omit hf

section SectionOverImage

variable {k : Type u} [CommRing k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {X Q : Over (Spec (CommRingCat.of k))}
    (j : X ⟶ G.X) (q : G.X ⟶ Q) [IsOpenImmersion (j ≫ q).left]

/-- Invert an open cell in the quotient and then include it in the group. -/
def sectionOverImage : openOver k Q (j ≫ q).left.opensRange ⟶ G.X :=
  Over.homMk ((j ≫ q).left.isoOpensRange.inv ≫ j.left) (by
    change ((j ≫ q).left.isoOpensRange.inv ≫ j.left) ≫ G.X.hom =
      (j ≫ q).left.opensRange.ι ≫ Q.hom
    calc
      _ = (j ≫ q).left.isoOpensRange.inv ≫ X.hom := by
        rw [Category.assoc, Over.w j]
      _ = ((j ≫ q).left.isoOpensRange.inv ≫ (j ≫ q).left) ≫ Q.hom := by
        rw [Category.assoc, Over.w (j ≫ q)]
      _ = _ := by rw [Scheme.Hom.isoOpensRange_inv_comp])

/-- The constructed morphism is a section on the actual open image. -/
@[reassoc] theorem sectionOverImage_comp :
    sectionOverImage j q ≫ q = openOverι k Q (j ≫ q).left.opensRange := by
  apply Over.OverMorphism.ext
  change ((j ≫ q).left.isoOpensRange.inv ≫ j.left) ≫ q.left =
    (j ≫ q).left.opensRange.ι
  simpa only [Category.assoc, Over.comp_left] using
    Scheme.Hom.isoOpensRange_inv_comp (j ≫ q).left

/-- Every point of the cell maps into the entire open image on underlying points. -/
theorem range_subset_image (p : RingPoint k X k) :
    Set.range (p ≫ (j ≫ q)).left ⊆ (j ≫ q).left.opensRange := by
  rintro _ ⟨x, rfl⟩
  change (j ≫ q).left (p.left x) ∈ Set.range (j ≫ q).left
  exact ⟨p.left x, rfl⟩

/-- Every rational point coming from this cell has an algebraic section nearby. -/
theorem exists_localSection (p : RingPoint k X k) :
    ∃ (V : Q.left.Opens) (s : openOver k Q V ⟶ G.X),
      Set.range (p ≫ (j ≫ q)).left ⊆ V ∧ s ≫ q = openOverι k Q V :=
  ⟨(j ≫ q).left.opensRange, sectionOverImage j q, range_subset_image j q p,
    sectionOverImage_comp j q⟩

end SectionOverImage

end Langlands.GroupScheme.QuotientCell
