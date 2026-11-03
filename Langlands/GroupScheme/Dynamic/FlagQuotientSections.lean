import Langlands.GroupScheme.Dynamic.FlagQuotientStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs

/-! # Transport of algebraic sections of actual flag-quotient maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable (k : Type u) [Field k]

/-- Left translation by an actual rational group point, as a relative-scheme isomorphism. -/
def rationalLeftTranslation (G : GroupScheme (Spec (CommRingCat.of k)))
    (a : RationalPoint k G.X) : G.X ≅ G.X where
  hom := (toUnit G.X ≫ a) * 𝟙 G.X
  inv := (toUnit G.X ≫ a⁻¹) * 𝟙 G.X
  hom_inv_id := by
    simp only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    rw [← mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, one_mul]
  inv_hom_id := by
    simp only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    rw [← mul_assoc, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, one_mul]

@[simp] theorem comp_rationalLeftTranslation
    (G : GroupScheme (Spec (CommRingCat.of k))) (a : RationalPoint k G.X)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) :
    g ≫ (rationalLeftTranslation k G a).hom = (toUnit T ≫ a) * g := by
  simp [rationalLeftTranslation, MonObj.comp_mul]

variable {X Q : Over (Spec (CommRingCat.of k))}

/-- Transport a section using a compatible source map and a quotient automorphism. -/
def translatedFlagSection (f : X ⟶ X) (e : Q ≅ Q) (U : Q.left.Opens)
    (s : openOver k Q U ⟶ X) :
    openOver k Q (e.inv.left ⁻¹ᵁ U) ⟶ X :=
  restrictedOver k e.inv U ≫ s ≫ f

/-- The transported map is a section on the inverse image of the original open. -/
theorem translatedFlagSection_comp (π : X ⟶ Q) (f : X ⟶ X) (e : Q ≅ Q)
    (he : f ≫ π = π ≫ e.hom) (U : Q.left.Opens)
    (s : openOver k Q U ⟶ X) (hs : s ≫ π = openOverι k Q U) :
    translatedFlagSection k f e U s ≫ π = openOverι k Q (e.inv.left ⁻¹ᵁ U) := by
  calc
    _ = restrictedOver k e.inv U ≫ s ≫ (f ≫ π) := by
      simp [translatedFlagSection]
    _ = (restrictedOver k e.inv U ≫ (s ≫ π)) ≫ e.hom := by
      rw [he]
      simp only [Category.assoc]
    _ = (restrictedOver k e.inv U ≫ openOverι k Q U) ≫ e.hom := by rw [hs]
    _ = (openOverι k Q (e.inv.left ⁻¹ᵁ U) ≫ e.inv) ≫ e.hom := by
      rw [restrictedOver_fac]
    _ = _ := by simp

/-- Translating a point contained in the original open gives a point in the new open. -/
theorem range_subset_translatedOpen (e : Q ≅ Q) (p q : RingPoint k Q k)
    (hpq : q ≫ e.hom = p) (U : Q.left.Opens) (hq : Set.range q.left ⊆ U) :
    Set.range p.left ⊆ e.inv.left ⁻¹ᵁ U := by
  dsimp only [RingPoint] at p q
  have he : p ≫ e.inv = q := by
    calc
      p ≫ e.inv = (q ≫ e.hom) ≫ e.inv :=
        congrArg (fun r : ringTest k k ⟶ Q => r ≫ e.inv) hpq.symm
      _ = q ≫ (e.hom ≫ e.inv) := Category.assoc _ _ _
      _ = q := by rw [e.hom_inv_id, Category.comp_id]
  rintro _ ⟨x, rfl⟩
  change e.inv.left (p.left x) ∈ U
  have hx := congrArg (fun r : ringTest k k ⟶ Q => r.left x) he
  change e.inv.left (p.left x) = q.left x at hx
  rw [hx]
  exact hq ⟨x, rfl⟩

/-- A section near one rational point propagates under compatible source maps
and quotient automorphisms that act transitively on rational points. -/
theorem localSections_of_transitive_lifts (π : X ⟶ Q) (q : RingPoint k Q k)
    (U : Q.left.Opens) (s : openOver k Q U ⟶ X)
    (hq : Set.range q.left ⊆ U) (hs : s ≫ π = openOverι k Q U)
    (htrans : ∀ p : RingPoint k Q k, ∃ (f : X ⟶ X) (e : Q ≅ Q),
      f ≫ π = π ≫ e.hom ∧ q ≫ e.hom = p) :
    ∀ p : RingPoint k Q k,
      ∃ (V : Q.left.Opens) (t : openOver k Q V ⟶ X),
        Set.range p.left ⊆ V ∧ t ≫ π = openOverι k Q V := by
  intro p
  obtain ⟨f, e, he, hp⟩ := htrans p
  exact ⟨e.inv.left ⁻¹ᵁ U, translatedFlagSection k f e U s,
    range_subset_translatedOpen k e p q hp U hq,
    translatedFlagSection_comp k π f e he U s hs⟩

end Langlands.GroupScheme.Dynamic
