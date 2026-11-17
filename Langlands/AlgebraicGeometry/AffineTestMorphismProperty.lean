import Langlands.CommutativeAlgebra.NilpotentQuotientProperty
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Morphism properties on affine tests -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A property of maps of schemes over `S`, tested on the opposite of a ring map
with every compatible choice of structure maps to `S`. -/
def affineTestMorphismProperty (P : MorphismProperty (Over S)) :
    MorphismProperty CommRingCat.{u} :=
  fun A B f => ∀ (a : Spec A ⟶ S) (b : Spec B ⟶ S)
    (h : Spec.map f ≫ a = b),
    P (Over.homMk (Spec.map f) h : Over.mk b ⟶ Over.mk a)

variable (P : MorphismProperty (Over S)) [P.IsMultiplicative] [P.RespectsIso]

theorem affineTestMorphismProperty_of_isIso {A B : CommRingCat.{u}}
    (f : A ⟶ B) [IsIso f] :
    affineTestMorphismProperty P f := by
  intro a b h
  change P (Over.isoMk (f := Over.mk b) (g := Over.mk a)
    (asIso (Spec.map f)) h).hom
  exact P.of_isIso _

instance affineTestMorphismProperty_isMultiplicative :
    (affineTestMorphismProperty P).IsMultiplicative where
  id_mem _ := affineTestMorphismProperty_of_isIso P _
  comp_mem f g hf hg := by
    intro a c h
    let b := Spec.map f ≫ a
    have hgb : Spec.map g ≫ b = c := by
      dsimp [b]
      rw [← Category.assoc, ← Spec.map_comp]
      exact h
    have hh := P.comp_mem
      (Over.homMk (Spec.map g) hgb : Over.mk c ⟶ Over.mk b)
      (Over.homMk (Spec.map f) rfl : Over.mk b ⟶ Over.mk a)
      (hg b c hgb) (hf a b rfl)
    convert hh using 1
    congr 1
    exact Spec.map_comp f g

instance affineTestMorphismProperty_respectsIso :
    (affineTestMorphismProperty P).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f _ => affineTestMorphismProperty_of_isIso P f)

/-- A multiplicative property of test-scheme maps over `S` extends from all
square-zero affine thickenings to all nilpotent affine thickenings. -/
theorem affineTestMorphismProperty_nilpotent
    (hP : ∀ (A : Type u) [CommRing A] (I : Ideal A), I ^ 2 = ⊥ →
      affineTestMorphismProperty P (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : IsNilpotent I) :
    affineTestMorphismProperty P (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  CommutativeAlgebra.nilpotentQuotient_of_squareZero
    (affineTestMorphismProperty P) hP A I hI

end Langlands.AlgebraicGeometry
