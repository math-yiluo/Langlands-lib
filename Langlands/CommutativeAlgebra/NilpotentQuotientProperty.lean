import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Extending a morphism property from square-zero to nilpotent quotients -/

universe u

open CategoryTheory

namespace Langlands.CommutativeAlgebra

/-- A multiplicative property of ring maps that respects isomorphisms holds
for nilpotent quotient maps if it holds for square-zero quotient maps. -/
theorem nilpotentQuotient_of_squareZero
    (P : MorphismProperty CommRingCat.{u})
    [P.IsMultiplicative] [P.RespectsIso]
    (hP : ∀ (A : Type u) [CommRing A] (I : Ideal A), I ^ 2 = ⊥ →
      P (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : IsNilpotent I) :
    P (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  apply Ideal.IsNilpotent.induction_on I hI
    (P := fun {A} [_] I => P (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  · exact hP
  · intro B _ I J hIJ h₁ h₂
    let e := DoubleQuot.quotQuotEquivQuotOfLE hIJ
    have he : IsIso (CommRingCat.ofHom e.toRingHom) :=
      e.toCommRingCatIso.isIso_hom
    have hcomp :
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))) ≫
          CommRingCat.ofHom e.toRingHom =
        CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      ext x
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hIJ
    rw [← hcomp]
    exact P.comp_mem _ _ h₁ (P.comp_mem _ _ h₂ (P.of_isIso _))

end Langlands.CommutativeAlgebra
