import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pullback squares for the fibre frame lifting assembly

Two base changes `X₁ ×_S T ⟶ X ×_S T` of a morphism `X₁ ⟶ X` over `S` form a pullback square
over `X₁ ⟶ X`, and the point `Spec κ(s) ⟶ S` factors through the spectrum of the sections of an
affine open neighbourhood of `s`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

/-- If `P₁` and `P` are base changes of `X₁ ⟶ S` and `X ⟶ S` along the same `T ⟶ S`, and
`i : X₁ ⟶ X` is a morphism over `S`, then a morphism `P₁ ⟶ P` over `i` and over `T` makes a
pullback square with `i`. -/
theorem isPullback_of_over {C : Type*} [Category* C] {P₁ P X₁ X T S : C} {a : P₁ ⟶ X₁}
    {b : P₁ ⟶ T} {c : P ⟶ X} {d : P ⟶ T} {h₁ : X₁ ⟶ S} {h : X ⟶ S} {t : T ⟶ S}
    {i : X₁ ⟶ X} {m : P₁ ⟶ P} (H₁ : IsPullback a b h₁ t) (H : IsPullback c d h t)
    (hi : i ≫ h = h₁) (hm₁ : m ≫ c = a ≫ i) (hm₂ : m ≫ d = b) : IsPullback a m i c :=
  IsPullback.of_bot (by rw [hm₂, hi]; exact H₁) hm₁.symm H

/-- The point `Spec κ(s) ⟶ S` factors through the spectrum of the sections over an affine open
neighbourhood `V` of `s`, via the germ followed by the residue map. -/
theorem fromSpecResidueField_eq_comp_fromSpec {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) {s : S} (hs : s ∈ V) :
    S.fromSpecResidueField s =
      Spec.map (S.presheaf.germ V s hs ≫ S.residue s) ≫ hV.fromSpec := by
  rw [Scheme.fromSpecResidueField, ← hV.fromSpecStalk_eq_fromSpecStalk hs,
    IsAffineOpen.fromSpecStalk, Spec.map_comp, Category.assoc]

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
