import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Mathlib.Algebra.DualNumber

/-!
# Separation of rational points and tangent vectors by global sections

For a scheme `X` with a morphism `p : X ⟶ Spec K` to the spectrum of a field and a line
bundle `L` on `X`, the global sections of `L` separate rational points and rational
tangent vectors when they have no rational base point, distinguish distinct rational
points, and detect every nonzero `K[ε]`-valued tangent vector at a rational point by a
section vanishing at that point. Vanishing along a morphism means that the pulled-back
section is zero. These are the conditions of the very-ampleness criterion that Milne
quotes from Hartshorne, formulated through `K`-points and `K[ε]`-points of `X`.
-/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A rational point is a section of the structure morphism to the spectrum of `K`. -/
def IsRationalPoint (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) : Prop :=
  x ≫ p = 𝟙 _

/-- A global section of a line bundle vanishes along a morphism when its pullback is zero. -/
def VanishesAlong (L : LineBundle X) {Y : Scheme.{u}} (f : Y ⟶ X)
    (s : Langlands.SchemeModule.GlobalSections L.obj) : Prop :=
  Langlands.SchemeModule.pullbackSection f L.obj s = 0

variable (K) in
/-- The structure morphism `Spec K[ε] ⟶ Spec K` of the dual numbers. -/
def dualNumberProjection :
    Spec (CommRingCat.of (DualNumber K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))

variable (K) in
/-- The closed point `Spec K ⟶ Spec K[ε]`, the spectrum of the augmentation `ε ↦ 0`. -/
def dualNumberAugmentation :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (DualNumber K)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)

/-- A rational tangent vector at `x` is a `K[ε]`-point of `X` over `K` restricting to `x`. -/
def IsTangentVectorAt (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X) : Prop :=
  t ≫ p = dualNumberProjection K ∧ dualNumberAugmentation K ≫ t = x

/-- A nonzero rational tangent vector at `x` is one different from the constant
`K[ε]`-point `dualNumberProjection K ≫ x`. -/
def IsNonzeroTangentVectorAt (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X) : Prop :=
  IsTangentVectorAt p x t ∧ t ≠ dualNumberProjection K ≫ x

/-- The complete linear system of global sections of `L` has no rational base point,
separates rational points, and separates nonzero rational tangent vectors. -/
def SeparatesPointsAndTangents (p : X ⟶ Spec (CommRingCat.of K)) (L : LineBundle X) :
    Prop :=
  (∀ x : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x →
      ∃ s : Langlands.SchemeModule.GlobalSections L.obj, ¬ VanishesAlong L x s) ∧
    (∀ x y : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x → IsRationalPoint p y →
      x ≠ y →
        ∃ s : Langlands.SchemeModule.GlobalSections L.obj,
          VanishesAlong L x s ∧ ¬ VanishesAlong L y s) ∧
    (∀ x : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x →
      ∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ X, IsNonzeroTangentVectorAt p x t →
        ∃ s : Langlands.SchemeModule.GlobalSections L.obj,
          VanishesAlong L x s ∧ ¬ VanishesAlong L t s)

/-- The closed point of `Spec K[ε]` is a section of its structure morphism. -/
theorem dualNumberAugmentation_comp_dualNumberProjection :
    dualNumberAugmentation K ≫ dualNumberProjection K = 𝟙 _ := by
  rw [dualNumberAugmentation, dualNumberProjection, ← Spec.map_comp, ← Spec.map_id]
  rfl

/-- The base of a rational tangent vector is a rational point. -/
theorem IsTangentVectorAt.isRationalPoint {p : X ⟶ Spec (CommRingCat.of K)}
    {x : Spec (CommRingCat.of K) ⟶ X} {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X}
    (ht : IsTangentVectorAt p x t) : IsRationalPoint p x := by
  rw [IsRationalPoint, ← ht.2, Category.assoc, ht.1,
    dualNumberAugmentation_comp_dualNumberProjection]

/-- The constant `K[ε]`-point at a rational point is a tangent vector there. -/
theorem isTangentVectorAt_dualNumberProjection_comp {p : X ⟶ Spec (CommRingCat.of K)}
    {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x) :
    IsTangentVectorAt p x (dualNumberProjection K ≫ x) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hx, Category.comp_id]
  · rw [← Category.assoc, dualNumberAugmentation_comp_dualNumberProjection, Category.id_comp]

end Langlands.AlgebraicGeometry.Picard
