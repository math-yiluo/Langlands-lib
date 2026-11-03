import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.Rational.Characters
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual integral group models and their generic points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BasePoints

variable {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)

/-- Restrict a section to `T`, then use the actual pullback point correspondence. -/
def baseChangeSectionHom :
    (Over.mk (𝟙 S) ⟶ G.X) →*
      (Over.mk (𝟙 T) ⟶ ((baseChange b).obj G).X) :=
  (baseChangeBasePointsEquiv b G).symm.toMonoidHom.comp
    (G.points.map (Over.homMk b (by simp) :
      Over.mk b ⟶ Over.mk (𝟙 S)).op).hom

/-- Projection of the changed section to the original group scheme. -/
theorem baseChangeSectionHom_fst (x : Over.mk (𝟙 S) ⟶ G.X) :
    (baseChangeSectionHom b G x).left ≫ pullback.fst G.X.hom b = b ≫ x.left := by
  have h := congrArg (fun y : Over.mk b ⟶ G.X => y.left)
    ((baseChangeBasePointsEquiv b G).apply_symm_apply
      ((G.points.map (Over.homMk b (by simp) :
        Over.mk b ⟶ Over.mk (𝟙 S)).op).hom x))
  exact (baseChangeBasePointsEquiv_left b G _).symm.trans h

/-- The underlying morphism is the unique lift of the restricted section and the identity. -/
theorem baseChangeSectionHom_left (x : Over.mk (𝟙 S) ⟶ G.X) :
    (baseChangeSectionHom b G x).left =
      pullback.lift (b ≫ x.left) (𝟙 T) (by simp [Category.assoc, x.w]) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact baseChangeSectionHom_fst b G x
  · rw [pullback.lift_snd]
    exact (baseChangeSectionHom b G x).w

/-- The base-point correspondence commutes with a group-scheme homomorphism. -/
theorem baseChangeBasePointsEquiv_comp {G H : GroupScheme S} (f : G ⟶ H)
    (x : Over.mk (𝟙 T) ⟶ ((baseChange b).obj G).X) :
    baseChangeBasePointsEquiv b H (x ≫ ((baseChange b).map f).hom.hom) =
      baseChangeBasePointsEquiv b G x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  simp only [baseChangeBasePointsEquiv_left, Over.comp_left]
  change (x.left ≫ ((Over.pullback b).map f.hom.hom).left) ≫
      pullback.fst H.X.hom b =
    (x.left ≫ pullback.fst G.X.hom b) ≫ f.hom.hom.left
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]

/-- Naturality of changing a section's base. -/
theorem baseChangeSectionHom_naturality {G H : GroupScheme S} (f : G ⟶ H)
    (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom b H (x ≫ f.hom.hom) =
      baseChangeSectionHom b G x ≫ ((baseChange b).map f).hom.hom := by
  apply (baseChangeBasePointsEquiv b H).injective
  rw [baseChangeBasePointsEquiv_comp]
  change (baseChangeBasePointsEquiv b H)
      ((baseChangeBasePointsEquiv b H).symm (_ ≫ (x ≫ f.hom.hom))) =
    (baseChangeBasePointsEquiv b G)
      ((baseChangeBasePointsEquiv b G).symm (_ ≫ x)) ≫ f.hom.hom
  simp only [MulEquiv.apply_symm_apply, Category.assoc]

end BasePoints

/-- An affine flat finite-type group model with its supplied generic-fibre identification. -/
structure IntegralModel (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) where
  group : GroupScheme (Spec (CommRingCat.of R))
  [affine : IsAffineHom group.X.hom]
  [flat : Flat group.X.hom]
  [finiteType : LocallyOfFiniteType group.X.hom]
  genericIso : (baseChange (Spec.algebraMap R K)).obj group ≅ G

attribute [instance] IntegralModel.affine IntegralModel.flat IntegralModel.finiteType

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

variable {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- Smoothness is an additional property of the actual structural morphism. -/
def IsSmooth : Prop := Smooth M.group.X.hom

/-- The actual generic fibre, before using its chosen identification with `G`. -/
abbrev genericFibre : GroupScheme (Spec (CommRingCat.of K)) :=
  (baseChange (Spec.algebraMap R K)).obj M.group

/-- Sections over the actual integral base, with their pointwise group law. -/
abbrev integralSections : Type u := rationalPoints M.group

/-- The integral-point homomorphism into the given generic group. -/
def integralPointMap : M.integralSections →* rationalPoints G :=
  (rationalPoints.map M.genericIso.hom).comp
    (baseChangeSectionHom (Spec.algebraMap R K) M.group)

/-- Evaluation uses the actual inclusion, the pullback lift and the specified isomorphism. -/
theorem integralPointMap_left (x : M.integralSections) :
    (M.integralPointMap x).left =
      pullback.lift ((Spec.algebraMap R K) ≫ x.left) (𝟙 _)
        (by simp [Category.assoc, x.w]) ≫ M.genericIso.hom.hom.hom.left := by
  change (baseChangeSectionHom (Spec.algebraMap R K) M.group x).left ≫ _ = _
  rw [baseChangeSectionHom_left]

/-- The integral points inside the existing group of generic rational points. -/
def integralPoints : Subgroup (rationalPoints G) := M.integralPointMap.range

theorem mem_integralPoints (g : rationalPoints G) :
    g ∈ M.integralPoints ↔ ∃ x : M.integralSections, M.integralPointMap x = g :=
  Iff.rfl

/-- A model morphism extending the specified generic-group morphism `f`. -/
structure Hom (N : IntegralModel R K H) (f : G ⟶ H) where
  hom : M.group ⟶ N.group
  generic_comm :
    (baseChange (Spec.algebraMap R K)).map hom ≫ N.genericIso.hom =
      M.genericIso.hom ≫ f

variable {M} {N : IntegralModel R K H} {f : G ⟶ H}

/-- The specified compatibility square gives naturality of integral-point maps. -/
theorem Hom.integralPointMap_naturality (φ : M.Hom N f) (x : M.integralSections) :
    N.integralPointMap (rationalPoints.map φ.hom x) =
      rationalPoints.map f (M.integralPointMap x) := by
  change baseChangeSectionHom (Spec.algebraMap R K) N.group (x ≫ φ.hom.hom.hom) ≫
      N.genericIso.hom.hom.hom =
    (baseChangeSectionHom (Spec.algebraMap R K) M.group x ≫
      M.genericIso.hom.hom.hom) ≫ f.hom.hom
  rw [baseChangeSectionHom_naturality, Category.assoc]
  change _ ≫
      ((baseChange (Spec.algebraMap R K)).map φ.hom ≫ N.genericIso.hom).hom.hom =
    _
  rw [φ.generic_comm]
  rfl

/-- Generic morphisms with compatible models carry integral points to integral points. -/
theorem Hom.map_mem_integralPoints (φ : M.Hom N f) {g : rationalPoints G}
    (hg : g ∈ M.integralPoints) : rationalPoints.map f g ∈ N.integralPoints := by
  obtain ⟨x, rfl⟩ := hg
  exact ⟨rationalPoints.map φ.hom x, φ.integralPointMap_naturality x⟩

end IntegralModel
end Langlands.GroupScheme
