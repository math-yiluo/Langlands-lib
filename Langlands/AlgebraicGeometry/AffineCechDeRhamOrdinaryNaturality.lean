import Langlands.AlgebraicGeometry.AffineCechDeRhamCoverPullback
import Langlands.AlgebraicGeometry.AffineCechDeRhamSchemePullback
import Langlands.AlgebraicGeometry.AffineCechDeRhamStructureH1

/-! # Ordinary morphisms on the degree-one Hodge sequence -/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  (a : X ⟶ Y) (ha : a ≫ g = f) (α : U.I₀ → V.I₀)
  (hα : ∀ i, coverOpens U i ≤ a ⁻¹ᵁ coverOpens V (α i))

/-- Pull back a closed form along the given morphism on compatible covers. -/
def closedFormsPullback : closedForms g V →ₗ[R] closedForms f U :=
  ((pullOneForms a ha α hα 0).comp (closedForms g V).subtype).codRestrict _ (fun b => by
    change cechD U (oneForms f) 0 (pullOneForms a ha α hα 0 b.val) = 0 ∧
      cochainMap U (exteriorD1 f) 0 (pullOneForms a ha α hα 0 b.val) = 0
    rw [cechD_pullOneForms, ← pullTwoForms_exteriorD1, b.property.1, b.property.2,
      map_zero, map_zero]
    exact ⟨rfl, rfl⟩)

variable [Smooth f] [IsSeparated f] [Finite U.I₀] [Smooth g] [IsSeparated g] [Finite V.I₀]

private abbrev localMaps := LocalPullbacks.ofMorphism (⊥ : Ideal R) a ha α hα
private lemma bot_sq : (⊥ : Ideal R) * ⊥ = ⊥ := Ideal.bot_mul _

omit [Smooth f] [Smooth g] [IsSeparated f] [IsSeparated g] [Finite U.I₀] [Finite V.I₀] in
private lemma ordinary_cochainOne_fst (b : C1 g V) :
    ((localMaps a ha α hα).cochainOne bot_sq b).1 = pullFunctions a ha α hα 1 b.1 := by
  funext τ
  rw [LocalPullbacks.cochainOne_fst, pullFunctions_apply]
  let r := (localMaps a ha α hα).sections τ 0
  change r (b.1 (α ∘ τ)) + RelativeForms.contractDifferenceOne r r bot_sq
    ((localMaps a ha α hα).congruent τ 1 0) _ = r (b.1 (α ∘ τ))
  rw [RelativeForms.contractDifferenceOne_self, add_zero]

/-- The projection to function classes computes the ordinary pullback on the
function component of any cocycle. -/
lemma schemePullbackH1_toStructureH1_class (b : cocycles g V) :
    toStructureH1 f U (schemePullbackH1 a ha α hα ((boundaries g V).mkQ b)) =
      (structureBoundaries f U).mkQ ⟨pullFunctions a ha α hα 1 b.val.1, by
        change cechD U (functions f) 1 (pullFunctions a ha α hα 1 b.val.1) = 0
        rw [cechD_pullFunctions, show cechD V (functions g) 1 b.val.1 = 0 from
          (forgetFormsCocycle g V b).property, map_zero]⟩ := by
  change toStructureH1 f U
    ((localMaps a ha α hα).pullbackH1 bot_sq ((boundaries g V).mkQ b)) = _
  rw [LocalPullbacks.pullbackH1_mk, toStructureH1_class]
  apply congrArg ((structureBoundaries f U).mkQ)
  apply Subtype.ext
  exact ordinary_cochainOne_fst a ha α hα b.val

/-- The class of a closed form pulls back to the class of its pulled-back form. -/
lemma schemePullbackH1_closedFormClass (b : closedForms g V) :
    schemePullbackH1 a ha α hα (closedFormClass g V b) =
      closedFormClass f U (closedFormsPullback a ha α hα b) := by
  change (localMaps a ha α hα).pullbackH1 bot_sq ((boundaries g V).mkQ _) =
    (boundaries f U).mkQ _
  rw [LocalPullbacks.pullbackH1_mk]
  apply congrArg ((boundaries f U).mkQ)
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  change ((localMaps a ha α hα).cochainOne bot_sq (0, b.val)).1 = 0
  rw [ordinary_cochainOne_fst, map_zero]

end Langlands.AlgebraicGeometry.AffineCechDeRham
