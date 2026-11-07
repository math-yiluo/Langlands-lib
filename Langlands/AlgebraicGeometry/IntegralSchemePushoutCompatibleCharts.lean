import Langlands.AlgebraicGeometry.IntegralSchemePushoutLocallyRinged
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Compatible open charts in locally ringed pushouts -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LocallyRingedPushout

variable {Z₀ X₀ Y₀ P₀ Z X Y P : LocallyRingedSpace.{u}}
variable {i₀ : Z₀ ⟶ X₀} {j₀ : Z₀ ⟶ Y₀} {a₀ : X₀ ⟶ P₀} {b₀ : Y₀ ⟶ P₀}
variable {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P}

/-- A cartesian open map of two pushout spans induces an open chart with exact ranges. -/
lemma isOpenImmersion_and_range
    (h₀ : IsPushout i₀ j₀ a₀ b₀) (h : IsPushout i j a b)
    (z : Z₀ ⟶ Z) (l : X₀ ⟶ X) (r : Y₀ ⟶ Y)
    (hl : i₀ ≫ l = z ≫ i) (hr : j₀ ≫ r = z ≫ j)
    [LocallyRingedSpace.IsOpenImmersion z]
    [LocallyRingedSpace.IsOpenImmersion l]
    [LocallyRingedSpace.IsOpenImmersion r]
    (hcl : i.base ⁻¹' Set.range l.base = Set.range z.base)
    (hcr : j.base ⁻¹' Set.range r.base = Set.range z.base)
    (q : P₀ ⟶ P) (hql : a₀ ≫ q = l ≫ a) (hqr : b₀ ≫ q = r ≫ b) :
    LocallyRingedSpace.IsOpenImmersion q ∧
      Set.range l.base = a.base ⁻¹' Set.range q.base ∧
      Set.range r.base = b.base ⁻¹' Set.range q.base := by
  let τ : span i₀ j₀ ⟶ span i j := spanHomMk z l r hl hr
  have hτ : ∀ t, LocallyRingedSpace.IsOpenImmersion (τ.app t) := by
    rintro (_ | _ | _) <;> dsimp [τ] <;> infer_instance
  let := hτ
  have hcart : ∀ {s t} (f : s ⟶ t),
      ((span i j).map f).base ⁻¹' Set.range (τ.app t).base =
        Set.range (τ.app s).base := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _)
    all_goals first | exact hcl | exact hcr | rfl
  have hq : ∀ t, h₀.cocone.ι.app t ≫ q = τ.app t ≫ h.cocone.ι.app t := by
    rintro (_ | _ | _)
    · change (i₀ ≫ a₀) ≫ q = z ≫ (i ≫ a)
      rw [Category.assoc, hql, ← Category.assoc, hl, Category.assoc]
    · exact hql
    · exact hqr
  refine ⟨LocallyRingedColimit.isOpenImmersion_of_cartesian τ
    h₀.isColimit h.isColimit q hq hcart, ?_, ?_⟩
  · exact LocallyRingedColimit.range_of_cartesian τ
      h₀.isColimit h.isColimit q hq hcart WalkingSpan.left
  · exact LocallyRingedColimit.range_of_cartesian τ
      h₀.isColimit h.isColimit q hq hcart WalkingSpan.right

end LocallyRingedPushout

namespace CompatibleOpen

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : i ⁻¹ᵁ U = j ⁻¹ᵁ V)

/-- The map from the common inverse image to the first open. -/
abbrev leftMap : (i ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  i.resLE U (i ⁻¹ᵁ U) le_rfl

/-- The map from the common inverse image to the second open. -/
abbrev rightMap : (i ⁻¹ᵁ U).toScheme ⟶ V.toScheme :=
  j.resLE V (i ⁻¹ᵁ U) hUV.le

variable {P₀ P : LocallyRingedSpace.{u}}
    {a₀ : U.toScheme.toLocallyRingedSpace ⟶ P₀}
    {b₀ : V.toScheme.toLocallyRingedSpace ⟶ P₀}
    {a : X.toLocallyRingedSpace ⟶ P} {b : Y.toLocallyRingedSpace ⟶ P}

/-- The map from the pushout of a compatible open pair into the large pushout. -/
def comparison
    (h₀ : IsPushout (leftMap i U).toLRSHom (rightMap i j U V hUV).toLRSHom a₀ b₀)
    (h : IsPushout i.toLRSHom j.toLRSHom a b) : P₀ ⟶ P :=
  h₀.desc (U.ι.toLRSHom ≫ a) (V.ι.toLRSHom ≫ b) (by
    have hl := Scheme.forgetToLocallyRingedSpace.congr_map
      (Scheme.Hom.resLE_comp_ι i (U := U) (V := i ⁻¹ᵁ U) le_rfl)
    have hr := Scheme.forgetToLocallyRingedSpace.congr_map
      (Scheme.Hom.resLE_comp_ι j (U := V) (V := i ⁻¹ᵁ U) hUV.le)
    dsimp only [Functor.map_comp, Scheme.forgetToLocallyRingedSpace_map] at hl hr
    change (leftMap i U).toLRSHom ≫ U.ι.toLRSHom =
      (i ⁻¹ᵁ U).ι.toLRSHom ≫ i.toLRSHom at hl
    change (rightMap i j U V hUV).toLRSHom ≫ V.ι.toLRSHom =
      (i ⁻¹ᵁ U).ι.toLRSHom ≫ j.toLRSHom at hr
    rw [← Category.assoc, hl, Category.assoc, h.w,
      ← Category.assoc, ← hr, Category.assoc])

/-- A pushout on compatible opens embeds openly, with precisely those inverse images. -/
lemma comparison_isOpenImmersion_and_range
    (h₀ : IsPushout (leftMap i U).toLRSHom (rightMap i j U V hUV).toLRSHom a₀ b₀)
    (h : IsPushout i.toLRSHom j.toLRSHom a b) :
    LocallyRingedSpace.IsOpenImmersion (comparison i j U V hUV h₀ h) ∧
      (U : Set X) = a.base ⁻¹' Set.range (comparison i j U V hUV h₀ h).base ∧
      (V : Set Y) = b.base ⁻¹' Set.range (comparison i j U V hUV h₀ h).base := by
  have hl := Scheme.forgetToLocallyRingedSpace.congr_map
    (Scheme.Hom.resLE_comp_ι i (U := U) (V := i ⁻¹ᵁ U) le_rfl)
  have hr := Scheme.forgetToLocallyRingedSpace.congr_map
    (Scheme.Hom.resLE_comp_ι j (U := V) (V := i ⁻¹ᵁ U) hUV.le)
  have hcl : i.toLRSHom.base ⁻¹' Set.range U.ι.toLRSHom.base =
      Set.range (i ⁻¹ᵁ U).ι.toLRSHom.base := by
    change i ⁻¹' Set.range U.ι = Set.range (i ⁻¹ᵁ U).ι
    simp only [Scheme.Opens.range_ι]
    rfl
  have hcr : j.toLRSHom.base ⁻¹' Set.range V.ι.toLRSHom.base =
      Set.range (i ⁻¹ᵁ U).ι.toLRSHom.base := by
    change j ⁻¹' Set.range V.ι = Set.range (i ⁻¹ᵁ U).ι
    simp only [Scheme.Opens.range_ι]
    exact congrArg SetLike.coe hUV.symm
  obtain ⟨ho, hU, hV⟩ := LocallyRingedPushout.isOpenImmersion_and_range h₀ h
    (i ⁻¹ᵁ U).ι.toLRSHom U.ι.toLRSHom V.ι.toLRSHom hl hr hcl hcr
    (comparison i j U V hUV h₀ h)
    (h₀.inl_desc _ _ _) (h₀.inr_desc _ _ _)
  refine ⟨ho, ?_, ?_⟩
  · simpa only [← Scheme.Hom.comp_toLRSHom, Scheme.Opens.range_ι] using hU
  · simpa only [← Scheme.Hom.comp_toLRSHom, Scheme.Opens.range_ι] using hV

end CompatibleOpen

end Langlands.AlgebraicGeometry.IntegralSchemePushout
