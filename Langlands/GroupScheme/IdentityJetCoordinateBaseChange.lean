import Langlands.GroupScheme.IdentityJetBaseChange
import Langlands.GroupScheme.IdentityJetCoordinates

/-! # Actual ambient jet coordinate sections under change of base -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

private theorem pullback_function_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(Z, ⊤)) :
    f.appLE U V hVU (g.appLE ⊤ U (by simp) a) =
      h.appLE ⊤ V (by simp) a := by
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE f g ⊤ U V (by simp) hVU) a
  have he := congrArg
    (fun (k : X ⟶ Z) => k.appLE ⊤ V (by simp)) hfg
  simp only [CommRingCat.comp_apply] at hh
  exact hh.trans (ConcreteCategory.congr_hom he a)

variable {S T : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]
  (b : T ⟶ S)

private theorem baseChanged_affine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChanged_affine

/-- The open condition for actual function pullback above a base-change square. -/
theorem baseChangeMap_preimage (n : ℕ) {U : S.Opens} {V : T.Opens}
    (hVU : V ≤ b ⁻¹ᵁ U) :
    projection ((GroupScheme.baseChange b).obj G) n ⁻¹ᵁ V ≤
      baseChangeMap G b n ⁻¹ᵁ (projection G n ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, (baseChange_isPullback G b n).w,
    Scheme.Hom.comp_preimage]
  exact (projection ((GroupScheme.baseChange b).obj G) n).preimage_mono hVU

/-- Pullback of actual jet functions above compatible opens of the two bases. -/
def baseChangeSectionsRingMap (n : ℕ) (U : S.Opens) (V : T.Opens)
    (hVU : V ≤ b ⁻¹ᵁ U) :
    Γ(scheme G n, projection G n ⁻¹ᵁ U) →+*
      Γ(scheme ((GroupScheme.baseChange b).obj G) n,
        projection ((GroupScheme.baseChange b).obj G) n ⁻¹ᵁ V) :=
  (baseChangeMap G b n).appLE _ _ (baseChangeMap_preimage G b n hVU) |>.hom

variable {B : CommRingCat.{u}} (j : G.X.left ⟶ Spec B)

/-- Actual ambient coordinate functions are preserved by actual jet base change. -/
theorem jetCoordinateMap_baseChange (n : ℕ) (U : S.Opens) (V : T.Opens)
    (hVU : V ≤ b ⁻¹ᵁ U) (a : B) :
    baseChangeSectionsRingMap G b n U V hVU (jetCoordinateMap G j n U a) =
      jetCoordinateMap ((GroupScheme.baseChange b).obj G)
        (pullback.fst G.X.hom b ≫ j) n V a := by
  have he : baseChangeMap G b n ≫ (inclusion G n ≫ j) =
      inclusion ((GroupScheme.baseChange b).obj G) n ≫ (pullback.fst G.X.hom b ≫ j) := by
    rw [← Category.assoc, baseChangeMap_inclusion, Category.assoc]
  exact pullback_function_comp (baseChangeMap G b n) (inclusion G n ≫ j) _
    he _ _ (baseChangeMap_preimage G b n hVU) ((Scheme.ΓSpecIso B).inv a)

omit [IsAffineHom G.X.hom] in
/-- Ambient identity vanishing is preserved by an arbitrary change of base. -/
theorem vanishesAtIdentity_baseChange (I : Ideal B) (hI : VanishesAtIdentity G j I) :
    VanishesAtIdentity ((GroupScheme.baseChange b).obj G)
      (pullback.fst G.X.hom b ≫ j) I := by
  intro a ha
  rw [← Category.assoc, identitySection_baseChange_fst, Category.assoc,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hI a ha, map_zero]

/-- Actual global quotient-coordinate sections commute with pullback on all opens. -/
theorem quotientCoordinates_baseChange (I : Ideal B) (hI : VanishesAtIdentity G j I)
    (n : ℕ) (U : S.Opens) (V : T.Opens) (hVU : V ≤ b ⁻¹ᵁ U)
    (z : B ⧸ I ^ (n + 1)) :
    baseChangeSectionsRingMap G b n U V hVU
      ((module G n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (quotientCoordinates G j I hI n z)) =
      (module ((GroupScheme.baseChange b).obj G) n).presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op
          (quotientCoordinates ((GroupScheme.baseChange b).obj G)
            (pullback.fst G.X.hom b ≫ j) I
            (vanishesAtIdentity_baseChange G b j I hI) n z) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [quotientCoordinates_mk, quotientCoordinates_mk,
    jetCoordinateMap_restrict, jetCoordinateMap_restrict]
  exact jetCoordinateMap_baseChange G b j n U V hVU a

end Langlands.GroupScheme.IdentityJet
