import Langlands.GroupScheme.IdentityJetAmbientCoordinates
import Langlands.AlgebraicGeometry.Picard.LineHom.SectionsTensor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine generation of actual subgroup identity jets -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet

open Langlands.AlgebraicGeometry.Picard.LineHom

private theorem closedBaseChange_span
    {R : Type u} [CommRing R] {Y S X : Scheme.{u}} [IsAffine Y]
    (p : Y ⟶ Spec (.of R)) (b : S ⟶ Spec (.of R))
    (k : X ⟶ pullback p b) [IsClosedImmersion k]
    {f : X ⟶ S} (hk : k ≫ pullback.snd p b = f) (U : S.affineOpens) :
    letI := ((f.app U).hom.toAlgebra)
    Submodule.span Γ(S, U)
      (Set.range ((k ≫ pullback.fst p b).appLE ⊤
        (f ⁻¹ᵁ U) (le_preimage_top _ _))) = ⊤ := by
  subst f
  let := (((k ≫ pullback.snd p b).app U).hom.toAlgebra)
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let := Langlands.AlgebraicGeometry.FiniteLinearEquations.sectionsAlgebra (Over.mk p)
  have : IsAffineHom p := inferInstance
  have : IsAffineHom (pullback.snd p b) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  have : IsAffine (Over.mk p).left := inferInstanceAs (IsAffine Y)
  let W : (pullback p b).Opens := pullback.snd p b ⁻¹ᵁ U
  have hW : IsAffineOpen W := U.2.preimage (pullback.snd p b)
  let P : Submodule Γ(S, U) Γ(X, (k ≫ pullback.snd p b) ⁻¹ᵁ U) :=
    Submodule.span Γ(S, U)
      (Set.range ((k ≫ pullback.fst p b).appLE ⊤
        ((k ≫ pullback.snd p b) ⁻¹ᵁ U) (le_preimage_top _ _)))
  change P = ⊤
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨y, rfl⟩ := k.app_surjective W hW x
  obtain ⟨z, rfl⟩ := (sectionsTensorHom_bijective b (Over.mk p) U.2).surjective y
  induction z with
  | tmul a c =>
    rw [sectionsTensorHom_tmul, map_mul]
    have ha :
        k.app W ((pullback.fst p b).appLE ⊤ W (le_preimage_top _ _) a) =
          (k ≫ pullback.fst p b).appLE ⊤
            ((k ≫ pullback.snd p b) ⁻¹ᵁ U) (le_preimage_top _ _) a := by
      have h := Scheme.Hom.appLE_comp_appLE k (pullback.fst p b) ⊤ W
        (k ⁻¹ᵁ W) (le_preimage_top _ _) le_rfl
      rw [Scheme.Hom.appLE_eq_app] at h
      exact ConcreteCategory.congr_hom h a
    have hc :
        k.app W ((pullback.snd p b).app U c) =
          (k ≫ pullback.snd p b).app U c := by
      exact (ConcreteCategory.congr_hom
        (Scheme.Hom.comp_app k (pullback.snd p b) U) c).symm
    change k.app W ((pullback.fst p b).appLE ⊤ W (le_preimage_top _ _) a) *
      k.app W ((pullback.snd p b).app U c) ∈ _
    rw [ha, hc, mul_comm]
    exact P.smul_mem c (Submodule.subset_span ⟨a, rfl⟩)
  | add z z' hz hz' =>
    simpa only [map_add] using Submodule.add_mem _ hz hz'

open AffineCoordinates Corepresented

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  (b : S ⟶ Spec R) {H : GroupScheme S}
  (h : H ⟶ (GroupScheme.baseChange b).obj G)

attribute [local instance] sectionAlgebra

/-- Fixed ambient coordinates generate the actual subgroup functions on each
affine base open. -/
theorem ambient_coordinateMap_span
    [IsClosedImmersion h.hom.hom.left] (U : S.affineOpens) :
    Submodule.span Γ(S, U)
      (Set.range (coordinateMap H (ambientProjection G b h) U)) = ⊤ := by
  have hk : h.hom.hom.left ≫ pullback.snd G.X.hom b = H.X.hom :=
    Over.w h.hom.hom
  have hspan :
      Submodule.span Γ(S, U)
        (Set.range ((h.hom.hom.left ≫ pullback.fst G.X.hom b).appLE ⊤
          (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _))) = ⊤ := by
    exact closedBaseChange_span G.X.hom b h.hom.hom.left hk U
  have hsurj : Function.Surjective (fun a : algebra G =>
      (groupSchemeIso G).inv.hom.hom.left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv a)) :=
    (ConcreteCategory.bijective_of_isIso
      (groupSchemeIso G).inv.hom.hom.left.appTop).surjective.comp
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv).surjective
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := hsurj a
  apply Submodule.subset_span
  refine ⟨z, ?_⟩
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE
      (h.hom.hom.left ≫ pullback.fst G.X.hom b)
      (groupSchemeIso G).inv.hom.hom.left ⊤ ⊤
      (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _) (le_preimage_top _ _))
        ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv z)
  change
    ((groupSchemeIso G).inv.hom.hom.left.appLE ⊤
      ((groupSchemeIso G).inv.hom.hom.left ⁻¹ᵁ ⊤) le_rfl ≫
      (h.hom.hom.left ≫ pullback.fst G.X.hom b).appLE ⊤
        (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _))
      ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv z) = _ at hh
  rw [Scheme.Hom.appLE_eq_app] at hh
  change
    (h.hom.hom.left ≫ pullback.fst G.X.hom b).appLE ⊤
      (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _)
        ((groupSchemeIso G).inv.hom.hom.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv z)) =
      coordinateMap H (ambientProjection G b h) U z at hh
  exact hh.symm.trans (congrArg
    (fun w : Γ(G.X.left, ⊤) =>
      (h.hom.hom.left ≫ pullback.fst G.X.hom b).appLE ⊤
        (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _) w) hz)

section Quotient

variable {T : Scheme.{u}} (K : GroupScheme T) [IsAffineHom K.X.hom]
  {B : CommRingCat.{u}} (j : K.X.left ⟶ Spec B)
  (I : Ideal B) (hI : VanishesAtIdentity K j I)

/-- Generation of group functions descends to the actual identity jet, preserving
the prescribed global sections of the ambient quotient. -/
theorem quotientCoordinates_restrict_span (n : ℕ) (U : T.affineOpens)
    (hgen : Submodule.span Γ(T, U) (Set.range (coordinateMap K j U)) = ⊤) :
    Submodule.span Γ(T, U)
      (Set.range (fun z : B ⧸ I ^ (n + 1) =>
        (module K n).presheaf.map (homOfLE (show (U : T.Opens) ≤ ⊤ from le_top)).op
          (quotientCoordinates K j I hI n z))) = ⊤ := by
  let L : Γ(K.X.left, K.X.hom ⁻¹ᵁ U) →ₗ[Γ(T, U)] Γ(module K n, U) :=
    (sectionsEquiv K n U).symm.toLinearMap.comp
      (Ideal.Quotient.mkₐ Γ(T, U)
        (RingHom.ker (augmentation K U) ^ (n + 1))).toLinearMap
  have hL : Function.Surjective L :=
    (sectionsEquiv K n U).symm.surjective.comp
      (Ideal.Quotient.mkₐ_surjective Γ(T, U) _)
  have hspan : Submodule.span Γ(T, U)
      (L '' Set.range (coordinateMap K j U)) = ⊤ := by
    rw [← Submodule.map_span, hgen, Submodule.map_top, LinearMap.range_eq_top]
    exact hL
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  apply (sectionsEquiv K n U).injective
  rw [sectionsEquiv_restrict_quotientCoordinates]
  exact ((sectionsEquiv K n U).apply_symm_apply
    (Ideal.Quotient.mk _ (coordinateMap K j U a))).symm

end Quotient

/-- The ambient coordinate projection respects the actual map to the base. -/
theorem ambientProjection_over :
    ambientProjection G b h ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (algebra G))) = H.X.hom ≫ b := by
  change (h.hom.hom.left ≫ pullback.fst G.X.hom b ≫
    (groupSchemeIso G).inv.hom.hom.left) ≫
      (groupScheme (functor G) (corepresentation G)).X.hom = _
  rw [Category.assoc, Category.assoc, Over.w]
  change h.hom.hom.left ≫ pullback.fst G.X.hom b ≫ G.X.hom = _
  rw [pullback.condition, ← Category.assoc]
  exact congrArg (fun k => k ≫ b) (Over.w h.hom.hom)

/-- Ambient scalar functions are the actual base scalar functions. -/
theorem ambient_coordinateMap_algebraMap (U : S.Opens) (r : R) :
    coordinateMap H (ambientProjection G b h) U (algebraMap R (algebra G) r) =
      H.X.hom.app U (b.appLE ⊤ U (le_preimage_top _ _)
        ((Scheme.ΓSpecIso R).inv r)) := by
  have hh := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (algebra G)))) r
  change (Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv
      (algebraMap R (algebra G) r) =
    (Spec.map (CommRingCat.ofHom (algebraMap R (algebra G)))).appTop
      ((Scheme.ΓSpecIso R).inv r) at hh
  change (ambientProjection G b h).appLE ⊤ (H.X.hom ⁻¹ᵁ U)
    (le_preimage_top _ _) _ = _
  rw [hh]
  have hc := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE (ambientProjection G b h)
      (Spec.map (CommRingCat.ofHom (algebraMap R (algebra G)))) ⊤ ⊤
      (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _) (le_preimage_top _ _))
    ((Scheme.ΓSpecIso R).inv r)
  change (ambientProjection G b h).appLE ⊤ (H.X.hom ⁻¹ᵁ U)
      (le_preimage_top _ _)
      ((Spec.map (CommRingCat.ofHom (algebraMap R (algebra G)))).appTop
        ((Scheme.ΓSpecIso R).inv r)) =
    (ambientProjection G b h ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (algebra G)))).appLE ⊤
      (H.X.hom ⁻¹ᵁ U) (le_preimage_top _ _) ((Scheme.ΓSpecIso R).inv r) at hc
  rw [hc, ambientProjection_over]
  have hf := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE H.X.hom b ⊤ U (H.X.hom ⁻¹ᵁ U)
      (le_preimage_top _ _) le_rfl) ((Scheme.ΓSpecIso R).inv r)
  rw [Scheme.Hom.appLE_eq_app] at hf
  exact hf.symm

variable [IsAffineHom H.X.hom]

/-- Restriction of the fixed ambient quotient coordinates as an `R`-linear map. -/
def ambientQuotientCoordinateLinear (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : Module R Γ(module H n, U) :=
      Module.compHom _ (algebraMap R Γ(S, U))
    (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →ₗ[R] Γ(module H n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  letI : Module R Γ(module H n, U) :=
    Module.compHom _ (algebraMap R Γ(S, U))
  refine
    { toFun := fun z => (module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b h n z)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := ?_ }
  intro r z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  change (module H n).presheaf.map
      (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
        (ambientQuotientCoordinates G b h n (Ideal.Quotient.mk _ (r • a))) =
    (algebraMap R Γ(S, U) r) •
      (module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b h n (Ideal.Quotient.mk _ a))
  apply (sectionsEquiv H n U).injective
  rw [(sectionsEquiv H n U).map_smul]
  change sectionsEquiv H n U
      ((module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (quotientCoordinates H (ambientProjection G b h) _
            (ambientProjection_vanishesAtIdentity G b h) n
              (Ideal.Quotient.mk _ (r • a)))) =
    (algebraMap R Γ(S, U) r) • sectionsEquiv H n U
      ((module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (quotientCoordinates H (ambientProjection G b h) _
            (ambientProjection_vanishesAtIdentity G b h) n (Ideal.Quotient.mk _ a)))
  rw [sectionsEquiv_restrict_quotientCoordinates,
    sectionsEquiv_restrict_quotientCoordinates, Algebra.smul_def, map_mul,
    ambient_coordinateMap_algebraMap]
  rfl

/-- The actual affine tensor map induced by the fixed ambient truncated coordinates. -/
def ambientTensorCoordinates (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →ₗ[Γ(S, U)]
      Γ(module H n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  letI : Module R Γ(module H n, U) :=
    Module.compHom _ (algebraMap R Γ(S, U))
  letI : IsScalarTower R Γ(S, U) Γ(module H n, U) :=
    ⟨fun r a x => by
      change (algebraMap R Γ(S, U) r * a) • x =
        (algebraMap R Γ(S, U) r) • (a • x)
      exact mul_smul _ _ _⟩
  exact (ambientQuotientCoordinateLinear G b h n U).liftBaseChange Γ(S, U)

@[simp]
theorem ambientTensorCoordinates_tmul (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (z : algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ambientTensorCoordinates G b h n U (a ⊗ₜ[R] z) =
      a • (module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b h n z) := rfl

/-- Fixed ambient truncated coordinates generate sections of the actual subgroup
identity jet over every affine base open. -/
theorem ambientQuotientCoordinates_restrict_span
    [IsClosedImmersion h.hom.hom.left] (n : ℕ) (U : S.affineOpens) :
    Submodule.span Γ(S, U)
      (Set.range (fun z : algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1) =>
        (module H n).presheaf.map (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b h n z))) = ⊤ :=
  quotientCoordinates_restrict_span H (ambientProjection G b h)
    (augIdeal (corepresentation G)) (ambientProjection_vanishesAtIdentity G b h) n U
      (ambient_coordinateMap_span G b h U)

/-- Every actual affine jet section is in the image of the fixed ambient tensor map. -/
theorem ambientTensorCoordinates_surjective
    [IsClosedImmersion h.hom.hom.left] (n : ℕ) (U : S.affineOpens) :
    let := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Function.Surjective (ambientTensorCoordinates G b h n U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : Module R Γ(module H n, U) :=
    Module.compHom _ (algebraMap R Γ(S, U))
  let : IsScalarTower R Γ(S, U) Γ(module H n, U) :=
    ⟨fun r a x => by
      change (algebraMap R Γ(S, U) r * a) • x =
        (algebraMap R Γ(S, U) r) • (a • x)
      exact mul_smul _ _ _⟩
  rw [← LinearMap.range_eq_top]
  change LinearMap.range
    ((ambientQuotientCoordinateLinear G b h n U).liftBaseChange Γ(S, U)) = ⊤
  rw [LinearMap.range_liftBaseChange]
  exact ambientQuotientCoordinates_restrict_span G b h n U

end Langlands.GroupScheme.IdentityJet
