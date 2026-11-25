/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierSplitProjector
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedCoefficientCoverMaps

/-! # Coefficient pullback along actual morphisms of covers

Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, restriction of
coefficient functions in the first paragraph and the negating-roots construction
(blueprint: lem-wft-as-coefficient-pull-calculus).

The regular lift is the adjunct of the inverse monoidal unit comparison. Comparing
its value on one identifies its underlying map with the coefficient morphism.
The coefficient identity and composition laws then combine with lower-star unit,
associativity and equality-transport comparisons to prove the contravariant functor
laws. Evaluation identities follow from their actual functor-map/counit formula.
Finally, the mate of upperStarFromPointComp respects constant global scalars.
The resulting ΓΛ-linearity identifies regular scalar maps with scalar multiples of
identities, so they commute with every module map. Applying this term by term to
the finite sum proves equivariant conjugacy of the actual averaging projectors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The regular lift in condensedPull is the adjunct of the canonical unit comparison. -/
theorem condensedCoefficientLift_eq_adjunct {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ f) =
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
        (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ f)).inv := by
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift, ProEtale.CondensedRing.homEquiv_εIso_inv_hom]

/-- On underlying abelian sheaves, the regular lift is the coefficient morphism itself. -/
theorem condensedCoefficientLift_hom {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ f)).hom =
      ProEtale.condensedPushforwardHom Λ f := by
  rw [condensedCoefficientLift_eq_adjunct,
    ProEtale.CondensedRing.homEquiv_εIso_inv_hom]

/-- The coefficient lift respects composition, with the actual lower-star comparison. -/
theorem condensedCoefficientLift_comp {W Y Z : Scheme.{u}} (g : W ⟶ Y) (f : Y ⟶ Z) :
    Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ (g ≫ f)).obj (condensedUnit Λ W))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ (g ≫ f)) =
      Mod.regularLift
          ((ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y))
          (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ f) ≫
        (ProEtale.CondensedRing.lowerStar Λ f).map
          (Mod.regularLift
            ((ProEtale.CondensedRing.lowerStar Λ g).obj (condensedUnit Λ W))
            (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ g)) ≫
          (ProEtale.CondensedRing.lowerStarComp Λ g f).hom.app (condensedUnit Λ W) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', ProEtale.CondensedRing.lowerStar_map_hom,
    ProEtale.CondensedRing.lowerStarComp_hom_app_hom, condensedCoefficientLift_hom]
  exact ProEtale.condensedPushforwardHom_comp Λ g f

omit [IsCommMonObj Λ] in
/-- The coefficient lift along an identity is the inverse pushforward unit comparison. -/
theorem condensedCoefficientLift_id (X : Scheme.{u}) :
    Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ (𝟙 X)).obj (condensedUnit Λ X))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ (𝟙 X)) =
      (ProEtale.CondensedRing.lowerStarId Λ X).inv.app (condensedUnit Λ X) := by
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift, ProEtale.condensedPushforwardHom_id]
  rfl

/-- Pulling coefficient functions along an identity cover map is the identity. -/
theorem condensedPull_id {X : Scheme.{u}} (Y : Over X) :
    condensedPull Λ (𝟙 Y) = 𝟙 _ := by
  unfold condensedPull
  change (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
      (Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ (𝟙 Y.left)).obj (condensedUnit Λ Y.left))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ (𝟙 Y.left))) ≫
    (ProEtale.CondensedRing.lowerStarComp Λ (𝟙 Y.left) Y.hom).hom.app _ ≫
      (ProEtale.CondensedRing.lowerStarCongr Λ (Category.id_comp Y.hom)).hom.app _ = 𝟙 _
  rw [condensedCoefficientLift_id]
  rw [ProEtale.CondensedRing.lowerStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact Category.id_comp _

private def coefficientLowerStarFactor {W Y Z : Scheme.{u}}
    {a : W ⟶ Z} {b : W ⟶ Y} {c : Y ⟶ Z} (e : b ≫ c = a) :=
  ProEtale.CondensedRing.lowerStarComp Λ b c ≪≫
    ProEtale.CondensedRing.lowerStarCongr Λ e

omit [IsCommMonObj Λ] in
private theorem coefficientLowerStarFactor_rfl {W Y Z : Scheme.{u}}
    (b : W ⟶ Y) (c : Y ⟶ Z) :
    coefficientLowerStarFactor Λ (rfl : b ≫ c = b ≫ c) =
      ProEtale.CondensedRing.lowerStarComp Λ b c := by
  simp only [coefficientLowerStarFactor, ProEtale.CondensedRing.lowerStarCongr,
    eqToIso_refl, Iso.trans_refl]

omit [IsCommMonObj Λ] in
private theorem coefficientLowerStarFactor_assoc {W Y Z X : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X)
    (a : W ⟶ Z) (b : Y ⟶ X) (c : W ⟶ X)
    (e₁ : f ≫ g = a) (e₂ : g ≫ h = b) (e₃ : f ≫ b = c) :
    (ProEtale.CondensedRing.lowerStar Λ f).associator
        (ProEtale.CondensedRing.lowerStar Λ g) (ProEtale.CondensedRing.lowerStar Λ h) ≪≫
      Functor.isoWhiskerLeft (ProEtale.CondensedRing.lowerStar Λ f)
        (coefficientLowerStarFactor Λ e₂) ≪≫ coefficientLowerStarFactor Λ e₃ =
    Functor.isoWhiskerRight (coefficientLowerStarFactor Λ e₁)
        (ProEtale.CondensedRing.lowerStar Λ h) ≪≫
      coefficientLowerStarFactor Λ (show a ≫ h = c by rw [← e₁, Category.assoc, e₂, e₃]) := by
  subst a b c
  simp only [coefficientLowerStarFactor, ProEtale.CondensedRing.lowerStarCongr,
    eqToIso_refl, Iso.trans_refl]
  exact ProEtale.CondensedRing.lowerStarComp_assoc Λ f g h

/-- Evaluation is compatible with a map into the coefficient direct image. -/
theorem condensedEvaluation_precomp {X T : Scheme.{u}} (x : T ⟶ X)
    {Y : Over X} (s : Over.mk x ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a : N ⟶ M)
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    (ProEtale.CondensedRing.upperStar Λ x).map a ≫ condensedEvaluation Λ x s ι =
      condensedEvaluation Λ x s (a ≫ ι) := by
  simp only [condensedEvaluation, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Pulling functions back along a cover map agrees with evaluation at the composed root. -/
theorem condensedEvaluation_comp_cover {X T : Scheme.{u}} (x : T ⟶ X)
    {Y Z : Over X} (s : Over.mk x ⟶ Y) (h : Y ⟶ Z)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left)) :
    condensedEvaluation Λ x (s ≫ h) ι =
      condensedEvaluation Λ x s (ι ≫ condensedPull Λ h) := by
  simp only [condensedEvaluation, condensedPull_comp, Category.assoc]

/-- An actual isomorphism of covers gives an isomorphism of coefficient functions. -/
def condensedCoverIso {X : Scheme.{u}} {Y Z : Over X} (e : Y ≅ Z) :
    (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) ≅
      (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left) where
  hom := condensedPull Λ e.inv
  inv := condensedPull Λ e.hom
  hom_inv_id := by
    rw [← condensedPull_comp, e.hom_inv_id, condensedPull_id]
  inv_hom_id := by
    rw [← condensedPull_comp, e.inv_hom_id, condensedPull_id]

/-- Cover conjugacy is contravariantly transported to coefficient functions. -/
theorem condensedPull_conjugacy {X : Scheme.{u}} {Y Z : Over X} (e : Y ≅ Z)
    (a : Y ⟶ Y) (b : Z ⟶ Z) (hab : a ≫ e.hom = e.hom ≫ b) :
    condensedPull Λ a ≫ (condensedCoverIso Λ e).hom =
      (condensedCoverIso Λ e).hom ≫ condensedPull Λ b := by
  change condensedPull Λ a ≫ condensedPull Λ e.inv =
    condensedPull Λ e.inv ≫ condensedPull Λ b
  rw [← condensedPull_comp, ← condensedPull_comp]
  congr 1
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hab, Iso.inv_hom_id_assoc]

private instance additiveFromPoint (X : Scheme.{u}) :
    (ProEtale.upperStarFromPoint X).Additive := by
  have adj : ProEtale.upperStarFromPoint X ⊣ _ :=
    ProEtale.pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (ProEtale.toSpecZ X))
  have : (ProEtale.upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (ProEtale.upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (ProEtale.upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (ProEtale.upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

private def coefficientScalars (X : Scheme.{u}) :
    MonObj.Γ Λ →+* MonObj.Γ (ProEtale.condensedRingObj Λ X) :=
  MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint X)

@[instance_reducible] private def coefficientLinear (X : Scheme.{u}) :
    Linear (MonObj.Γ Λ)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (ProEtale.condensedRingObj Λ X)) :=
  Mod.linearOfRingHom (coefficientScalars Λ X)

attribute [local instance] coefficientLinear

private theorem coefficientLinear_lowerStar {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (ProEtale.CondensedRing.lowerStar Λ f).Linear (MonObj.Γ Λ) := by
  apply Mod.linear_mapMod_comp_comap
    (ProEtale.lowerStar Ab.{u + 1} f) (ProEtale.condensedPushforwardHom Λ f)
    (coefficientScalars Λ Y) (coefficientScalars Λ Z)
  intro a
  simp only [coefficientScalars, MonObj.Γ.mapFunctor_hom,
    ProEtale.condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (ProEtale.upperStarFromPoint Z) (ProEtale.upperStarFromPoint Y)
    (ProEtale.upperStarFromPointComp f).hom a.hom

attribute [local instance] coefficientLinear_lowerStar

private theorem coefficientScalar_eq_smul (X : Scheme.{u}) (a : MonObj.Γ Λ) :
    (Mod.regularEndRingHom
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) a)).asHom =
      a • 𝟙 (condensedUnit Λ X) := by
  rw [Mod.linearOfRingHom_smul_id (coefficientScalars Λ X)]
  apply Mod.hom_ext
  simp only [Mod.regularEndRingHom_apply, Mod.regularLift, Mod.homMk_hom,
    Mod.smulNatTrans_app_hom]
  change (ρ_ (ProEtale.condensedRingObj Λ X)).inv ≫
      ProEtale.condensedRingObj Λ X ◁ (coefficientScalars Λ X a).hom ≫ MonObj.mul = _
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq
    (S := ProEtale.condensedRingObj Λ X) (coefficientScalars Λ X a).hom

private theorem mappedCoefficientScalar {X : Scheme.{u}} (T : Over X) (a : MonObj.Γ Λ) :
    (ProEtale.CondensedRing.lowerStar Λ T.hom).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint T.left) a)).asHom =
      a • 𝟙 ((ProEtale.CondensedRing.lowerStar Λ T.hom).obj (condensedUnit Λ T.left)) := by
  exact (congrArg (ProEtale.CondensedRing.lowerStar Λ T.hom).map
    (coefficientScalar_eq_smul Λ T.left a)).trans
      (((ProEtale.CondensedRing.lowerStar Λ T.hom).map_smul a _).trans
        (congrArg (fun t ↦ a • t)
          ((ProEtale.CondensedRing.lowerStar Λ T.hom).map_id _)))

/-- Constant coefficient scalars commute with every morphism of pushed-forward modules. -/
theorem condensedCoefficientScalar_naturality {X : Scheme.{u}} {Y Z : Over X}
    (a : MonObj.Γ Λ)
    (f : (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) ⟶
      (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left)) :
    f ≫ (ProEtale.CondensedRing.lowerStar Λ Z.hom).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Z.left) a)).asHom =
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y.left) a)).asHom ≫ f := by
  rw [mappedCoefficientScalar, mappedCoefficientScalar]
  calc
    _ = a • f := by rw [Linear.comp_smul, Category.comp_id]
    _ = (a • 𝟙 _) ≫ f :=
      ((Linear.smul_comp _ _ _ a (𝟙 _) f).trans
        (congrArg (fun t ↦ a • t) (Category.id_comp f))).symm

/-- Equivariant cover isomorphisms intertwine the actual averaging endomorphisms. -/
theorem condensedProjector_conjugacy (G : Type v) [AddGroup G] [Fintype G]
    {X : Scheme.{u}} {Y Z : Over X} (e : Y ≅ Z)
    (σY : G → (Y ⟶ Y)) (σZ : G → (Z ⟶ Z))
    (hσ : ∀ c, σY c ≫ e.hom = e.hom ≫ σZ c) (χ : AddChar G (MonObj.Γ Λ)) :
    (condensedProjector Λ G Y σY χ).asHom ≫ (condensedCoverIso Λ e).hom =
      (condensedCoverIso Λ e).hom ≫ (condensedProjector Λ G Z σZ χ).asHom := by
  classical
  unfold condensedProjector
  simp only [End.sum_asHom]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Category.assoc, ← condensedCoefficientScalar_naturality]
  rw [← Category.assoc, condensedPull_conjugacy Λ e (σY c) (σZ c) (hσ c)]
  exact Category.assoc _ _ _

private theorem condensedProjector_eq_actionProjector
    (G : Type v) [AddCommGroup G] [Fintype G]
    {X : Scheme.{u}} (Y : Over X) (σ : G → (Y ⟶ Y)) (χ : AddChar G (MonObj.Γ Λ)) :
    condensedProjector Λ G Y σ χ = ArtinSchreierUnit.actionProjector
      ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left))
      (fun c ↦ End.of (condensedPull Λ (σ c))) χ := by
  unfold condensedProjector ArtinSchreierUnit.actionProjector
  apply Finset.sum_congr rfl
  intro c hc
  apply End.ext
  have hs := mappedCoefficientScalar Λ Y
    (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c))
  calc
    _ = condensedPull Λ (σ c) ≫
        ((Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c)) • 𝟙 _) :=
      congrArg (fun t ↦ condensedPull Λ (σ c) ≫ t) hs
    _ = _ := (Linear.comp_smul _ _ _ _ _ _).trans
      (congrArg (fun t ↦ (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c)) • t)
        (Category.comp_id _))

/-- The actual averaging endomorphism of an additive cover action is idempotent. -/
theorem condensedProjector_idempotent
    (G : Type v) [AddCommGroup G] [Fintype G]
    {X : Scheme.{u}} (Y : Over X) (σ : G → (Y ⟶ Y))
    (hσ : ∀ a b, σ (a + b) = σ a ≫ σ b)
    (χ : AddChar G (MonObj.Γ Λ)) (hq : IsUnit (Fintype.card G : MonObj.Γ Λ)) :
    (condensedProjector Λ G Y σ χ).asHom ≫ (condensedProjector Λ G Y σ χ).asHom =
      (condensedProjector Λ G Y σ χ).asHom := by
  rw [condensedProjector_eq_actionProjector]
  apply ArtinSchreierUnit.actionProjector_idempotent _ _ χ _ hq
  intro a b
  rw [add_comm a b, hσ b a, condensedPull_comp]

/-- The specified image inclusion and projection split the averaging idempotent. -/
theorem condensedProjector_image_retraction
    (G : Type v) [AddCommGroup G] [Fintype G]
    {X : Scheme.{u}} (Y : Over X) (σ : G → (Y ⟶ Y))
    (hσ : ∀ a b, σ (a + b) = σ a ≫ σ b)
    (χ : AddChar G (MonObj.Γ Λ)) (hq : IsUnit (Fintype.card G : MonObj.Γ Λ)) :
    image.ι (condensedProjector Λ G Y σ χ).asHom ≫
        factorThruImage (condensedProjector Λ G Y σ χ).asHom = 𝟙 _ := by
  rw [← cancel_mono (image.ι _), ← cancel_epi (factorThruImage _)]
  simp only [Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
  exact condensedProjector_idempotent Λ G Y σ hσ χ hq


end AlgebraicGeometry.ArtinSchreierTrace
