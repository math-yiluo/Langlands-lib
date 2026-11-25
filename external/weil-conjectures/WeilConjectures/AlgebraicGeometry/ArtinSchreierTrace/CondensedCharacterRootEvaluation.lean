/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.SplitCondensedRegularProduct
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedCoefficientCoverMaps
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedSheetScalars
import WeilConjectures.CategoryTheory.CharacterMatrixImage
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Evaluation of a character projector on a split torsor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local implicit_reducible] condensedUnit
attribute [local implicit_reducible] CommMon.toMon
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory Mod.monoidalCategory Mod.monoidalCategoryStruct Monoidal.induced

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarLowerStarAdjunction
  ProEtale.CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod

private instance pointColimits (X : Scheme.{u}) :
    PreservesColimits (ProEtale.upperStarFromPoint X) :=
  (ProEtale.pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
      (ProEtale.toSpecZ X))).leftAdjoint_preservesColimits

private instance pointAdditive (X : Scheme.{u}) :
    (ProEtale.upperStarFromPoint X).Additive := by
  have : PreservesBinaryBiproducts (ProEtale.upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem evaluation_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (x : T ⟶ X) (s : Over.mk x ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (v : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    (ProEtale.CondensedRing.upperStar Λ x).map v ≫
      condensedEvaluation Λ x s (𝟙 _) = condensedEvaluation Λ x s v := by
  simp only [condensedEvaluation, Category.id_comp, Functor.map_comp, Category.assoc]

private theorem evaluation_precomp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (x : T ⟶ X) (s : Over.mk x ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a : N ⟶ M)
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    (ProEtale.CondensedRing.upperStar Λ x).map a ≫ condensedEvaluation Λ x s ι =
      condensedEvaluation Λ x s (a ≫ ι) := by
  simp only [condensedEvaluation, Functor.map_comp, Category.assoc]

private theorem evaluation_pull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} {Y Z : Over X}
    (x : T ⟶ X) (s : Over.mk x ⟶ Y) (h : Y ⟶ Z) :
    (ProEtale.CondensedRing.upperStar Λ x).map (condensedPull Λ h) ≫
      condensedEvaluation Λ x s (𝟙 _) =
      condensedEvaluation Λ x (s ≫ h) (𝟙 _) := by
  simp only [condensedEvaluation, Category.id_comp, ← Functor.map_comp_assoc,
    condensedPull_comp]

/-- The value of an averaged coefficient function at a root is the weighted sum
of its values at the translated roots.
Source: blueprint lemma-artin-schreier-character-sheaf, explicit averaging projector
(blueprint: lem-fd-as-character-root-evaluation).

Proof: expand the finite sum defining the projector, move each constant scalar
through root evaluation, and compose pullbacks of functions. -/
theorem condensedProjector_rootEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (G : Type v) [AddGroup G] [Fintype G] (σ : G → (Y ⟶ Y))
    (χ : AddChar G (MonObj.Γ Λ)) (x : T ⟶ X) (s : Over.mk x ⟶ Y) :
    (ProEtale.CondensedRing.upperStar Λ x).map (condensedProjector Λ G Y σ χ).asHom ≫
        condensedEvaluation Λ x s (𝟙 _) =
      ∑ c : G, condensedEvaluation Λ x (s ≫ σ c) (𝟙 _) ≫
        (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom
          (ProEtale.upperStarFromPoint T)
          (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c)))).asHom := by
  classical
  let : (ProEtale.CondensedRing.upperStar Λ x).Additive :=
    ProEtale.CondensedRing.upperStar_additive Λ x
  simp only [condensedProjector, End.sum_asHom,
    Functor.map_sum (ProEtale.CondensedRing.upperStar Λ x), Functor.map_comp,
    Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro c hc
  have hs := sheetProjection_scalar Λ Y.hom x s.left (Over.w s)
    (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c))
  rw [← condensedEvaluation_id_eq_sheetProjection Λ Y x s] at hs
  rw [hs, ← Category.assoc, evaluation_pull]

private theorem evaluation_translation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (G : Type v) [AddCommGroup G] (σ : Multiplicative G →* Aut Y)
    (x : T ⟶ X) (s : Over.mk x ⟶ Y) (a c : G) :
    (ProEtale.CondensedRing.upperStar Λ x).map
        (condensedPull Λ (σ (Multiplicative.ofAdd c)).asIso.hom) ≫
      condensedEvaluation Λ x (s ≫ (σ (Multiplicative.ofAdd a)).asIso.hom) (𝟙 _) =
    condensedEvaluation Λ x (s ≫ (σ (Multiplicative.ofAdd (a + c))).asIso.hom) (𝟙 _) := by
  have he : (s ≫ (σ (Multiplicative.ofAdd a)).asIso.hom) ≫
      (σ (Multiplicative.ofAdd c)).asIso.hom =
      s ≫ (σ (Multiplicative.ofAdd (a + c))).asIso.hom := by
    rw [Category.assoc]
    congr 1
    rw [add_comm a c, ofAdd_add, map_mul, Aut.mul_asIso, Iso.trans_hom]
  simp only [condensedEvaluation, Category.id_comp, ← Functor.map_comp_assoc]
  rw [← he, condensedPull_comp Λ (s ≫ _) _]

/-- On a chart with root-labelled sheets, evaluation at the root trivializes the
image of the character projector.
Source: blueprint lemma-artin-schreier-character-sheaf, Step 4, eigenfunction evaluation
(blueprint: lem-fd-as-character-root-evaluation).

Proof: the sheet projections identify the direct image with the finite product
of coefficient objects. Translation by c replaces the a-component by the
(a+c)-component. Constant scalars commute with the projections. Reindexing the
averaging sum therefore gives matrix entry n⁻¹χ(a-b). The character-matrix image
lemma identifies its image with the coefficient object by the zero projection.
Exact pullback preserves images, so this is precisely the stated evaluation. -/
theorem condensedCharacterImage_rootEvaluation_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (G : Type v) [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    (hn : IsUnit (Fintype.card G : MonObj.Γ Λ))
    (x : T ⟶ X) [WeaklyEtale x] (s : Over.mk x ⟶ Y)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback Y.hom x)
      (fun a : G ↦ pullback.lift (s.left ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left)
        (𝟙 T) (by
          simp only [Category.assoc, Over.w, Over.mk_hom]
          exact (Category.id_comp x).symm))))) :
    IsIso (condensedEvaluation Λ x s
      (image.ι (condensedProjector Λ G Y
        (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom)) := by
  classical
  let F := ProEtale.CondensedRing.upperStar Λ x
  let : F.Additive := ProEtale.CondensedRing.upperStar_additive Λ x
  let P := (condensedProjector Λ G Y (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom
  let E (a : G) := condensedEvaluation Λ x (s ≫ (σ (Multiplicative.ofAdd a)).asIso.hom) (𝟙 _)
  let r : MonObj.Γ Λ →+* End (condensedUnit Λ T) :=
    Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint T))
  have hE (a : G) : E a = sheetProjection Λ Y.hom x
      (s.left ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left)
      (by simp only [Category.assoc, Over.w, Over.mk_hom]) :=
    condensedEvaluation_id_eq_sheetProjection Λ Y x _
  have hq : IsIso (Pi.lift E) := by
    have hEf := funext hE
    rw [hEf]
    exact sheetProjection_product_isIso Λ Y.hom x G _ _ hc
  let q := asIso (Pi.lift E)
  have he (a : G) : F.map P ≫ q.hom ≫ Pi.π (fun _ : G ↦ condensedUnit Λ T) a =
      ∑ b : G, (q.hom ≫ Pi.π (fun _ : G ↦ condensedUnit Λ T) b) ≫
        (r (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (a - b))).asHom := by
    simp only [q, asIso_hom, Pi.lift_comp_π]
    change F.map P ≫ E a = ∑ b : G, E b ≫ (r
      (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (a - b))).asHom
    simp only [P, condensedProjector, End.sum_asHom, Functor.map_sum F, Functor.map_comp,
      Preadditive.sum_comp, Category.assoc]
    have hs (c : G) : F.map
        ((ProEtale.CondensedRing.lowerStar Λ Y.hom).map
          (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom
            (ProEtale.upperStarFromPoint Y.left)
            (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c)))).asHom) ≫ E a =
        E a ≫ (r (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c))).asHom := by
      rw [hE]
      exact sheetProjection_scalar Λ Y.hom x _ _ _
    have ht (c : G) : F.map
        (condensedPull Λ (σ (Multiplicative.ofAdd c)).asIso.hom) ≫ E a = E (a + c) :=
      evaluation_translation Λ Y G σ x s a c
    simp_rw [hs, ← Category.assoc, ht]
    apply Fintype.sum_equiv (Equiv.addLeft a)
    intro c
    simp only [Equiv.coe_addLeft, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hi := characterMatrix_image_evaluation_isIso r G χ hn q (End.of (F.map P)) he
  have hzero : E 0 = condensedEvaluation Λ x s (𝟙 _) := by
    simp only [E, ofAdd_zero, map_one]
    change condensedEvaluation Λ x (s ≫ 𝟙 Y) (𝟙 _) = _
    rw [Category.comp_id]
  have hm : image.ι (F.map P) ≫ q.hom ≫ Pi.π (fun _ : G ↦ condensedUnit Λ T) 0 =
      image.ι (F.map P) ≫ condensedEvaluation Λ x s (𝟙 _) := by
    simp only [q, asIso_hom, Pi.lift_comp_π, hzero]
  rw [hm] at hi
  have hh : condensedEvaluation Λ x s (image.ι P) =
      (PreservesImage.iso F P).inv ≫ image.ι (F.map P) ≫
        condensedEvaluation Λ x s (𝟙 _) := by
    rw [← evaluation_map Λ Y x s]
    rw [← PreservesImage.hom_comp_map_image_ι F P]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, F]
  rw [hh]
  infer_instance

/-- Constants give the inverse of root evaluation on the trivial-character
image, after pullback to a root chart.
Source: blueprint lemma-artin-schreier-character-sheaf, trivial-character clause
(blueprint: lem-fd-as-character-root-evaluation).

Proof: the image factorization replaces the composite with the image inclusion
by the projector. Its evaluation is the weighted sum of translated evaluations.
Each constant has the same value at every root; the sum of n copies of n⁻¹ is 1. -/
theorem condensedTrivialCharacter_constantMap_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (Y : Over X)
    (G : Type v) [AddGroup G] [Fintype G] (σ : G → (Y ⟶ Y))
    (hn : IsUnit (Fintype.card G : MonObj.Γ Λ))
    (x : T ⟶ X) (s : Over.mk x ⟶ Y) :
    let P := (condensedProjector Λ G Y σ (1 : AddChar G (MonObj.Γ Λ))).asHom
    let u : condensedUnit Λ X ⟶
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) :=
    Mod.regularLift
      ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left))
      (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ Y.hom)
    (ProEtale.CondensedRing.upperStar Λ x).map (u ≫ factorThruImage P) ≫
      condensedEvaluation Λ x s (image.ι P) =
        (regularUnitIso Λ x).inv := by
  classical
  dsimp only
  let F := ProEtale.CondensedRing.upperStar Λ x
  let u : condensedUnit Λ X ⟶
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) :=
    Mod.regularLift
    ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left))
    (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ Y.hom)
  let r : MonObj.Γ Λ →+* End (condensedUnit Λ T) :=
    Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint T))
  let eps := (regularUnitIso Λ x).inv
  rw [evaluation_precomp, Category.assoc, image.fac, ← evaluation_map Λ Y x s]
  rw [Functor.map_comp, Category.assoc, condensedProjector_rootEvaluation,
    Preadditive.comp_sum]
  have hu (c : G) : F.map u ≫
      condensedEvaluation Λ x (s ≫ σ c) (𝟙 _) = eps := by
    rw [evaluation_map]
    exact condensedEvaluation_coefficientUnit Λ Y x (s ≫ σ c)
  change ∑ c : G, F.map u ≫ condensedEvaluation Λ x (s ≫ σ c) (𝟙 _) ≫
    (r (Ring.inverse (Fintype.card G : MonObj.Γ Λ) *
      (1 : AddChar G (MonObj.Γ Λ)) (-c))).asHom = eps
  simp only [← Category.assoc, hu, AddChar.one_apply, mul_one,
    Finset.sum_const, Finset.card_univ]
  rw [← Preadditive.comp_nsmul, ← End.nsmul_asHom, ← map_nsmul r, nsmul_eq_mul,
    Ring.mul_inverse_cancel _ hn, map_one, End.one_asHom]
  exact Category.comp_id eps

end AlgebraicGeometry.ArtinSchreierTrace
