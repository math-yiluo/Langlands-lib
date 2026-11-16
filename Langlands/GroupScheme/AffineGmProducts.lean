import Langlands.GroupScheme.AffineGmEquivariantMap
import Langlands.GroupScheme.ImageGenerationCommutator
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.Dynamic.SchemeActionLimit

/-! # Action-interface comparison and products of fixed and attracting schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}

/-- Express the same actual categorical action through its all-test point laws. -/
def toPointwiseSchemeAction (a : SchemeAction H X) : PointwiseSchemeAction H X where
  hom := a.hom
  one_left := a.act_one
  mul_left := a.act_mul

@[simp] theorem toPointwiseSchemeAction_act (a : SchemeAction H X)
    {T : Over S} (h : T ⟶ H.X) (x : T ⟶ X) :
    a.toPointwiseSchemeAction.act h x = a.act h x := rfl

@[simp] theorem toPointwiseSchemeAction_isFixed (a : SchemeAction H X)
    {T : Over S} (x : T ⟶ X) :
    a.toPointwiseSchemeAction.IsFixed x ↔ a.IsFixed x := Iff.rfl

end SchemeAction

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X Y : Over S}

/-- Recover the categorical action from the supplied actual morphism and point laws. -/
@[instance_reducible] def toSchemeAction (a : PointwiseSchemeAction H X) : SchemeAction H X :=
  schemeActionOfPointLaws a.hom a.one_left a.mul_left

@[simp] theorem toSchemeAction_hom (a : PointwiseSchemeAction H X) :
    a.toSchemeAction.hom = a.hom := rfl

@[simp] theorem toSchemeAction_act (a : PointwiseSchemeAction H X)
    {T : Over S} (h : T ⟶ H.X) (x : T ⟶ X) :
    a.toSchemeAction.act h x = a.act h x := rfl

@[simp] theorem toSchemeAction_isFixed (a : PointwiseSchemeAction H X)
    {T : Over S} (x : T ⟶ X) :
    a.toSchemeAction.IsFixed x ↔ a.IsFixed x := Iff.rfl

@[simp] theorem toSchemeAction_toPointwiseSchemeAction (a : PointwiseSchemeAction H X) :
    a.toSchemeAction.toPointwiseSchemeAction = a := by
  cases a
  rfl

variable (a : PointwiseSchemeAction H X) (b : PointwiseSchemeAction H Y)

/-- The first projection of the existing diagonal product action is equivariant. -/
theorem prod_isEquivariant_fst : (a.prod b).IsEquivariant a (fst X Y) := by
  intro T h x
  exact prod_act_fst a b h x

/-- The second projection of the existing diagonal product action is equivariant. -/
theorem prod_isEquivariant_snd : (a.prod b).IsEquivariant b (snd X Y) := by
  intro T h x
  exact prod_act_snd a b h x

/-- All-refinement fixedness in a product is fixedness in both factors. -/
theorem prod_isFixed_iff {T : Over S} (x : T ⟶ X ⊗ Y) :
    (a.prod b).IsFixed x ↔ a.IsFixed (x ≫ fst X Y) ∧ b.IsFixed (x ≫ snd X Y) := by
  constructor
  · intro hx
    exact ⟨IsEquivariant.map_isFixed (a.prod b) a (prod_isEquivariant_fst a b) hx,
      IsEquivariant.map_isFixed (a.prod b) b (prod_isEquivariant_snd a b) hx⟩
  · rintro ⟨hx, hy⟩ V c h
    apply CartesianMonoidalCategory.hom_ext
    · rw [prod_act_fst, Category.assoc, hx]
    · rw [prod_act_snd, Category.assoc, hy]

variable {X Y : Over S}
  (a : PointwiseSchemeAction (Gm S).toGrp X)
  (b : PointwiseSchemeAction (Gm S).toGrp Y)

@[simp] theorem toSchemeAction_gmOrbit {T : Over S} (x : T ⟶ X) :
    a.toSchemeAction.gmOrbit x = a.orbit x := rfl

/-- Both interfaces require the same actual affine-line extension. -/
theorem toSchemeAction_isGmOrbitExtension_iff {T : Over S} (x : T ⟶ X)
    (E : T ⊗ AffineLine.scheme S ⟶ X) :
    a.toSchemeAction.IsGmOrbitExtension x E ↔
      T ◁ AffineLine.unitInclusion S ≫ E = a.orbit x := Iff.rfl

/-- An actual product orbit extends precisely when both component orbits extend. -/
theorem prod_isAttracted_iff {T : Over S} (x : T ⟶ X ⊗ Y) :
    (a.prod b).IsAttracted x ↔
      a.IsAttracted (x ≫ fst X Y) ∧ b.IsAttracted (x ≫ snd X Y) := by
  constructor
  · intro hx
    exact ⟨IsEquivariant.map_isAttracted (a.prod b) a (prod_isEquivariant_fst a b) hx,
      IsEquivariant.map_isAttracted (a.prod b) b (prod_isEquivariant_snd a b) hx⟩
  · rintro ⟨⟨E, hE⟩, ⟨F, hF⟩⟩
    refine ⟨lift E F, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, hE]
      exact (IsEquivariant.orbit_comp (a.prod b) a (prod_isEquivariant_fst a b) x).symm
    · rw [Category.assoc, lift_snd, hF]
      exact (IsEquivariant.orbit_comp (a.prod b) b (prod_isEquivariant_snd a b) x).symm

end PointwiseSchemeAction

namespace SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}

@[simp] theorem toPointwiseSchemeAction_toSchemeAction (a : SchemeAction H X) :
    a.toPointwiseSchemeAction.toSchemeAction = a :=
  ModObj.ext _ _ rfl

end SchemeAction

namespace GmCoordinateAction

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}
  [IsAffine X.left] [IsAffine Y.left]
  (a : PointwiseSchemeAction (Gm (Spec R)).toGrp X)
  (b : PointwiseSchemeAction (Gm (Spec R)).toGrp Y)

local instance : IsAffine (X ⊗ Y).left := by
  change IsAffine (CategoryTheory.Limits.pullback X.hom Y.hom)
  infer_instance

/-- The product of the fixed inclusions is fixed for the diagonal action. -/
theorem fixedProdHom_isFixed :
    (a.prod b).IsFixed (schemeActionFixedHom a ⊗ₘ schemeActionFixedHom b) := by
  rw [PointwiseSchemeAction.prod_isFixed_iff]
  constructor
  · rw [tensorHom_fst]
    intro V c h
    simpa only [Category.assoc] using
      schemeActionFixedHom_isFixed a V (c ≫ fst _ (schemeActionFixedScheme b)) h
  · rw [tensorHom_snd]
    intro V c h
    simpa only [Category.assoc] using
      schemeActionFixedHom_isFixed b V (c ≫ snd (schemeActionFixedScheme a) _) h

/-- The product of the attracting inclusions is attracted for the diagonal action. -/
theorem attractingProdHom_isAttracted :
    (a.prod b).IsAttracted (schemeActionAttractingHom a ⊗ₘ schemeActionAttractingHom b) := by
  rw [PointwiseSchemeAction.prod_isAttracted_iff]
  constructor
  · simpa only [tensorHom_fst] using
      PointwiseSchemeAction.IsAttracted.comp a (schemeActionAttractingHom_isAttracted a)
        (fst _ (schemeActionAttractingScheme b))
  · simpa only [tensorHom_snd] using
      PointwiseSchemeAction.IsAttracted.comp b (schemeActionAttractingHom_isAttracted b)
        (snd (schemeActionAttractingScheme a) _)

/-- The actual fixed scheme of a diagonal product is the product of the fixed schemes. -/
def schemeActionFixedProdIso : schemeActionFixedScheme (a.prod b) ≅
    schemeActionFixedScheme a ⊗ schemeActionFixedScheme b where
  hom := lift
    (schemeActionFixedMap (a.prod b) a (a.prod_isEquivariant_fst b))
    (schemeActionFixedMap (a.prod b) b (a.prod_isEquivariant_snd b))
  inv := ((exists_schemeActionFixed_factor_iff_all (a.prod b)
    (schemeActionFixedHom a ⊗ₘ schemeActionFixedHom b)).mpr (fixedProdHom_isFixed a b)).choose
  hom_inv_id := by
    apply (cancel_mono (schemeActionFixedHom (a.prod b))).mp
    rw [Category.assoc, Exists.choose_spec ((exists_schemeActionFixed_factor_iff_all
      (a.prod b) _).mpr (fixedProdHom_isFixed a b)), Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, tensorHom_fst, tensorHom_snd,
        lift_fst_assoc, lift_snd_assoc, schemeActionFixedMap_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono (schemeActionFixedHom a)).mp
      simp only [Category.assoc, lift_fst, schemeActionFixedMap_comp]
      rw [← Category.assoc, Exists.choose_spec ((exists_schemeActionFixed_factor_iff_all
        (a.prod b) _).mpr (fixedProdHom_isFixed a b))]
      simp only [tensorHom_fst, Category.id_comp]
    · apply (cancel_mono (schemeActionFixedHom b)).mp
      simp only [Category.assoc, lift_snd, schemeActionFixedMap_comp]
      rw [← Category.assoc, Exists.choose_spec ((exists_schemeActionFixed_factor_iff_all
        (a.prod b) _).mpr (fixedProdHom_isFixed a b))]
      simp only [tensorHom_snd, Category.id_comp]

/-- The fixed product comparison retains the actual inclusions. -/
theorem schemeActionFixedProdIso_hom_comp :
    (schemeActionFixedProdIso a b).hom ≫
      (schemeActionFixedHom a ⊗ₘ schemeActionFixedHom b) =
        schemeActionFixedHom (a.prod b) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, schemeActionFixedProdIso,
      lift_fst_assoc, lift_snd_assoc, schemeActionFixedMap_comp]

/-- The actual attracting scheme of a product is the product of its attracting schemes. -/
def schemeActionAttractingProdIso : schemeActionAttractingScheme (a.prod b) ≅
    schemeActionAttractingScheme a ⊗ schemeActionAttractingScheme b where
  hom := lift
    (schemeActionAttractingMap (a.prod b) a (a.prod_isEquivariant_fst b))
    (schemeActionAttractingMap (a.prod b) b (a.prod_isEquivariant_snd b))
  inv := ((exists_schemeActionAttracting_factor_iff_all (a.prod b)
    (schemeActionAttractingHom a ⊗ₘ schemeActionAttractingHom b)).mpr
      (attractingProdHom_isAttracted a b)).choose
  hom_inv_id := by
    apply (cancel_mono (schemeActionAttractingHom (a.prod b))).mp
    rw [Category.assoc, Exists.choose_spec ((exists_schemeActionAttracting_factor_iff_all
      (a.prod b) _).mpr (attractingProdHom_isAttracted a b)), Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, tensorHom_fst, tensorHom_snd,
        lift_fst_assoc, lift_snd_assoc, schemeActionAttractingMap_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono (schemeActionAttractingHom a)).mp
      simp only [Category.assoc, lift_fst, schemeActionAttractingMap_comp]
      rw [← Category.assoc, Exists.choose_spec ((exists_schemeActionAttracting_factor_iff_all
        (a.prod b) _).mpr (attractingProdHom_isAttracted a b))]
      simp only [tensorHom_fst, Category.id_comp]
    · apply (cancel_mono (schemeActionAttractingHom b)).mp
      simp only [Category.assoc, lift_snd, schemeActionAttractingMap_comp]
      rw [← Category.assoc, Exists.choose_spec ((exists_schemeActionAttracting_factor_iff_all
        (a.prod b) _).mpr (attractingProdHom_isAttracted a b))]
      simp only [tensorHom_snd, Category.id_comp]

/-- The attracting product comparison retains the actual inclusions. -/
theorem schemeActionAttractingProdIso_hom_comp :
    (schemeActionAttractingProdIso a b).hom ≫
      (schemeActionAttractingHom a ⊗ₘ schemeActionAttractingHom b) =
        schemeActionAttractingHom (a.prod b) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, schemeActionAttractingProdIso,
      lift_fst_assoc, lift_snd_assoc, schemeActionAttractingMap_comp]

end GmCoordinateAction

end Langlands.GroupScheme
