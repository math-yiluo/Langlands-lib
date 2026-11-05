import Langlands.GroupScheme.Lie.FiniteAction
import Langlands.GroupScheme.MultiplicativePointTopology

/-! # Characters reconstructed from natural affine unit values -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCharacterNaturalValues

open AffineCoordinates

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F]
variable (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
variable (α : ∀ A : CommAlgCat.{u} F, H.affinePoints A →* Aˣ)
variable (hα : ∀ {A B : CommAlgCat.{u} F} (f : A ⟶ B) (y : H.affinePoints A),
  α B (H.affinePointMap f y) = Units.map f.hom.toMonoidHom (α A y))

abbrev M := (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp

local instance gm_isAffine : IsAffine (M (F := F)).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (Gm.toSpecZ (Spec (CommRingCat.of F))))
  infer_instance

/-- The natural unit values in the corepresented source and target coordinates. -/
def coordinateApp (A : CommAlgCat.{u} F) :
    (functor H).obj A →* (functor (M (F := F))).obj A :=
  (actualPointsEquiv (M (F := F)) A).symm.toMonoidHom.comp
    ((Gm.affineUnitsEquiv (CommRingCat.of F) A).symm.toMonoidHom.comp
      ((α A).comp (actualPointsEquiv H A).toMonoidHom))

@[simp] theorem coordinateApp_values (A : CommAlgCat.{u} F)
    (x : (functor H).obj A) :
    Gm.affineUnitsEquiv (CommRingCat.of F) A
      (actualPointsEquiv (M (F := F)) A (coordinateApp H α A x)) =
      α A (actualPointsEquiv H A x) := by
  simp [coordinateApp]

/-- A natural transformation of the corepresented group functors. -/
def coordinateNat : functor H ⟶ functor (M (F := F)) where
  app A := GrpCat.ofHom (coordinateApp H α A)
  naturality {A B} f := by
    ext x
    apply (actualPointsEquiv (M (F := F)) B).injective
    apply (Gm.affineUnitsEquiv (CommRingCat.of F) B).injective
    change Gm.affineUnitsEquiv (CommRingCat.of F) B
        (actualPointsEquiv (M (F := F)) B
          (coordinateApp H α B ((functor H).map f x))) =
      Gm.affineUnitsEquiv (CommRingCat.of F) B
        (actualPointsEquiv (M (F := F)) B
          ((functor (M (F := F))).map f (coordinateApp H α A x)))
    rw [coordinateApp_values, actualPointsEquiv_naturality,
      actualPointsEquiv_naturality, Gm.affineUnitsEquiv_naturality,
      coordinateApp_values]
    exact hα f _

/-- The character associated to the natural family of homomorphisms into units. -/
def character : rationalCharacters H :=
  Additive.ofMul ((groupSchemeIso H).inv ≫
    Corepresented.groupSchemeMap (corepresentation H) (corepresentation (M (F := F)))
      (coordinateNat H α hα) ≫ (groupSchemeIso (M (F := F))).hom)

theorem actualPointsEquiv_affinePointsEquiv
    (A : CommAlgCat.{u} F)
    (x : (Corepresented.groupScheme (functor H) (corepresentation H)).affinePoints A) :
    actualPointsEquiv H A
      (Corepresented.affinePointsEquiv _ (corepresentation H) A x) =
      x ≫ (groupSchemeIso H).hom.hom.hom := by
  change (Corepresented.affinePointsEquiv _ (corepresentation H) A).symm
    (Corepresented.affinePointsEquiv _ (corepresentation H) A x) ≫ _ = _
  rw [MulEquiv.symm_apply_apply]

/-- The reconstructed character has the prescribed values on every affine algebra. -/
theorem character_values (A : CommAlgCat.{u} F) (y : H.affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of F) A
      (y ≫ (character H α hα).toMul.hom.hom) = α A y := by
  have h := Corepresented.groupSchemeMap_affinePoints
    (corepresentation H) (corepresentation (M (F := F))) (coordinateNat H α hα)
    (y ≫ (groupSchemeIso H).inv.hom.hom)
  have h' := congrArg (fun z => Gm.affineUnitsEquiv (CommRingCat.of F) A
    (actualPointsEquiv (M (F := F)) A z)) h
  change _ = Gm.affineUnitsEquiv (CommRingCat.of F) A
    (actualPointsEquiv (M (F := F)) A
      (coordinateApp H α A
        (Corepresented.affinePointsEquiv _ (corepresentation H) A
          (y ≫ (groupSchemeIso H).inv.hom.hom)))) at h'
  rw [coordinateApp_values, actualPointsEquiv_affinePointsEquiv,
    actualPointsEquiv_affinePointsEquiv] at h'
  simpa only [character, toMul_ofMul, Grp.comp_hom_hom, Category.assoc,
    ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using h'

end Langlands.GroupScheme.AffineCharacterNaturalValues
