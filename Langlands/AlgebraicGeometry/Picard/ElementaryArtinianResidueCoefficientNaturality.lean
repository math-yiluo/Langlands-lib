import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianResidueCoefficient

/-! # The residue coefficient map and structure sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules

@[reassoc]
private lemma unit_pushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitToPushforwardUnit g ≫ (Scheme.Modules.pushforward g).map (unitToPushforwardUnit f) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _ = unitToPushforwardUnit (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

@[reassoc]
private lemma unit_pushforward_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    unitToPushforwardUnit f ≫ (Scheme.Modules.pushforwardCongr h).hom.app _ =
      unitToPushforwardUnit g := by
  cases h
  apply Scheme.Modules.hom_ext
  intro U
  change Scheme.Modules.Hom.app (unitToPushforwardUnit f) U ≫
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map
      (𝟙 (op (f ⁻¹ᵁ U))) =
      Scheme.Modules.Hom.app (unitToPushforwardUnit f) U
  exact (congrArg (fun k => Scheme.Modules.Hom.app (unitToPushforwardUnit f) U ≫ k)
    ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map_id _)).trans
      (Category.comp_id _)

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) [IsLocalRing S]

/-- The residue coefficient map carries structure sections along the original scheme map. -/
@[reassoc]
lemma residueCoefficient_unit {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    unitToPushforwardUnit (residueι φ X) ≫ residueCoefficient φ f =
      unitToPushforwardUnit f.left ≫
        (Scheme.Modules.pushforward f.left).map (unitToPushforwardUnit (residueι φ Y)) := by
  unfold residueCoefficient
  rw [unit_pushforward_comp_assoc, unit_pushforward_congr_assoc]
  have h := unit_pushforward_comp (residueι φ Y) f.left
  rw [← h]
  simp

/-- A residue section lifted from the original scheme maps to the residue of its pullback. -/
lemma residueCoefficient_app_lift {X Y : Over (Spec (CommRingCat.of R))}
    (f : Y ⟶ X) (U : X.left.Opens) (a : Γ(X.left, U)) :
    Scheme.Modules.Hom.app (residueCoefficient φ f) U ((residueι φ X).app U a) =
      (residueι φ Y).app (f.left ⁻¹ᵁ U) (f.left.app U a) := by
  exact congrArg
    (fun k : SheafOfModules.unit X.left.ringCatSheaf ⟶
        (Scheme.Modules.pushforward f.left).obj (residueModule φ Y) =>
      Scheme.Modules.Hom.app k U a)
    (residueCoefficient_unit φ f)

/-- Apply the residue coefficient map in every product coordinate. -/
def residueProductCoefficient (ι : Type u)
    {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    (∏ᶜ fun _ : ι => residueModule φ X) ⟶
      (Scheme.Modules.pushforward f.left).obj (∏ᶜ fun _ : ι => residueModule φ Y) :=
  Pi.lift (fun j => Pi.π (fun _ : ι => residueModule φ X) j ≫ residueCoefficient φ f) ≫
    (PreservesProduct.iso (Scheme.Modules.pushforward f.left)
      (fun _ : ι => residueModule φ Y)).inv

/-- Product coefficients retain the prescribed map in each coordinate. -/
@[reassoc]
lemma residueProductCoefficient_π (ι : Type u)
    {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) (j : ι) :
    residueProductCoefficient φ ι f ≫
        (Scheme.Modules.pushforward f.left).map (Pi.π (fun _ : ι => residueModule φ Y) j) =
      Pi.π (fun _ : ι => residueModule φ X) j ≫ residueCoefficient φ f := by
  unfold residueProductCoefficient
  rw [Category.assoc]
  have h :
      (PreservesProduct.iso (Scheme.Modules.pushforward f.left)
        (fun _ : ι => residueModule φ Y)).inv ≫
          (Scheme.Modules.pushforward f.left).map (Pi.π (fun _ : ι => residueModule φ Y) j) =
        Pi.π (fun _ : ι => (Scheme.Modules.pushforward f.left).obj (residueModule φ Y)) j := by
    apply (Iso.inv_comp_eq _).mpr
    exact (piComparison_comp_π (Scheme.Modules.pushforward f.left)
      (fun _ : ι => residueModule φ Y) j).symm
  rw [h, Pi.lift_comp_π]

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
