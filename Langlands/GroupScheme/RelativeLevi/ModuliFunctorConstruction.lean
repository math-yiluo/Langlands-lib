import Langlands.GroupScheme.RelativeLevi.ModuliConjugation

/-! # Constructing the Levi presheaf from restriction stability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P U : GroupScheme S} {M T : Over S}

/-- The actual Levi images are closed under the specified subgroup restriction.
The definition names an obligation and does not assert it. -/
def RestrictionStable (P : GroupScheme S) : Prop :=
  ∀ {M T : Over S} (a : T ⟶ M)
    (F : LeviImage ((baseChange M.hom).obj P)),
      IsLeviImage (restrictImage a F.val)

namespace LeviImage

/-- Actual subgroup restriction, restricted to Levi images when it preserves them. -/
def restrict (hstable : RestrictionStable P) (a : T ⟶ M)
    (F : LeviImage ((baseChange M.hom).obj P)) :
    LeviImage ((baseChange T.hom).obj P) :=
  ⟨restrictImage a F.val, hstable a F⟩

@[simp]
theorem restrict_val (hstable : RestrictionStable P) (a : T ⟶ M)
    (F : LeviImage ((baseChange M.hom).obj P)) :
    (F.restrict hstable a).val = restrictImage a F.val :=
  rfl

@[simp]
theorem restrict_id (hstable : RestrictionStable P)
    (F : LeviImage ((baseChange M.hom).obj P)) :
    F.restrict hstable (𝟙 M) = F :=
  ext (restrictImage_id F.val)

theorem restrict_comp (hstable : RestrictionStable P) {N : Over S}
    (a : T ⟶ M) (b : N ⟶ T) (F : LeviImage ((baseChange M.hom).obj P)) :
    (F.restrict hstable a).restrict hstable b = F.restrict hstable (b ≫ a) :=
  ext (restrictImage_comp a b F.val)

end LeviImage

/-- The actual Levi-image presheaf, given a proof of restriction stability.
This constructor retains the stability premise explicitly. -/
def moduliFunctorOfStability (hstable : RestrictionStable P) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := LeviImage ((baseChange T.unop.hom).obj P)
  map a := TypeCat.ofHom (LeviImage.restrict hstable a.unop)
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext F
    exact F.restrict_id hstable
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext F
    exact (F.restrict_comp hstable a.unop b.unop).symm

/-- Forgetting a Levi presentation embeds the constructed presheaf into the
presheaf of all actual subgroup functors. -/
def moduliInclusionOfStability (hstable : RestrictionStable P) :
    moduliFunctorOfStability hstable ⟶ subgroupPresheaf P where
  app _ := TypeCat.ofHom Subtype.val

/-- The actual points of the supplied group act by conjugation on Levi images.
This definition itself does not need restriction stability. -/
@[instance_reducible]
def leviConjugationAction (r : U ⟶ P) (T : Over S) :
    MulAction (T ⟶ U.X) (LeviImage ((baseChange T.hom).obj P)) where
  smul g F := F.conjugate (pulledBackPoint P T (g ≫ r.hom.hom))
  one_smul F := by
    apply LeviImage.ext
    change conjugateImage (pulledBackPointHom P T (1 ≫ r.hom.hom)) F.val = F.val
    rw [MonObj.one_comp, map_one, conjugateImage_one]
  mul_smul g h F := by
    apply LeviImage.ext
    change conjugateImage (pulledBackPointHom P T ((g * h) ≫ r.hom.hom)) F.val =
      conjugateImage (pulledBackPointHom P T (g ≫ r.hom.hom))
        (conjugateImage (pulledBackPointHom P T (h ≫ r.hom.hom)) F.val)
    rw [MonObj.mul_comp, map_mul, conjugateImage_mul]

/-- The Levi action commutes with restriction on every test. -/
theorem LeviImage.restrict_smul (hstable : RestrictionStable P)
    (r : U ⟶ P) (a : T ⟶ M) (g : M ⟶ U.X)
    (F : LeviImage ((baseChange M.hom).obj P)) :
    letI := leviConjugationAction r M
    letI := leviConjugationAction r T
    (g • F).restrict hstable a = (a ≫ g) • F.restrict hstable a := by
  apply LeviImage.ext
  exact restrictImage_conjugateAt a (g ≫ r.hom.hom) F.val

/-- An actual representing correspondence already supplies restriction stability,
by transporting each Levi value to its unique representing point. -/
theorem ModuliRepresentation.restrictionStable {X : Over S}
    (ρ : ModuliRepresentation P X) : RestrictionStable P := by
  intro M T a F
  have he : (ρ.pointsEquiv T (a ≫ (ρ.pointsEquiv M).symm F)).val =
      restrictImage a F.val := by
    simpa only [restrictImage, Equiv.apply_symm_apply] using
      ρ.naturality a ((ρ.pointsEquiv M).symm F)
  rw [← he]
  exact (ρ.pointsEquiv T (a ≫ (ρ.pointsEquiv M).symm F)).property

end Langlands.GroupScheme.RelativeLevi
