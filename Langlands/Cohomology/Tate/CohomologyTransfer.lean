import Langlands.Cohomology.Tate.StandardCochains
import Langlands.Cohomology.Tate.HomTransfer
import Langlands.Cohomology.Tate.HomologyTransfer

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Apply the standard-resolution comparison and then the genuine relative trace. -/
def homogeneousCochainTransferComponent (A : Rep.{u} R G) (n : ℕ) :
    ((Rep.standardComplex R H).X n ⟶ Rep.res H.subtype A) →ₗ[R]
      ((Rep.standardComplex R G).X n ⟶ A) where
  toFun f := homTransfer H ((Rep.standardComplex R G).X n) A
    (standardCosetComparisonComponent H n ≫ f)
  map_add' f g := by rw [Preadditive.comp_add, map_add]
  map_smul' r f := by rw [Linear.comp_smul, map_smul, RingHom.id_apply]

/-- Ordinary cohomological transfer on the actual homogeneous Hom complexes. -/
def homogeneousCochainTransfer (A : Rep.{u} R G) :
    (Rep.standardComplex R H).linearYonedaObj R (Rep.res H.subtype A) ⟶
      (Rep.standardComplex R G).linearYonedaObj R A where
  f n := ModuleCat.ofHom (homogeneousCochainTransferComponent H A n)
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (Rep.standardComplex R G).d (n + 1) n ≫
        homTransfer H ((Rep.standardComplex R G).X n) A
          (standardCosetComparisonComponent H n ≫ f) =
      homTransfer H ((Rep.standardComplex R G).X (n + 1)) A
        (standardCosetComparisonComponent H (n + 1) ≫
          (Rep.standardComplex R H).d (n + 1) n ≫ f)
    rw [← homTransfer_precomp]
    apply congrArg (homTransfer H ((Rep.standardComplex R G).X (n + 1)) A)
    have hc : Rep.resMap H.subtype ((Rep.standardComplex R G).d (n + 1) n) ≫
        standardCosetComparisonComponent H n =
          standardCosetComparisonComponent H (n + 1) ≫ (Rep.standardComplex R H).d (n + 1) n :=
      ((standardCosetComparison (R := R) H).comm (n + 1) n).symm
    rw [← Category.assoc, hc, Category.assoc]

/-- Independently constructed ordinary corestriction on Mathlib's inhomogeneous cochains. -/
def ordinaryCorestrictionCochainMap (A : Rep.{u} R G) :
    groupCohomology.inhomogeneousCochains (Rep.res H.subtype A) ⟶
      groupCohomology.inhomogeneousCochains A :=
  (cochainsIsoStandard (Rep.res H.subtype A)).hom ≫ homogeneousCochainTransfer H A ≫
    (cochainsIsoStandard A).inv

/-- Ordinary cohomological corestriction induced by its proved cochain map. -/
def ordinaryCohomologyCorestriction (A : Rep.{u} R G) (n : ℕ) :
    groupCohomology (Rep.res H.subtype A) n ⟶ groupCohomology A n :=
  HomologicalComplex.homologyMap (ordinaryCorestrictionCochainMap H A) n

end Langlands.Tate
