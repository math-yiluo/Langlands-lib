import Langlands.Geometry.EtaleTransportAffine
import Langlands.Geometry.EtaleTransportSections
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Sheafification and injectives for actual small-etale transport sheaves -/

noncomputable section

universe u w uA

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ) [Small.{u} G]

section ConcreteCoefficients

variable (A : Type uA) [Category.{u} A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Z, FunLike (FA X Z) (CA X) (CA Z)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Sheafify on the essentially small actual affine transport basis. -/
instance affineBasis_hasSheafify : HasSheafify (affineBasisTopology ρ) A :=
  hasSheafifyEssentiallySmallSite _ _

/-- The affine small-model comparison uses only essentially `u`-small limits. -/
instance affineBasis_smallModel_structuredArrow_hasLimits (X : (AffineBasis ρ)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow X (equivSmallModel (AffineBasis ρ)).inverse.op) A :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Transfer genuine left-exact sheafification to the full transport site. -/
instance transport_hasSheafify : HasSheafify (transportTopology ρ) A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (affineBasisTopology ρ) (transportTopology ρ) (affineBasisInclusion ρ)

/-- Actual transport sheafification of arbitrary presheaves. -/
def sheafify : ((Object ρ)ᵒᵖ ⥤ A) ⥤ Sheaf ρ A :=
  presheafToSheaf (transportTopology ρ) A

/-- The sheafification universal property is a constructed adjunction. -/
def sheafifyAdjunction :
    sheafify ρ A ⊣ sheafToPresheaf (transportTopology ρ) A :=
  sheafificationAdjunction (transportTopology ρ) A

instance sheafify_preservesFiniteLimits :
    PreservesFiniteLimits (sheafify ρ A) :=
  inferInstanceAs (PreservesFiniteLimits
    (presheafToSheaf (transportTopology ρ) A))

instance affineBasisSheaf_abelian [Abelian A] :
    Abelian (CategoryTheory.Sheaf (affineBasisTopology ρ) A) := inferInstance

instance transportSheaf_abelian [Abelian A] :
    Abelian (Sheaf ρ A) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf (transportTopology ρ) A))

instance sheafify_additive [Abelian A] : (sheafify ρ A).Additive :=
  inferInstanceAs (presheafToSheaf (transportTopology ρ) A).Additive

instance affineBasisSheaf_isGrothendieckAbelian
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (CategoryTheory.Sheaf (affineBasisTopology ρ) A) :=
  CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance transportSheaf_isGrothendieckAbelian
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf ρ A) :=
  IsGrothendieckAbelian.of_equivalence (affineBasisSheafEquiv ρ A)

instance transportSheaf_enoughInjectives
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    EnoughInjectives (Sheaf ρ A) := inferInstance

end ConcreteCoefficients

section Modules

variable (R : Type u) [CommRing R]

/-- Module transport sheaves have enough injectives in the scheme universe. -/
instance moduleSheaf_enoughInjectives :
    EnoughInjectives (ModuleSheaf.{u, w, u, u} ρ R) := inferInstance

/-- A constructed injective resolution in the actual equivariant sheaf category. -/
def moduleSheafInjectiveResolution (F : ModuleSheaf.{u, w, u, u} ρ R) :
    InjectiveResolution F :=
  injectiveResolution F

end Modules

end Langlands.Geometry.EtaleTransport
