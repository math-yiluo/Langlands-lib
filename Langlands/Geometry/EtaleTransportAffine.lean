import Langlands.Geometry.EtaleTransportSite
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-! # An affine basis for the actual small-etale transport site -/

noncomputable section

universe u w uA vA

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The actual affine etale scheme represented by a small affine-site object. -/
def affineBasisObject (U : SmallModel.{u} Y.AffineEtale) : Object ρ :=
  ⟨(Scheme.AffineEtale.Spec Y).obj ((equivSmallModel.{u} Y.AffineEtale).inverse.obj U)⟩

/-- Small affine representatives with all genuine labelled scheme morphisms. -/
def AffineBasis : Type u :=
  InducedCategory (Object ρ) (affineBasisObject ρ)

instance : Category (AffineBasis ρ) :=
  inferInstanceAs (Category (InducedCategory (Object ρ) (affineBasisObject ρ)))

/-- Include each actual affine representative and its complete labelled morphisms. -/
def affineBasisInclusion : AffineBasis ρ ⥤ Object ρ :=
  inducedFunctor (affineBasisObject ρ)

instance : (affineBasisInclusion ρ).Full :=
  inferInstanceAs (inducedFunctor (affineBasisObject ρ)).Full

instance : (affineBasisInclusion ρ).Faithful :=
  inferInstanceAs (inducedFunctor (affineBasisObject ρ)).Faithful

/-- Ordinary affine covers still cover after keeping all transport labels. -/
instance affineBasisInclusion_isCoverDense :
    (affineBasisInclusion ρ).IsCoverDense (transportTopology ρ) where
  is_cover U := by
    apply Y.smallEtaleTopology.superset_covering ?_
      (Functor.is_cover_of_isCoverDense (Scheme.AffineEtale.Spec Y)
        Y.smallEtaleTopology U.etale)
    intro V f hf
    obtain ⟨⟨W, l, m, h⟩⟩ := hf
    let e := equivSmallModel.{u} Y.AffineEtale
    let a := (Scheme.AffineEtale.Spec Y).mapIso (e.unitIso.app W).symm
    change Nonempty (Presieve.CoverByImageStructure (affineBasisInclusion ρ)
      ((inclusion ρ).map f))
    refine ⟨⟨e.functor.obj W, (inclusion ρ).map (l ≫ a.inv),
      (inclusion ρ).map (a.hom ≫ m), ?_⟩⟩
    rw [← Functor.map_comp]
    congr 1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The induced covering-sieve topology on the actual affine basis. -/
def affineBasisTopology : GrothendieckTopology (AffineBasis ρ) :=
  (affineBasisInclusion ρ).inducedTopology (transportTopology ρ)

instance affineBasisInclusion_isDenseSubsite :
    (affineBasisInclusion ρ).IsDenseSubsite
      (affineBasisTopology ρ) (transportTopology ρ) := by
  dsimp [affineBasisTopology]
  infer_instance

section SmallGroup

variable [Small.{u} G]

/-- Both group labels and actual scheme maps form a small set of morphisms. -/
instance object_locallySmall : LocallySmall.{u} (Object ρ) where
  hom_small U V :=
    small_of_injective (f := fun f : U ⟶ V => (f.label, f.left))
      (fun _ _ h => Object.Hom.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

instance affineBasis_locallySmall : LocallySmall.{u} (AffineBasis ρ) :=
  locallySmall_of_faithful (affineBasisInclusion ρ)

instance affineBasis_essentiallySmall : EssentiallySmall.{u} (AffineBasis ρ) :=
  essentiallySmall_of_small_of_locallySmall _

variable (A : Type uA) [Category.{vA} A] [HasLimitsOfSize.{u, u} A]

/-- The right Kan extension only uses limits over essentially small comma categories. -/
instance affineBasis_structuredArrow_hasLimits (X : (Object ρ)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (affineBasisInclusion ρ).op) A :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

instance affineBasis_restriction_isEquivalence :
    ((affineBasisInclusion ρ).sheafPushforwardContinuous A
      (affineBasisTopology ρ) (transportTopology ρ)).IsEquivalence :=
  inferInstance

/-- Sheaves on the actual affine transport basis recover all transport sheaves. -/
def affineBasisSheafEquiv :
    CategoryTheory.Sheaf (affineBasisTopology ρ) A ≌ Sheaf ρ A :=
  ((affineBasisInclusion ρ).sheafPushforwardContinuous A
    (affineBasisTopology ρ) (transportTopology ρ)).asEquivalence.symm

end SmallGroup

end Langlands.Geometry.EtaleTransport
