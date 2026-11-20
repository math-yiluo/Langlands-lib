import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction.Conditional
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof

/-! # Ordinary restriction on the analytic étale site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uA vA

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- An actual open analytic domain, regarded as an object of the étale site. -/
def openEtaleObject (U : Opens (localizedSpaceFunctor.obj X)) : EtaleSite X :=
  OpenEtaleRestriction.openEtaleObject X (etaleOpenDomainStatement X) U

/-- A morphism into an open domain is determined by its map to the base. -/
instance openEtaleObject_hom_subsingleton (W : EtaleSite X)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    Subsingleton (W ⟶ openEtaleObject X U) :=
  OpenEtaleRestriction.openEtaleObject_hom_subsingleton X (etaleOpenDomainStatement X) W U

/-- Factor an actual étale object through an open domain containing its image. -/
def openEtaleLift (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X)
    (hW : ∀ y, localizedSpaceFunctor.map W.hom y ∈ U) :
    W ⟶ openEtaleObject X U :=
  OpenEtaleRestriction.openEtaleLift X (etaleOpenDomainStatement X) U W hW

/-- Every map to the open-domain object has image in that open. -/
theorem mem_open_of_openEtale_hom {U : Opens (localizedSpaceFunctor.obj X)}
    {W : EtaleSite X} (f : W ⟶ openEtaleObject X U)
    (y : localizedSpaceFunctor.obj W.left) :
    localizedSpaceFunctor.map W.hom y ∈ U :=
  OpenEtaleRestriction.mem_open_of_openEtale_hom X (etaleOpenDomainStatement X) f y

/-- Inclusion of open sets is the canonical factorization of domain inclusions. -/
def openEtaleMap {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V) :
    openEtaleObject X U ⟶ openEtaleObject X V :=
  OpenEtaleRestriction.openEtaleMap X (etaleOpenDomainStatement X) f

/-- The actual ordinary-open site maps into the actual étale site. -/
def openEtaleFunctor : Opens (localizedSpaceFunctor.obj X) ⥤ EtaleSite X :=
  OpenEtaleRestriction.openEtaleFunctor X (etaleOpenDomainStatement X)

/-- The map between two open-domain spaces retains the ambient point. -/
theorem openEtaleMap_apply_val {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V)
    (y : localizedSpaceFunctor.obj (openEtaleObject X U).left) :
    (localizedSpaceFunctor.map (openEtaleMap X f).left y).val = y.val :=
  OpenEtaleRestriction.openEtaleMap_apply_val X (etaleOpenDomainStatement X) f y

/-- Images of actual opens preserve finite cones of maps from every étale object. -/
instance openEtaleFunctor_representablyFlat : RepresentablyFlat (openEtaleFunctor X) :=
  OpenEtaleRestriction.openEtaleFunctor_representablyFlat X (etaleOpenDomainStatement X)

/-- A covering family of ordinary opens jointly covers their actual domain spaces. -/
theorem openEtaleFunctor_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
      (etaleTopology X) (openEtaleFunctor X) :=
  OpenEtaleRestriction.openEtaleFunctor_coverPreserving X (etaleOpenDomainStatement X)

/-- Precomposition with canonical open domains takes actual étale sheaves to sheaves. -/
instance openEtaleFunctor_isContinuous :
    (openEtaleFunctor X).IsContinuous
      (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X) :=
  OpenEtaleRestriction.openEtaleFunctor_isContinuous X (etaleOpenDomainStatement X)

variable (A : Type uA) [Category.{vA} A]

/-- The actual étale sheaf restricted to the ordinary underlying topology. -/
def etaleUnderlyingSheaf :
    Sheaf (etaleTopology X) A ⥤ TopCat.Sheaf A (localizedSpaceFunctor.obj X) :=
  OpenEtaleRestriction.etaleUnderlyingSheaf X (etaleOpenDomainStatement X) A

/-- The ordinary-open sections are the original sections over the actual analytic domain. -/
theorem etaleUnderlyingSheaf_obj_obj (F : Sheaf (etaleTopology X) A)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    ((etaleUnderlyingSheaf X A).obj F).obj.obj (op U) =
      F.obj.obj (op (openEtaleObject X U)) := rfl

/-- Ordinary restrictions evaluate the original étale presheaf on the domain factorization. -/
theorem etaleUnderlyingSheaf_obj_map (F : Sheaf (etaleTopology X) A)
    {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V) :
    ((etaleUnderlyingSheaf X A).obj F).obj.map f.op =
      F.obj.map (openEtaleMap X f).op := rfl

end Langlands.Sheaf.Equivariant.Analytic
