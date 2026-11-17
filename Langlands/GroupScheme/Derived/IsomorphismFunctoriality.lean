import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.RepresentedSubgroupTransport

/-! # Induced isomorphisms of actual derived subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IsDerivedSubgroup

variable {S : Scheme.{u}} {G H D E : GroupScheme S}
  {d : D ⟶ G} {e : E ⟶ H}

/-- An ambient isomorphism induces an actual isomorphism between supplied
representatives of the full derived subgroups. -/
def mapIso (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e)
    (f : G ≅ H) : D ≅ E :=
  hd.isRepresentedBy.isoOfComap he.isRepresentedBy f (derivedSubgroup_comap_iso f)

/-- The induced forward isomorphism commutes with the actual inclusions. -/
@[reassoc]
theorem mapIso_hom_comp (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e)
    (f : G ≅ H) :
    (hd.mapIso he f).hom ≫ e = d ≫ f.hom :=
  hd.isRepresentedBy.isoOfComap_hom_comp he.isRepresentedBy f
    (derivedSubgroup_comap_iso f)

/-- The induced inverse isomorphism commutes with the actual inclusions. -/
@[reassoc]
theorem mapIso_inv_comp (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e)
    (f : G ≅ H) :
    (hd.mapIso he f).inv ≫ d = e ≫ f.inv :=
  hd.isRepresentedBy.isoOfComap_inv_comp he.isRepresentedBy f
    (derivedSubgroup_comap_iso f)

/-- The forward map is the previously defined derived-subgroup map. -/
theorem mapIso_hom_eq_map (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e)
    (f : G ≅ H) :
    (hd.mapIso he f).hom = hd.map he f.hom :=
  he.isRepresentedBy.hom_ext
    ((hd.mapIso_hom_comp he f).trans (hd.map_comp he f.hom).symm)

/-- The inclusion square uniquely determines the induced isomorphism. -/
theorem mapIso_unique (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e)
    (f : G ≅ H) (q : D ≅ E) (hq : q.hom ≫ e = d ≫ f.hom) :
    q = hd.mapIso he f := by
  apply Iso.ext
  exact he.isRepresentedBy.hom_ext (hq.trans (hd.mapIso_hom_comp he f).symm)

end Langlands.GroupScheme.IsDerivedSubgroup
