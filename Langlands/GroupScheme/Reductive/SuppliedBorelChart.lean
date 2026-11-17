import Langlands.GroupScheme.Reductive.SuppliedTorusAffineModel
import Langlands.GroupScheme.Reductive.BorelAdaptedRootBase
import Langlands.GroupScheme.RelativeLevi.BorelTransport

/-! # Open charts adapted to the supplied Borel and maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace SuppliedTorusAffineChart

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G B : GroupScheme S}
  {i : T.toGrp ⟶ G} (C : SuppliedTorusAffineChart i)

/-- The actual supplied Borel inclusion expressed in the affine model. -/
def borelInclusion (j : B ⟶ G) :
    (GroupScheme.baseChange C.map).obj B ⟶ C.model.group :=
  (GroupScheme.baseChange C.map).map j ≫ C.groupIso.inv

/-- Pullback and the actual ambient comparison preserve the relative Borel. -/
theorem isRelativeBorel_borelInclusion (j : B ⟶ G)
    (hG : IsReductive G) (hj : IsRelativeBorelSubgroup j) :
    IsRelativeBorelSubgroup (C.borelInclusion j) :=
  (hj.baseChange hG C.map).comp_iso C.groupIso.symm

/-- The supplied torus remains contained in the supplied Borel inside the
model, as an exact factorization of actual group-scheme homomorphisms. -/
theorem torus_le_borelInclusion (j : B ⟶ G) (t : T.toGrp ⟶ B)
    (C : SuppliedTorusAffineChart (t ≫ j)) :
    SubgroupFunctor.range C.model.inclusion ≤ SubgroupFunctor.range (C.borelInclusion j) := by
  have hf : C.model.inclusion =
      (CommGroupScheme.groupHom C.torusIso.hom ≫ (GroupScheme.baseChange C.map).map t) ≫
        C.borelInclusion j := by
    apply (cancel_mono C.groupIso.hom).mp
    simpa only [borelInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Functor.map_comp] using C.inclusion_eq
  rw [hf]
  exact SubgroupFunctor.range_comp_le _ _

end SuppliedTorusAffineChart

/-- A supplied-torus affine model and an open restriction whose regular
exponent and root base present the actual supplied Borel. -/
structure SuppliedBorelChart {S : Scheme.{u}} {T : CommGroupScheme S}
    {G B : GroupScheme S} (j : B ⟶ G) (t : T.toGrp ⟶ B) where
  affine : SuppliedTorusAffineChart (t ≫ j)
  point : affine.model.base
  adapted : AffineRegularBorel.AdaptedBorelRootBaseData affine.model.inclusion
    (affine.borelInclusion j) affine.model.rootDatum point

namespace SuppliedBorelChart

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G B : GroupScheme S}
  {j : B ⟶ G} {t : T.toGrp ⟶ B} (C : SuppliedBorelChart j t)

/-- The final chart scheme may be an arbitrary open of the affine model. -/
abbrev space : Scheme.{u} := C.adapted.neighbourhood

/-- The actual chart morphism to the original base. -/
def map : C.space ⟶ S := C.adapted.projection ≫ C.affine.map

instance : IsOpenImmersion C.adapted.projection := C.adapted.openImmersion
instance : Etale C.affine.map := C.affine.etale
instance : Etale C.map := by
  dsimp [map]
  infer_instance

/-- Every base point is covered by a chart adapted to the actual supplied
Borel and actual supplied maximal torus. -/
theorem exists_over (j : B ⟶ G) (t : T.toGrp ⟶ B)
    (hG : IsReductive G) (hj : IsRelativeBorelSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup (t ≫ j))
    (hmax : IsFibrewiseMaximalTorus (T := T) (t ≫ j)) (s : S) :
    ∃ C : SuppliedBorelChart j t, s ∈ Set.range C.map := by
  obtain ⟨A, x, hx⟩ := SuppliedTorusAffineChart.exists_over (t ≫ j) hG hT ht hmax s
  let d := AffineRegularBorel.adaptedBorelRootBase A.model.inclusion (A.borelInclusion j)
    A.model.rootDatum A.model.fibrewiseRootDatum A.model.reductive A.model.closed
    A.model.maximal (A.isRelativeBorel_borelInclusion j hG hj)
    (SuppliedTorusAffineChart.torus_le_borelInclusion j t A) x
  let C : SuppliedBorelChart j t := ⟨A, x, d⟩
  obtain ⟨y, hy⟩ := d.contains
  exact ⟨C, y, (congrArg A.map hy).trans hx⟩

end SuppliedBorelChart

end Langlands.GroupScheme
