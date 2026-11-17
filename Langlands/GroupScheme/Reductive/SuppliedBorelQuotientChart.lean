import Langlands.GroupScheme.Reductive.SuppliedBorelChart
import Langlands.GroupScheme.Reductive.SuppliedAdjointTorusChart
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction

/-! # Actual supplied central quotients in Borel-adapted coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace SuppliedTorusAffineChart

variable {S U : Scheme.{u}} {T : CommGroupScheme S} {G D : GroupScheme S}
  {i : T.toGrp ⟶ G} (C : SuppliedTorusAffineChart i)

/-- The actual supplied quotient map expressed in the affine coordinates. -/
def quotientMap (q : T.toGrp ⟶ D) :
    splitTorus C.model.base C.model.coordinates ⟶ (GroupScheme.baseChange C.map).obj D :=
  CommGroupScheme.groupHom C.torusIso.hom ≫ (GroupScheme.baseChange C.map).map q

/-- The actual coordinate comparison transports the full central subgroup. -/
theorem centralKernel_eq :
    ((((center G).comap i).baseChange C.map).comap
      (CommGroupScheme.groupHom C.torusIso.hom)) =
        (center C.model.group).comap C.model.inclusion := by
  rw [SubgroupFunctor.comap_baseChange, ← center_baseChange,
    ← SubgroupFunctor.comap_comp, ← C.inclusion_eq, SubgroupFunctor.comap_comp]
  congr 1
  ext Z x
  exact mem_center_comp_iso_iff C.groupIso x

/-- The affine coordinate quotient retains its full fppf kernel. -/
theorem quotientMap_isFppfQuotient (q : T.toGrp ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient ((center G).comap i) q) :
    RelativeRoot.IsFppfQuotient ((center C.model.group).comap C.model.inclusion)
      (C.quotientMap q) := by
  have h := (hq.baseChange C.map).iso_comp (Langlands.CommGroupScheme.groupIso C.torusIso)
  simpa only [C.centralKernel_eq, quotientMap, Langlands.CommGroupScheme.groupIso] using h

/-- Identify the model pullback with the actual direct supplied group pullback. -/
def groupIsoOver (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    C.model.groupOver p ≅ (GroupScheme.baseChange r).obj G :=
  (GroupScheme.baseChange p).mapIso C.groupIso ≪≫
    Descent.pullbackComparison C.map p r hp G

/-- Identify the normalized coordinate torus with the same supplied torus
on an arbitrary scheme over the affine chart. -/
def torusIsoOver (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    splitTorus U C.model.coordinates ≅ (GroupScheme.baseChange r).obj T.toGrp :=
  (splitTorus.baseChangeIso p C.model.coordinates).symm ≪≫
    (GroupScheme.baseChange p).mapIso (Langlands.CommGroupScheme.groupIso C.torusIso) ≪≫
    Descent.pullbackComparison C.map p r hp T.toGrp

/-- The supplied inclusion square remains exact after arbitrary pullback. -/
theorem inclusion_eqOver (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    C.model.inclusionOver p ≫ (C.groupIsoOver p r hp).hom =
      (C.torusIsoOver p r hp).hom ≫ (GroupScheme.baseChange r).map i := by
  dsimp only [AffinePinnedModel.inclusionOver, BasedBorelTransport.baseChangeInclusion,
    groupIsoOver, torusIsoOver, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Langlands.CommGroupScheme.groupIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, C.inclusion_eq, Functor.map_comp, Category.assoc,
    Descent.pullbackComparison_naturality]

/-- The supplied quotient in normalized coordinates on an arbitrary scheme. -/
def quotientMapOver (q : T.toGrp ⟶ D) (p : U ⟶ C.model.base)
    (r : U ⟶ S) (hp : p ≫ C.map = r) :
    splitTorus U C.model.coordinates ⟶ (GroupScheme.baseChange r).obj D :=
  (C.torusIsoOver p r hp).hom ≫ (GroupScheme.baseChange r).map q

/-- The direct normalized quotient agrees with the iterated actual pullback. -/
theorem quotientMapOver_eq (q : T.toGrp ⟶ D) (p : U ⟶ C.model.base)
    (r : U ⟶ S) (hp : p ≫ C.map = r) :
    C.quotientMapOver q p r hp =
      (splitTorus.baseChangeIso p C.model.coordinates).inv ≫
        (GroupScheme.baseChange p).map (C.quotientMap q) ≫
        (Descent.pullbackComparison C.map p r hp D).hom := by
  dsimp only [quotientMapOver, quotientMap, torusIsoOver, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Langlands.CommGroupScheme.groupIso]
  rw [Functor.map_comp]
  simp only [Category.assoc, Descent.pullbackComparison_naturality]

/-- The direct normalized quotient is a full fppf quotient of the transported
original central subgroup on every scheme. -/
theorem quotientMapOver_isFppfQuotient (q : T.toGrp ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient ((center G).comap i) q)
    (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    RelativeRoot.IsFppfQuotient
      ((((center G).comap i).baseChange r).comap (C.torusIsoOver p r hp).hom)
      (C.quotientMapOver q p r hp) :=
  (hq.baseChange r).iso_comp (C.torusIsoOver p r hp)

variable (b : C.model.rootDatum.Base) (q : T.toGrp ⟶ D)
  (hq : RelativeRoot.IsFppfQuotient ((center G).comap i) q)

/-- The actual direct supplied quotient chart, for any chosen root base and
arbitrary scheme over the affine chart. -/
def quotientChartOver (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    (GroupScheme.baseChange r).obj D ≅ splitTorus U b.support :=
  (Descent.pullbackComparison C.map p r hp D).symm ≪≫
    C.model.adjointQuotientChartOver b (C.quotientMap q)
      (C.quotientMap_isFppfQuotient q hq) p

@[reassoc]
theorem quotientChartOver_fac (p : U ⟶ C.model.base) (r : U ⟶ S)
    (hp : p ≫ C.map = r) :
    C.quotientMapOver q p r hp ≫ (C.quotientChartOver b q hq p r hp).hom =
      splitTorus.characterProjection U (fun a : b.support => C.model.rootDatum.root a) := by
  rw [C.quotientMapOver_eq]
  simp only [quotientChartOver, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact C.model.adjointQuotientChartOver_fac b (C.quotientMap q)
    (C.quotientMap_isFppfQuotient q hq) p

end SuppliedTorusAffineChart

namespace SuppliedBorelChart

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G B D : GroupScheme S}
  {j : B ⟶ G} {t : T.toGrp ⟶ B} (C : SuppliedBorelChart j t)
  (q : T.toGrp ⟶ D) (hq : RelativeRoot.IsFppfQuotient ((center G).comap (t ≫ j)) q)

/-- The actual supplied quotient on the Borel-adapted open chart, with its
coordinates indexed by the simple roots of the supplied Borel. -/
def quotientChart : (GroupScheme.baseChange C.map).obj D ≅
    splitTorus C.space C.adapted.rootBase.support :=
  C.affine.quotientChartOver C.adapted.rootBase q hq C.adapted.projection C.map rfl

@[reassoc]
theorem quotientChart_fac :
    C.affine.quotientMapOver q C.adapted.projection C.map rfl ≫
        (C.quotientChart q hq).hom =
      splitTorus.characterProjection C.space
        (fun a : C.adapted.rootBase.support => C.affine.model.rootDatum.root a) :=
  C.affine.quotientChartOver_fac C.adapted.rootBase q hq C.adapted.projection C.map rfl

end SuppliedBorelChart

end Langlands.GroupScheme
