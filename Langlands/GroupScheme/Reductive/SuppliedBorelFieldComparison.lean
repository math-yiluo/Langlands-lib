import Langlands.GroupScheme.Reductive.SuppliedBorelQuotientChart
import Langlands.GroupScheme.Reductive.BorelAdjointChartComparison
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Actual field comparisons between supplied Borel charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- A model's actual full root datum realizes its coordinate inclusion on
any supplied field-valued point, with its original coefficient map. -/
theorem rootDatum_fieldPoint {k : Type u} [Field k]
    (p : Spec (CommRingCat.of k) ⟶ M.base) :
    letI := (M.reductive.isConnectedReductive_baseChange p).isAffineHom
    IsRootDatumOf (T := splitTorus.commGroupScheme _ M.coordinates)
      (M.inclusionOver p) (CoordinateRootDatum.fieldRealization k M.rootDatum) := by
  let φ := Spec.preimage p
  let : Algebra M.ring k := φ.hom.toAlgebra
  have hp : algebraBaseMap M.ring k = p := Spec.map_preimage p
  have h := M.fibrewiseRootDatum.field k
  change IsRootDatumOf (T := splitTorus.commGroupScheme _ M.coordinates)
    ((splitTorus.baseChangeIso (algebraBaseMap M.ring k) M.coordinates).inv ≫
      (GroupScheme.baseChange (algebraBaseMap M.ring k)).map M.inclusion) _ at h
  rwa [hp] at h

/-- The normalized coordinate inclusion remains maximal on every supplied
field-valued point. -/
theorem maximal_fieldPoint {k : Type u} [Field k]
    (p : Spec (CommRingCat.of k) ⟶ M.base) :
    IsMaximalTorus (T := splitTorus.commGroupScheme _ M.coordinates) (M.inclusionOver p) := by
  let := M.reductive.smooth
  exact IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange p).obj (splitTorus.commGroupScheme M.base M.coordinates))
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (splitTorus.baseChangeIso p M.coordinates).symm (M.maximal.fieldPoint p)

/-- Fixed integer exponents retain their normalized coordinates on every
scheme over a model. -/
theorem exponentCocharacterOver_eq {U : Scheme.{u}} (p : U ⟶ M.base)
    (n : M.coordinates → ℤ) :
    Dynamic.baseChangeCocharacter p (AffineRegularBorel.cocharacter M.inclusion n) =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter U M.coordinates n) ≫
        M.inclusionOver p := by
  rw [AffineRegularBorel.cocharacter, Dynamic.baseChangeCocharacter_comp,
    ← splitTorus.groupHom_exponentCocharacter_baseChange M.base M.coordinates p n]
  simp only [inclusionOver, BasedBorelTransport.baseChangeInclusion,
    Category.assoc, Iso.hom_inv_id_assoc]

end AffinePinnedModel

namespace SuppliedTorusAffineChart

variable {S U : Scheme.{u}} {T : CommGroupScheme S} {G B : GroupScheme S}
  {i : T.toGrp ⟶ G} (C : SuppliedTorusAffineChart i)

/-- The actual supplied Borel square on an arbitrary common pullback. -/
theorem borelInclusionOver_comp (j : B ⟶ G)
    (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    (GroupScheme.baseChange p).map (C.borelInclusion j) ≫ (C.groupIsoOver p r hp).hom =
      (Descent.pullbackComparison C.map p r hp B).hom ≫ (GroupScheme.baseChange r).map j := by
  simp only [borelInclusion, groupIsoOver, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  exact Descent.pullbackComparison_naturality C.map p r hp j

/-- The model's pulled-back Borel has exactly the original supplied Borel
range under its actual ambient identification. -/
theorem range_borelInclusionOver_comp (j : B ⟶ G)
    (p : U ⟶ C.model.base) (r : U ⟶ S) (hp : p ≫ C.map = r) :
    SubgroupFunctor.range
      ((GroupScheme.baseChange p).map (C.borelInclusion j) ≫ (C.groupIsoOver p r hp).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange r).map j) := by
  rw [C.borelInclusionOver_comp]
  exact SubgroupFunctor.range_iso_comp (Descent.pullbackComparison C.map p r hp B) _

end SuppliedTorusAffineChart

namespace SuppliedBorelChart

variable {S U : Scheme.{u}} {T : CommGroupScheme S} {G B : GroupScheme S}
  {j : B ⟶ G} {t : T.toGrp ⟶ B} (C C' : SuppliedBorelChart j t)

/-- The same fixed exponent presents the actual Borel after every further
pullback of its open chart. -/
theorem borelPresentationOver (a : U ⟶ C.space) :
    SubgroupFunctor.range ((GroupScheme.baseChange (a ≫ C.adapted.projection)).map
      (C.affine.borelInclusion j)) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (a ≫ C.adapted.projection)
        (AffineRegularBorel.cocharacter C.affine.model.inclusion C.adapted.exponent)) := by
  have h := Dynamic.pullbackCocharacter_presents C.adapted.projection a
    (a ≫ C.adapted.projection) rfl (C.affine.borelInclusion j)
    (Dynamic.baseChangeCocharacter C.adapted.projection
      (AffineRegularBorel.cocharacter C.affine.model.inclusion C.adapted.exponent))
    C.adapted.presentation
  simpa only [Dynamic.pullbackCocharacter, Dynamic.baseChangeCocharacter_tower] using h

/-- Compare actual ambient model pullbacks through their common supplied group. -/
def groupComparison (a : U ⟶ C.space) (a' : U ⟶ C'.space)
    (r : U ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    C.affine.model.groupOver (a ≫ C.adapted.projection) ≅
      C'.affine.model.groupOver (a' ≫ C'.adapted.projection) :=
  C.affine.groupIsoOver _ r ((Category.assoc _ _ _).trans ha) ≪≫
    (C'.affine.groupIsoOver _ r ((Category.assoc _ _ _).trans ha')).symm

/-- The actual coordinate-torus comparison uses the same original supplied torus. -/
def torusComparison (a : U ⟶ C.space) (a' : U ⟶ C'.space)
    (r : U ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    splitTorus U C.affine.model.coordinates ≅ splitTorus U C'.affine.model.coordinates :=
  C.affine.torusIsoOver _ r ((Category.assoc _ _ _).trans ha) ≪≫
    (C'.affine.torusIsoOver _ r ((Category.assoc _ _ _).trans ha')).symm

/-- The actual ambient and torus comparisons preserve the supplied inclusion. -/
theorem comparison_square (a : U ⟶ C.space) (a' : U ⟶ C'.space)
    (r : U ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    C.affine.model.inclusionOver (a ≫ C.adapted.projection) ≫
        (C.groupComparison C' a a' r ha ha').hom =
      (C.torusComparison C' a a' r ha ha').hom ≫
        C'.affine.model.inclusionOver (a' ≫ C'.adapted.projection) := by
  apply (cancel_mono (C'.affine.groupIsoOver (a' ≫ C'.adapted.projection) r
    ((Category.assoc _ _ _).trans ha')).hom).mp
  simp only [groupComparison, torusComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [C'.affine.inclusion_eqOver]
  simp only [Iso.inv_hom_id_assoc]
  exact C.affine.inclusion_eqOver _ r ((Category.assoc _ _ _).trans ha)

/-- The two dynamic parabolics agree under the actual ambient comparison
because they are both the original supplied Borel on this common scheme. -/
theorem comparison_parabolic (a : U ⟶ C.space) (a' : U ⟶ C'.space)
    (r : U ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    (Dynamic.parabolic (Dynamic.baseChangeCocharacter (a ≫ C.adapted.projection)
      (AffineRegularBorel.cocharacter C.affine.model.inclusion C.adapted.exponent))).comap
        (C.groupComparison C' a a' r ha ha').inv =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (a' ≫ C'.adapted.projection)
        (AffineRegularBorel.cocharacter C'.affine.model.inclusion C'.adapted.exponent)) := by
  rw [← C.borelPresentationOver a, ← C'.borelPresentationOver a',
    ← SubgroupFunctor.range_comp_iso]
  apply (SubgroupFunctor.range_comp_iso_eq_iff _ _
    (C'.affine.groupIsoOver (a' ≫ C'.adapted.projection) r
      ((Category.assoc _ _ _).trans ha'))).mp
  simp only [groupComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact (C.affine.range_borelInclusionOver_comp j _ r ((Category.assoc _ _ _).trans ha)).trans
    (C'.affine.range_borelInclusionOver_comp j _ r ((Category.assoc _ _ _).trans ha')).symm

/-- Every actual common field-valued pullback of two supplied Borel charts
has the full based coordinate comparison, including all-test characters. -/
def basedComparison {k : Type u} [Field k]
    (a : Spec (CommRingCat.of k) ⟶ C.space) (a' : Spec (CommRingCat.of k) ⟶ C'.space)
    (r : Spec (CommRingCat.of k) ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    BasedCoordinateIso
      (C.affine.model.inclusionOver (a ≫ C.adapted.projection))
      (C'.affine.model.inclusionOver (a' ≫ C'.adapted.projection))
      C.affine.model.rootDatum C'.affine.model.rootDatum C.adapted.rootBase C'.adapted.rootBase :=
  basedCoordinateIsoOfBorelCompatibleFieldIso
    (C.affine.model.reductive.isConnectedReductive_baseChange _)
    (C'.affine.model.reductive.isConnectedReductive_baseChange _)
    (C.affine.model.maximal_fieldPoint _) (C'.affine.model.maximal_fieldPoint _)
    C.adapted.rootBase C'.adapted.rootBase (C.groupComparison C' a a' r ha ha')
    (CommGroupScheme.isoOfGroupIso (C.torusComparison C' a a' r ha ha'))
    (C.comparison_square C' a a' r ha ha')
    (C.affine.model.rootDatum_fieldPoint _) (C'.affine.model.rootDatum_fieldPoint _)
    C.adapted.exponent C'.adapted.exponent C.adapted.regular C'.adapted.regular
    C.adapted.positive_iff C'.adapted.positive_iff (by
      simpa only [C.affine.model.exponentCocharacterOver_eq,
        C'.affine.model.exponentCocharacterOver_eq] using C.comparison_parabolic C' a a' r ha ha')

variable {D : GroupScheme S} (q : T.toGrp ⟶ D)
  (hq : RelativeRoot.IsFppfQuotient ((center G).comap (t ≫ j)) q)

/-- The actual based comparison intertwines the two normalized maps to the
same supplied quotient on a common field-valued pullback. -/
theorem basedComparison_quotient_square {k : Type u} [Field k]
    (a : Spec (CommRingCat.of k) ⟶ C.space) (a' : Spec (CommRingCat.of k) ⟶ C'.space)
    (r : Spec (CommRingCat.of k) ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    C.affine.quotientMapOver q (a ≫ C.adapted.projection) r
        ((Category.assoc _ _ _).trans ha) =
      (C.basedComparison C' a a' r ha ha').torusIso.hom ≫
        C'.affine.quotientMapOver q (a' ≫ C'.adapted.projection) r
          ((Category.assoc _ _ _).trans ha') := by
  change C.affine.quotientMapOver q _ r _ =
    (C.torusComparison C' a a' r ha ha').hom ≫ C'.affine.quotientMapOver q _ r _
  simp only [SuppliedTorusAffineChart.quotientMapOver, torusComparison,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- The actual supplied quotient transition on each common field point
is the simple-root coordinate permutation derived from its Borel data. -/
theorem quotientChartOver_field_transition {k : Type u} [Field k]
    (a : Spec (CommRingCat.of k) ⟶ C.space) (a' : Spec (CommRingCat.of k) ⟶ C'.space)
    (r : Spec (CommRingCat.of k) ⟶ S) (ha : a ≫ C.map = r) (ha' : a' ≫ C'.map = r) :
    (C.affine.quotientChartOver C.adapted.rootBase q hq (a ≫ C.adapted.projection)
        r ((Category.assoc _ _ _).trans ha)).inv ≫
      (C'.affine.quotientChartOver C'.adapted.rootBase q hq (a' ≫ C'.adapted.projection)
        r ((Category.assoc _ _ _).trans ha')).hom =
      (splitTorus.coordinatePermutationIso _ (C.basedComparison C' a a' r ha ha').simpleRootEquiv).hom := by
  have h := (C.basedComparison C' a a' r ha ha').quotientChart_transition
    (C.affine.quotientMapOver_isFppfQuotient q hq (a ≫ C.adapted.projection)
      r ((Category.assoc _ _ _).trans ha))
    (𝟙 _) (by
      simpa only [Category.comp_id] using C.basedComparison_quotient_square C' q a a' r ha ha')
    (C.affine.quotientChartOver C.adapted.rootBase q hq (a ≫ C.adapted.projection)
      r ((Category.assoc _ _ _).trans ha))
    (C'.affine.quotientChartOver C'.adapted.rootBase q hq (a' ≫ C'.adapted.projection)
      r ((Category.assoc _ _ _).trans ha'))
    (C.affine.quotientChartOver_fac C.adapted.rootBase q hq (a ≫ C.adapted.projection)
      r ((Category.assoc _ _ _).trans ha))
    (C'.affine.quotientChartOver_fac C'.adapted.rootBase q hq (a' ≫ C'.adapted.projection)
      r ((Category.assoc _ _ _).trans ha'))
  simpa only [Category.id_comp] using h

end SuppliedBorelChart

end Langlands.GroupScheme
