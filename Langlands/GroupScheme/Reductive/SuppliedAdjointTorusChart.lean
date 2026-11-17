import Langlands.GroupScheme.Reductive.AdjointTorusChart
import Langlands.GroupScheme.Reductive.BorelAdaptedRootBase
import Langlands.GroupScheme.Torus.CharacterProjection

/-! # Actual adjoint quotient charts with a supplied root base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

/-- Precomposing an actual full fppf quotient by an actual source
isomorphism transports its full kernel by inverse image. -/
theorem iso_comp {S : Scheme.{u}} {H G D : GroupScheme S}
    {F : SubgroupFunctor G} {q : G ⟶ D}
    (hq : RelativeRoot.IsFppfQuotient F q) (e : H ≅ G) :
    RelativeRoot.IsFppfQuotient (F.comap e.hom) (e.hom ≫ q) := by
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change Surjective (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · ext U x
    rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap,
      ← hq.2.2.2, mem_range_kernelι_iff]
    simp only [Grp.comp_hom_hom, Category.assoc]

end RelativeRoot.IsFppfQuotient

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Keep the actual group, coordinate torus, and full root datum, and
choose the supplied chamber as the model's base. Free root lines supply
the pinning for this choice of simple roots. -/
def withRootBase (b : M.rootDatum.Base) : AffinePinnedModel.{u} where
  ring := M.ring
  group := M.group
  reductive := M.reductive
  coordinates := M.coordinates
  inclusion := M.inclusion
  closed := M.closed
  maximal := M.maximal
  rootIndex := M.rootIndex
  rootDatum := M.rootDatum
  fibrewiseRootDatum := M.fibrewiseRootDatum
  rootLines := M.rootLines
  basis := b
  pinning := fun a => (Classical.choice (M.rootLines a)).symm

variable (b : M.rootDatum.Base) {D : GroupScheme M.base}
    (q : splitTorus M.base M.coordinates ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient ((center M.group).comap M.inclusion) q)

/-- The actual full central quotient, in coordinates for the supplied base. -/
def adjointQuotientChart : D ≅ splitTorus M.base b.support :=
  FppfQuotientComparison.fppfIso hq (M.withRootBase b).adjointChartProjection_isFppfQuotient

@[reassoc]
theorem adjointQuotientChart_fac :
    q ≫ (M.adjointQuotientChart b q hq).hom =
      splitTorus.characterProjection M.base (fun a : b.support => M.rootDatum.root a) := by
  rw [adjointQuotientChart, FppfQuotientComparison.fppfIso_fac]
  exact (splitTorus.characterProjection_eq_exponentTorusProjection
    (CommRingCat.of M.ring) _).symm

/-- Pull the actual quotient chart to an arbitrary scheme, keeping the
canonical coordinate normalization on the target split torus. -/
def adjointQuotientChartOver {U : Scheme.{u}} (p : U ⟶ M.base) :
    (GroupScheme.baseChange p).obj D ≅ splitTorus U b.support :=
  (GroupScheme.baseChange p).mapIso (M.adjointQuotientChart b q hq) ≪≫
    splitTorus.baseChangeIso p b.support

@[reassoc]
theorem adjointQuotientChartOver_fac {U : Scheme.{u}} (p : U ⟶ M.base) :
    (splitTorus.baseChangeIso p M.coordinates).inv ≫
        (GroupScheme.baseChange p).map q ≫ (M.adjointQuotientChartOver b q hq p).hom =
      splitTorus.characterProjection U (fun a : b.support => M.rootDatum.root a) := by
  change (splitTorus.baseChangeIso p M.coordinates).inv ≫
    (GroupScheme.baseChange p).map q ≫
    (GroupScheme.baseChange p).map (M.adjointQuotientChart b q hq).hom ≫
    (splitTorus.baseChangeIso p b.support).hom = _
  rw [← Functor.map_comp_assoc, M.adjointQuotientChart_fac,
    ← splitTorus.characterProjection_baseChange, Iso.inv_hom_id_assoc]

include hq in
/-- The normalized actual quotient map on every base change is still a
full fppf quotient; its kernel is the transported full central subgroup. -/
theorem adjointQuotientOver_isFppfQuotient {U : Scheme.{u}} (p : U ⟶ M.base) :
    RelativeRoot.IsFppfQuotient
      ((((center M.group).comap M.inclusion).baseChange p).comap
        (splitTorus.baseChangeIso p M.coordinates).inv)
      ((splitTorus.baseChangeIso p M.coordinates).inv ≫
        (GroupScheme.baseChange p).map q) :=
  (hq.baseChange p).iso_comp (splitTorus.baseChangeIso p M.coordinates).symm

end AffinePinnedModel

end Langlands.GroupScheme
