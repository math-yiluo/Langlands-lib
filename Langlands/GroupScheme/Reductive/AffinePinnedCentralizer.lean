import Langlands.GroupScheme.Reductive.AffinePinnedComparisonProperties
import Langlands.GroupScheme.Reductive.AffineRegularCentralizer
import Langlands.GroupScheme.Dynamic.CentralizerFromResidueFibres

/-! # The actual canonical-cocharacter centralizer of a pinned model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

/-- The canonical positive-coroot cocharacter centralizes exactly the original
coordinate split torus, including over a nonreduced or empty affine base. -/
theorem centralizer_originalCocharacter (M : AffinePinnedModel.{u}) :
    Dynamic.centralizer
        (BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis) =
      SubgroupFunctor.range M.inclusion := by
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : Smooth (splitTorus M.base M.coordinates).X.hom :=
    (isSplitTorus_splitTorus M.coordinates).smooth
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  apply Dynamic.centralizer_eq_range_of_residueFibres
  intro s
  let k := M.base.residueField s
  let : Algebra M.ring k := (Spec.preimage (M.base.fromSpecResidueField s)).hom.toAlgebra
  have hb : algebraBaseMap M.ring k = M.base.fromSpecResidueField s :=
    Spec.map_preimage _
  rw [← hb]
  change Dynamic.centralizer (Dynamic.baseChangeCocharacter (algebraBaseMap M.ring k)
    (AffineRegularBorel.cocharacter M.inclusion
      (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis))) = _
  rw [AffineRegularBorel.cocharacter_baseChange]
  have ht := centralizer_comp_eq_range_of_isRegular
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (M.reductive.isConnectedReductive_algebraMap k)
    (isSplitTorus_splitTorus M.coordinates)
    (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      M.coordinates M.group M.inclusion M.maximal k)
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) M.coordinates
      (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis))
    (AffineRegularBorel.isRegular_field M.inclusion _
      M.rootDatum M.fibrewiseRootDatum
      (AffineRegularBorel.positiveCorootExponent_regular M.inclusion
        M.rootDatum M.basis M.fibrewiseRootDatum k) k)
  have hr : SubgroupFunctor.range (splitTorus.baseChangeHom
      (K := k) M.group M.coordinates M.inclusion) =
      SubgroupFunctor.range ((baseChange (algebraBaseMap M.ring k)).map M.inclusion) :=
    SubgroupFunctor.range_iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap M.ring k) M.coordinates).symm _
  rwa [hr] at ht

/-- The equality of centralizer and actual normalized coordinate torus persists
over every common test scheme. -/
theorem centralizer_cocharacterOver (M : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) :
    Dynamic.centralizer (M.cocharacterOver f) =
      SubgroupFunctor.range (M.inclusionOver f) := by
  rw [cocharacterOver_eq_baseChange, Dynamic.centralizer_baseChange,
    centralizer_originalCocharacter, ← SubgroupFunctor.range_baseChangeHom]
  exact (SubgroupFunctor.range_iso_comp
    (splitTorus.baseChangeIso f M.coordinates).symm
    ((baseChange f).map M.inclusion)).symm

/-- The actual normalized coordinate inclusion represents that centralizer. -/
theorem isRepresentedBy_centralizer_cocharacterOver (M : AffinePinnedModel.{u})
    {T : Scheme.{u}} (f : T ⟶ M.base) :
    (Dynamic.centralizer (M.cocharacterOver f)).IsRepresentedBy (M.inclusionOver f) :=
  ⟨M.inclusionOver_mono f, (M.centralizer_cocharacterOver f).symm⟩

/-- Canonically identify any supplied representative of the cocharacter
centralizer with the actual normalized coordinate torus. -/
def cocharacterCentralizerIso (M : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) {Z : GroupScheme T} (z : Z ⟶ M.groupOver f)
    (hz : (Dynamic.centralizer (M.cocharacterOver f)).IsRepresentedBy z) :
    Z ≅ splitTorus T M.coordinates :=
  hz.isoOfIsRepresentedBy (M.isRepresentedBy_centralizer_cocharacterOver f)

theorem cocharacterCentralizerIso_hom_comp (M : AffinePinnedModel.{u})
    {T : Scheme.{u}} (f : T ⟶ M.base) {Z : GroupScheme T}
    (z : Z ⟶ M.groupOver f)
    (hz : (Dynamic.centralizer (M.cocharacterOver f)).IsRepresentedBy z) :
    (M.cocharacterCentralizerIso f z hz).hom ≫ M.inclusionOver f = z :=
  hz.isoOfIsRepresentedBy_hom_comp _

/-- For these models, preservation of the canonical cocharacter already
supplies an actual compatible isomorphism of the coordinate tori. -/
theorem PreservesCocharacter.preservesTorus
    {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base} {e : Comparison f g}
    (he : PreservesCocharacter e) : PreservesTorus e := by
  have hinv : N.cocharacterOver g ≫ e.inv = M.cocharacterOver f := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc := Dynamic.centralizer_eq_comap_of_iso (N.cocharacterOver g) e.symm
  rw [Iso.symm_hom, hinv] at hc
  have hrep := (M.isRepresentedBy_centralizer_cocharacterOver f).comp_iso e
  rw [← hc] at hrep
  let τ := hrep.isoOfIsRepresentedBy (N.isRepresentedBy_centralizer_cocharacterOver g)
  exact ⟨τ, (hrep.isoOfIsRepresentedBy_hom_comp
    (N.isRepresentedBy_centralizer_cocharacterOver g)).symm⟩

end Langlands.GroupScheme.AffinePinnedModel
