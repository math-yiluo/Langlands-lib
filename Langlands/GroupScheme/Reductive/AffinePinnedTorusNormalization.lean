import Langlands.GroupScheme.Reductive.AffinePinnedComparisonProperties
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Etale-local inner alignment of the actual coordinate tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A chosen actual target conjugator on each member of an etale cover makes
the normalized pulled-back comparison preserve the coordinate tori. -/
def HasEtaleTorusNormalization (e : Comparison f g) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T,
    ∀ j, ∃ c : Over.mk (𝟙 (𝒰.X j)) ⟶ (N.groupOver (𝒰.f j ≫ g)).X,
      PreservesTorus
        (pullComparison e (𝒰.f j) ≪≫ (N.groupOver (𝒰.f j ≫ g)).innerIso c)

/-- The first geometric normalization step follows from the published
etale-local conjugacy of maximal tori over arbitrary bases. -/
theorem hasEtaleTorusNormalization (e : Comparison f g) :
    HasEtaleTorusNormalization e := by
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : Smooth N.group.X.hom := N.reductive.smooth
  let : Smooth (N.groupOver g).X.hom := (N.reductive.baseChange g).smooth
  let : IsAffineHom (N.groupOver g).X.hom := (N.reductive.baseChange g).isAffineHom
  have hM : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme T M.coordinates) (M.inclusionOver f) :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom
      M.coordinates M.group M.inclusion M.maximal f
  have hN : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme T N.coordinates) (N.inclusionOver g) :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom
      N.coordinates N.group N.inclusion N.maximal g
  obtain ⟨𝒰, h𝒰⟩ := EtaleLocallySubgroupConjugate.of_isSplitTorus
    (T := splitTorus.commGroupScheme T M.coordinates)
    (T' := splitTorus.commGroupScheme T N.coordinates)
    (G := N.groupOver g)
    (i := M.inclusionOver f ≫ e.hom) (i' := N.inclusionOver g)
    (isSplitTorus_splitTorus M.coordinates) (isSplitTorus_splitTorus N.coordinates)
    (hM.comp_iso e) hN
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨c, τ, hτ⟩ := h𝒰 j
  let q := 𝒰.f j
  let cD := c ≫ (baseChangeCompIso g q N.group).inv.hom.hom
  refine ⟨cD, ⟨(splitTorus.baseChangeIso q M.coordinates).symm ≪≫ τ ≪≫
    splitTorus.baseChangeIso q N.coordinates, ?_⟩⟩
  change M.inclusionOver (q ≫ f) ≫
    ((pullComparison e q).hom ≫ ((N.groupOver (q ≫ g)).innerIso cD).hom) = _
  rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    BasedBorelTransport.baseChangeInclusion, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← innerIso_hom_comp]
  rw [← Functor.map_comp_assoc,
    ← Category.assoc _ _ (baseChangeCompIso g q N.group).inv, hτ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end Langlands.GroupScheme.AffinePinnedModel
