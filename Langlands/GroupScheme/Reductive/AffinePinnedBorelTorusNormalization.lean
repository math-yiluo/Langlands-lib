import Langlands.GroupScheme.Reductive.AffinePinnedBorelNormalization
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof

/-! # Torus normalization inside the aligned canonical Borel -/

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

/-- A target Borel point aligns the coordinate tori while retaining the
canonical-Borel square on each member of an etale cover. -/
def HasEtaleBorelTorusRefinement (e : Comparison f g) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T,
    ∀ j, ∃ c : Over.mk (𝟙 (𝒰.X j)) ⟶ (N.borelOver (𝒰.f j ≫ g)).X,
      let d := pullComparison e (𝒰.f j) ≪≫
        (N.groupOver (𝒰.f j ≫ g)).innerIso
          (c ≫ (N.borelInclusionOver (𝒰.f j ≫ g)).hom.hom)
      PreservesBorel d ∧ PreservesTorus d

/-- Maximal-torus conjugacy in the actual smooth affine target Borel gives
a correction that keeps the Borel alignment. -/
theorem hasEtaleBorelTorusRefinement (e : Comparison f g)
    (he : PreservesBorel e) : HasEtaleBorelTorusRefinement e := by
  obtain ⟨β, hβ⟩ := he
  let : Smooth (N.borelOver g).X.hom :=
    (N.isRelativeBorel_borelInclusionOver g).isRelativeParabolicSubgroup.smooth
  let : IsAffineHom (N.borelOver g).X.hom :=
    (N.isRelativeBorel_borelInclusionOver g).isRelativeParabolicSubgroup.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := EtaleLocallySubgroupConjugate.of_isSplitTorus
    (T := splitTorus.commGroupScheme T M.coordinates)
    (T' := splitTorus.commGroupScheme T N.coordinates)
    (G := N.borelOver g)
    (i := M.torusToBorelOver f ≫ β.hom) (i' := N.torusToBorelOver g)
    (isSplitTorus_splitTorus M.coordinates) (isSplitTorus_splitTorus N.coordinates)
    ((M.isFibrewiseMaximalTorus_torusToBorelOver f).comp_iso β)
    (N.isFibrewiseMaximalTorus_torusToBorelOver g)
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨c, τ, hτ⟩ := h𝒰 j
  let q := 𝒰.f j
  let cA := c ≫ ((baseChange q).map (N.borelInclusionOver g)).hom.hom
  have hmap : (baseChange q).map (M.inclusionOver f ≫ e.hom) =
      (baseChange q).map (M.torusToBorelOver f ≫ β.hom) ≫
        (baseChange q).map (N.borelInclusionOver g) := by
    rw [← torusToBorelOver_comp M f, Category.assoc, hβ,
      ← Category.assoc, Functor.map_comp]
  have hτA : (baseChange q).map (M.inclusionOver f ≫ e.hom) ≫
      (((baseChange q).obj (N.groupOver g)).innerIso cA).hom =
      τ.hom ≫ (baseChange q).map (N.inclusionOver g) := by
    rw [hmap, Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hτ,
      Category.assoc, ← Functor.map_comp, torusToBorelOver_comp]
  let cB := c ≫ (baseChangeCompIso g q N.borel).inv.hom.hom
  let cD := cA ≫ (baseChangeCompIso g q N.group).inv.hom.hom
  have hbinc : (baseChange q).map (N.borelInclusionOver g) ≫
        (baseChangeCompIso g q N.group).inv =
      (baseChangeCompIso g q N.borel).inv ≫ N.borelInclusionOver (q ≫ g) := by
    rw [← borelInclusionOver_pull N g q]
    simp only [Iso.inv_hom_id_assoc]
  have hcD : cD = cB ≫ (N.borelInclusionOver (q ≫ g)).hom.hom := by
    have hh := congrArg (fun b => c ≫ b.hom.hom) hbinc
    simpa only [cD, cA, cB, Grp.comp_hom_hom, Category.assoc] using hh
  refine ⟨cB, (PreservesBorel.pull ⟨β, hβ⟩ q).trans
    (preservesBorel_inner N (q ≫ g) cB), ?_⟩
  rw [← hcD]
  refine ⟨(splitTorus.baseChangeIso q M.coordinates).symm ≪≫ τ ≪≫
    splitTorus.baseChangeIso q N.coordinates, ?_⟩
  change M.inclusionOver (q ≫ f) ≫
    ((pullComparison e q).hom ≫ ((N.groupOver (q ≫ g)).innerIso cD).hom) = _
  rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    BasedBorelTransport.baseChangeInclusion, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← innerIso_hom_comp, ← Functor.map_comp_assoc,
    ← Category.assoc _ _ (baseChangeCompIso g q N.group).inv, hτA]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
end Langlands.GroupScheme.AffinePinnedModel
