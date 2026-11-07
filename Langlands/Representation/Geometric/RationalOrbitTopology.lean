import Langlands.Representation.Geometric.RationalOrbitProjection
import Langlands.Representation.Induction.SplitStagesRetraction
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof

/-! Topology and compact-open covers for the original rational orbit stages. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometric

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (p : P ⟶ G)
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (w : rationalPoints G)

local instance orbitTopologyAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance orbitTopologyPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance orbitTopologyFieldT2 : T2Space F := BruhatTits.localField_t2Space F

local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "S" => SubgroupFunctor.carrier (SubgroupFunctor.range p) T₀
local notation "Q" => SubgroupFunctor.carrier (Dynamic.parabolic χ) T₀
local notation "L" => SubgroupFunctor.carrier (Dynamic.centralizer χ) T₀
local notation "d" => Aubert.General.dynamic_isSemidirectDecomposition χ T₀
local notation "s" => Subgroup.inclusion (Aubert.General.IsSemidirectDecomposition.levi_le d)

/-- The actual restricted dynamic projection used in induction in stages. -/
def rationalOrbitStagesRetraction :
    rationalOrbitStages p χ w →* (rationalOrbitStages p χ w).comap s :=
  Induction.splitStagesRetraction (d).projection s (fun l => (d).projection_levi l)
    (rationalOrbitStages p χ w) (ker_projection_le_rationalOrbitStages p χ w)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Continuity of this original restricted projection follows from the
represented dynamic limit, without a projection-continuity premise. -/
theorem continuous_rationalOrbitStagesRetraction :
    Continuous (rationalOrbitStagesRetraction p χ w) :=
  Induction.continuous_splitStagesRetraction _ _ _ _ _
    (Aubert.General.continuous_dynamic_projection F G χ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem continuous_rationalOrbitDynamicSection : Continuous s :=
  continuous_subtype_val.subtype_mk _

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The original source point image is closed. -/
theorem isClosed_rationalOrbitSource (hp : IsParabolicSubgroup p) :
    IsClosed (S : Set (rationalPoints G)) := by
  have hc := hp.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hc
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hc

omit [LocallyCompactSpace (rationalPoints G)] in
/-- The full original compact-orbit stabilizer is closed in the actual
dynamic output parabolic. -/
theorem isClosed_rationalOrbitStabilizer (hp : IsParabolicSubgroup p) :
    IsClosed (orbitStabilizer S Q w : Set Q) :=
  Aubert.General.CorrectedFiltration.isClosed_orbitStabilizer S Q
    (isClosed_rationalOrbitSource p hp) w

omit [LocallyCompactSpace (rationalPoints G)] in
/-- The original source intersection is closed in the output Levi. -/
theorem isClosed_rationalOrbitTarget (hp : IsParabolicSubgroup p) :
    IsClosed (orbitStabilizer S L w : Set L) :=
  Aubert.General.CorrectedFiltration.isClosed_orbitStabilizer S L
    (isClosed_rationalOrbitSource p hp) w

omit [LocallyCompactSpace (rationalPoints G)] in
/-- Closedness of the literal stages subgroup follows from the actual
continuous dynamic projection and closed original target intersection. -/
theorem isClosed_rationalOrbitStages (hp : IsParabolicSubgroup p) :
    IsClosed (rationalOrbitStages p χ w : Set Q) :=
  (isClosed_rationalOrbitTarget p χ w hp).preimage
    (Aubert.General.continuous_dynamic_projection F G χ)

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The ambient split-projection kernel is closed by its original
identification with the actual dynamic radical. -/
theorem isClosed_rationalOrbitProjectionKernel :
    IsClosed ((d).projection.ker : Set Q) :=
  Aubert.General.CorrectedFiltration.isClosed_projection_ker (d)
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)

section Cover

variable [LocallyOfFiniteType G.X.hom]

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Every compact subset of the original dynamic projection kernel lies in a
compact open subgroup, via the original dynamic radical point isomorphism. -/
theorem exists_compactOpenSubgroup_rationalOrbitProjectionKernel
    (C : Set (d).projection.ker) (hC : IsCompact C) :
    ∃ K : OpenSubgroup (d).projection.ker,
      IsCompact (K : Set (d).projection.ker) ∧ C ⊆ (K : Set (d).projection.ker) := by
  let e := Aubert.General.CorrectedFiltration.projectionKerEquiv (d)
  obtain ⟨J, hJ, hCJ⟩ := BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup
    χ (e '' C) (hC.image e.continuous)
  refine ⟨J.comap e.toMonoidHom e.continuous, e.toHomeomorph.isCompact_preimage.mpr hJ, ?_⟩
  intro x hx
  exact hCJ ⟨x, hx, rfl⟩

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual ambient dynamic kernel has the pointwise compact-open cover
used by the native split-stages compatible-measure construction. -/
theorem rationalOrbitProjectionKernel_compactOpenCover (x : (d).projection.ker) :
    ∃ K : OpenSubgroup (d).projection.ker,
      IsCompact (K : Set (d).projection.ker) ∧ x ∈ K := by
  obtain ⟨K, hK, hx⟩ := exists_compactOpenSubgroup_rationalOrbitProjectionKernel χ
    {x} (isCompact_singleton)
  exact ⟨K, hK, hx (Set.mem_singleton x)⟩

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The restricted stages kernel has the same compact-open containment,
with the original nested point carriers retained. -/
theorem exists_compactOpenSubgroup_rationalOrbitStagesKernel
    (C : Set (rationalOrbitStagesRetraction p χ w).ker) (hC : IsCompact C) :
    ∃ K : OpenSubgroup (rationalOrbitStagesRetraction p χ w).ker,
      IsCompact (K : Set (rationalOrbitStagesRetraction p χ w).ker) ∧
        C ⊆ (K : Set (rationalOrbitStagesRetraction p χ w).ker) := by
  let e := Induction.splitStagesKernelContinuousEquiv (d).projection s
    (fun l => (d).projection_levi l) (rationalOrbitStages p χ w)
    (ker_projection_le_rationalOrbitStages p χ w)
  obtain ⟨J, hJ, hCJ⟩ := exists_compactOpenSubgroup_rationalOrbitProjectionKernel χ
    (e '' C) (hC.image e.continuous)
  refine ⟨J.comap e.toMonoidHom e.continuous, e.toHomeomorph.isCompact_preimage.mpr hJ, ?_⟩
  intro x hx
  exact hCJ ⟨x, hx, rfl⟩

end Cover

end Langlands.Geometric
