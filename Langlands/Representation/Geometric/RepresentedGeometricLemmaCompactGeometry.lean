import Langlands.Representation.Geometric.RepresentedGeometricLemmaStabilizerGeometry
import Langlands.Representation.Geometric.RepresentedParabolicCompactComparison
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Aubert.General.GeometricK0Target

/-! # Compact comparison for the original represented orbit stabilizer -/

noncomputable section

universe u v

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactGeometryAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "sQ" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "KQ" => Subgroup.subgroupOf
  (pointImage (lQ ≫ q) ⊓
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹)) (pointImage p))
  (pointImage (lQ ≫ q))

namespace GeometricLemmaIntersectionDatum

/-- The original target projection inverse image of the literal target
intersection parabolic, as a subgroup of the original target parabolic. -/
def compactComparisonSaturation
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) : Subgroup (pointImage q) :=
  Subgroup.comap (π) KQ

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The saturation contains the kernel of the original target projection. -/
theorem projectionKernel_le_compactComparisonSaturation :
    (π).ker ≤ D.compactComparisonSaturation := by
  intro a ha
  change (π) a ∈ KQ
  change (π) a = 1 at ha
  rw [ha]
  exact (KQ).one_mem

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [LocallyCompactSpace (rationalPoints G)] in
/-- The actual saturation is closed in the original target parabolic. -/
theorem isClosed_compactComparisonSaturation :
    IsClosed (D.compactComparisonSaturation : Set (pointImage q)) := by
  have hK : IsClosed (KQ : Set (pointImage (lQ ≫ q))) :=
    ((isClosed_leviPoints q lQ hq hlQ).preimage continuous_subtype_val).inter
      ((isClosed_map_conj (pointImage p) (isClosed_pointImage p hp.isClosedSubgroup)
        z⁻¹).preimage continuous_subtype_val)
  exact hK.preimage (continuous_projection_pointImage q lQ rQ hq hlQ hrQ hmulQ)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The original target Levi section of every saturation Levi point lies
in the full original orbit stabilizer. -/
theorem compactComparisonSaturation_section_mem_stabilizer
    (m : D.compactComparisonSaturation.comap sQ) :
    sQ (m : pointImage (lQ ≫ q)) ∈ H := by
  have hm := m.property
  change (π) ⟨((m : pointImage (lQ ≫ q)) : rationalPoints G),
    (dQ).levi_le (m : pointImage (lQ ≫ q)).property⟩ ∈ KQ at hm
  rw [(dQ).projection_levi] at hm
  have hx := Subgroup.mem_map_equiv.mp hm.2
  change (MulAut.conj (z⁻¹)⁻¹)
    (((m : pointImage (lQ ≫ q)) : rationalPoints G)) ∈ pointImage p
  simpa only [MulAut.conj_apply, MulAut.conj_symm_apply, Subgroup.coe_subtype,
    inv_inv] using hx

namespace DynamicRealization

variable {D} (R : D.DynamicRealization)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
include R in
/-- The full original orbit stabilizer lies in its projection saturation. -/
theorem stabilizer_le_compactComparisonSaturation :
    H ≤ D.compactComparisonSaturation := by
  intro a ha
  change (π) a ∈ KQ
  rw [← R.map_stabilizer_eq_targetParabolic]
  exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩

end DynamicRealization

local notation "hH" =>
  Geometric.isClosed_orbitStabilizer (pointImage p) (pointImage q) z⁻¹
    (isClosed_pointImage p hp.isClosedSubgroup)

/-- The natural compact-comparison family for the full original stabilizer.
Every generic closedness, kernel and section condition is now proved. -/
def orbitCompactComparison (R : D.DynamicRealization) :
    representedCompactComparisonFamily.{u,v} q lQ rQ hq hrQ hmulQ
      D.compactComparisonSaturation H D.projectionKernel_le_compactComparisonSaturation
      hH R.stabilizer_le_compactComparisonSaturation
      D.compactComparisonSaturation_section_mem_stabilizer :=
  representedCompactComparison q lQ rQ hq hlQ hrQ hmulQ
    D.compactComparisonSaturation H D.projectionKernel_le_compactComparisonSaturation
    hH R.stabilizer_le_compactComparisonSaturation
    D.isClosed_compactComparisonSaturation
    D.compactComparisonSaturation_section_mem_stabilizer

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
