import Langlands.Representation.Geometric.RepresentedGeometricLemmaIntersectionPoints
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStabilizerCoefficient

/-! # The source radical inside the full stabilizer kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance radicalLiftAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
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

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
private theorem sourceRadical_ambient_mem
    (m : pointImage (D.r' ≫ D.p')) :
    rationalPoints.map (l ≫ p) (m : rationalPoints M) ∈
      pointImage (l ≫ p) ⊓
        (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
  rw [← D.sourceRadicalPoints_eq]
  obtain ⟨n, hn⟩ := m.property
  refine ⟨n, ?_⟩
  simpa only [pointMap_comp_apply] using congrArg (rationalPoints.map (l ≫ p)) hn

/-- Inverse conjugation of an actual source-radical point lies in the full
orbit stabilizer. No projection-preservation hypothesis is used. -/
def sourceRadicalToStabilizer :
    pointImage (D.r' ≫ D.p') →* H where
  toFun m := ⟨⟨(MulAut.conj z⁻¹) (rationalPoints.map (l ≫ p) m), by
      have hm := (D.sourceRadical_ambient_mem m).2
      have hu := Subgroup.mem_map_equiv.mp hm
      apply pointImage_comp_le q rQ
      simpa only [MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv] using hu⟩, by
      change (MulAut.conj (z⁻¹)⁻¹)
        ((MulAut.conj z⁻¹) (rationalPoints.map (l ≫ p) m)) ∈ pointImage p
      simpa [MulAut.conj_apply, mul_assoc] using
          pointImage_comp_le p l (D.sourceRadical_ambient_mem m).1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem sourceRadicalToStabilizer_apply_coe
    (m : pointImage (D.r' ≫ D.p')) :
    ((D.sourceRadicalToStabilizer m : pointImage q) : rationalPoints G) =
      z⁻¹ * rationalPoints.map (l ≫ p) (m : rationalPoints M) * z := by
  change z⁻¹ * rationalPoints.map (l ≫ p) (m : rationalPoints M) * z⁻¹⁻¹ = _
  rw [inv_inv]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The lift belongs to the kernel of the original target Levi projection. -/
theorem sourceRadicalToStabilizer_mem_kernel
    (m : pointImage (D.r' ≫ D.p')) :
    D.sourceRadicalToStabilizer m ∈ NQH := by
  apply (dQ).projection_eq_one_iff _ |>.mpr
  change ((D.sourceRadicalToStabilizer m : pointImage q) : rationalPoints G) ∈
    pointImage (rQ ≫ q)
  rw [D.sourceRadicalToStabilizer_apply_coe]
  have hu := Subgroup.mem_map_equiv.mp (D.sourceRadical_ambient_mem m).2
  simpa only [MulAut.conj_symm_apply] using hu

/-- The same original lift with its target-kernel membership retained. -/
def sourceRadicalToStabilizerKernel :
    pointImage (D.r' ≫ D.p') →* NQH :=
  D.sourceRadicalToStabilizer.codRestrict NQH D.sourceRadicalToStabilizer_mem_kernel

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Projecting the lift back to the original source Levi recovers its point. -/
theorem stabilizerToLeviPoints_sourceRadicalToStabilizer
    (m : pointImage (D.r' ≫ D.p')) :
    letI := leviPointTopology l hl
    stabilizerToLeviPoints p l r hp hr hl hmul q z
      (D.sourceRadicalToStabilizer m) = (m : rationalPoints M) := by
  let := leviPointTopology l hl
  let dP := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hsource :
      Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹
        (D.sourceRadicalToStabilizer m) =
      Subgroup.inclusion dP.levi_le ((leviPointsEquiv p l hp hl) m) := by
    apply Subtype.ext
    rw [Geometric.stabilizerToInducing_apply, D.sourceRadicalToStabilizer_apply_coe]
    simp only [inv_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rfl
  change (leviPointsEquiv p l hp hl).symm (dP.projection
    (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹
      (D.sourceRadicalToStabilizer m))) = _
  rw [hsource]
  change (leviPointsEquiv p l hp hl).symm
    (dP.projection ⟨(leviPointsEquiv p l hp hl) m,
      dP.levi_le ((leviPointsEquiv p l hp hl) m).property⟩) = _
  rw [dP.projection_levi, ContinuousMulEquiv.symm_apply_apply]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Every actual source-radical point occurs in the image of the full
stabilizer's target-kernel intersection under the original source projection. -/
theorem sourceRadical_le_stabilizerKernel_image :
    letI := leviPointTopology l hl
    pointImage (D.r' ≫ D.p') ≤
      Subgroup.map (stabilizerToLeviPoints p l r hp hr hl hmul q z) NQH := by
  let := leviPointTopology l hl
  intro m hm
  exact ⟨D.sourceRadicalToStabilizer ⟨m, hm⟩,
    D.sourceRadicalToStabilizer_mem_kernel ⟨m, hm⟩,
    D.stabilizerToLeviPoints_sourceRadicalToStabilizer ⟨m, hm⟩⟩

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
