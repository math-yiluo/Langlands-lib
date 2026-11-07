import Langlands.Representation.Aubert.General.DynamicProjection
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.Representation.Geometric.RepresentedGeometricLemmaRawQuotient

/-! # Original stabilizer projection and source-radical image geometry -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

local instance stabilizerGeometryAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local notation "dP" =>
  isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "pZ" => p ≫ Iso.hom (G.innerIso z⁻¹)
local notation "dZ" =>
  isSemidirectDecomposition_pointImage pZ l r
    (IsParabolicSubgroup.isClosedSubgroup
      (IsParabolicSubgroup.comp_iso hp (G.innerIso z⁻¹))) hr hmul
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "KQ" =>
  Subgroup.subgroupOf
    (pointImage (lQ ≫ q) ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹)) (pointImage p))
    (pointImage (lQ ≫ q))

/-- The original inverse-conjugated point of the source parabolic. -/
def inverseConjugateParabolicPoint (a : pointImage p) : pointImage pZ :=
  ⟨(MulAut.conj z⁻¹) (a : rationalPoints G), by
    rw [show pointImage pZ =
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom from
        rationalPoints_range_comp_innerIso p z⁻¹]
    exact Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩⟩

omit [TopologicalSpace k] [IsAffineHom G.X.hom] in
/-- Original semidirect projection commutes with this ambient conjugation. -/
theorem sourceProjection_inverseConjugate (a : pointImage p) :
    ((dZ).projection (inverseConjugateParabolicPoint (z := z) a) : rationalPoints G) =
      (MulAut.conj z⁻¹) ((dP).projection a : rationalPoints G) := by
  have hM : pointImage (l ≫ pZ) =
      (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom := by
    simpa only [Category.assoc] using rationalPoints_range_comp_innerIso (l ≫ p) z⁻¹
  have hU : pointImage (r ≫ pZ) =
      (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom := by
    simpa only [Category.assoc] using rationalPoints_range_comp_innerIso (r ≫ p) z⁻¹
  let mZ : pointImage (l ≫ pZ) :=
    ⟨(MulAut.conj z⁻¹) ((dP).projection a : rationalPoints G), by
      rw [hM]
      exact Subgroup.mem_map.mpr ⟨(dP).projection a, ((dP).projection a).property, rfl⟩⟩
  apply congrArg Subtype.val
    (((dZ).projection_eq_iff (inverseConjugateParabolicPoint (z := z) a) mZ).mpr ?_)
  rw [hU]
  refine Subgroup.mem_map.mpr
    ⟨((dP).projection a : rationalPoints G)⁻¹ * (a : rationalPoints G),
      (dP).projection_inv_mul_mem a, ?_⟩
  simp only [map_mul, map_inv]
  simp only [mZ, inverseConjugateParabolicPoint, MulEquiv.coe_toMonoidHom,
    MulAut.conj_inv_apply, MulAut.conj_apply, inv_inv]

omit [TopologicalSpace k] [IsAffineHom G.X.hom] in
private theorem stabilizer_mem_iff (a : pointImage q) :
    a ∈ H ↔ (a : rationalPoints G) ∈
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom := by
  change (MulAut.conj (z⁻¹)⁻¹) (a : rationalPoints G) ∈ pointImage p ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

namespace DynamicRealization

variable {D}
variable (R : D.DynamicRealization)

include R

/-- The original target projection preserves the inverse-conjugated source
parabolic, using the same original common torus. -/
theorem targetProjection_mem_sourceParabolic
    (a : pointImage q)
    (ha : (a : rationalPoints G) ∈
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) :
    ((dQ).projection a : rationalPoints G) ∈
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hP : pointImage q =
      (Dynamic.parabolic (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetParabolic]
  have hM : pointImage (lQ ≫ q) =
      (Dynamic.centralizer (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetLevi]
  have hU : pointImage (rQ ≫ q) =
      (Dynamic.unipotent (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetRadical]
  have hF := (Dynamic.parabolic_isStable_conjugation iT
    (CommGroupScheme.groupHom R.sourceCocharacter)).restrict
      (CommGroupScheme.groupHom R.targetCocharacter)
  rw [AutomorphicAction.restrict_conjugation] at hF
  have hsrc : (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom =
      (Dynamic.parabolic (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints :=
    (rationalPoints_range_comp_innerIso p z⁻¹).symm.trans
      ((pointImage_eq_range_carrier pZ).trans
        (congrArg SubgroupFunctor.rationalPoints R.sourceParabolic))
  rw [hsrc] at ha ⊢
  exact (dQ).projection_mem_of_closed_stable
    (CommGroupScheme.groupHom R.targetCocharacter ≫ iT) hP hM hU
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _) hF a ha

/-- The full orbit stabilizer maps to the literal target intersection under
the original target Levi projection. -/
def stabilizerProjection : H →* KQ where
  toFun a := ⟨(dQ).projection a.val, ((dQ).projection a.val).property,
    R.targetProjection_mem_sourceParabolic a.val
      ((stabilizer_mem_iff a.val).mp a.property)⟩
  map_one' := Subtype.ext (map_one (dQ).projection)
  map_mul' a b := Subtype.ext (map_mul (dQ).projection a.val b.val)

@[simp]
theorem stabilizerProjection_apply (a : H) :
    (R.stabilizerProjection a : pointImage (lQ ≫ q)) = (dQ).projection a.val := rfl

/-- The original Levi section lifts every target intersection point. -/
theorem stabilizerProjection_surjective : Function.Surjective R.stabilizerProjection := by
  intro m
  refine ⟨⟨Subgroup.inclusion (dQ).levi_le m.val, ?_⟩, ?_⟩
  · exact (stabilizer_mem_iff _).mpr m.property.2
  · exact Subtype.ext ((dQ).projection_levi m.val)

/-- The image of the full original stabilizer is exactly the literal
intersection parabolic in the target Levi image. -/
theorem map_stabilizer_eq_targetParabolic :
    (H).map (dQ).projection = KQ := by
  ext m
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (R.stabilizerProjection ⟨a, ha⟩).property
  · intro hm
    obtain ⟨a, ha⟩ := R.stabilizerProjection_surjective ⟨m, hm⟩
    exact ⟨a.val, a.property, congrArg Subtype.val ha⟩

/-- In original source coordinates, the source projection preserves the
forward conjugate of the original target radical. -/
theorem sourceProjection_mem_conjugate_targetRadical
    (a : pointImage p)
    (ha : (a : rationalPoints G) ∈
      (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom) :
    ((dP).projection a : rationalPoints G) ∈
      (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
  have hP : pointImage pZ =
      (Dynamic.parabolic (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.sourceParabolic]
  have hM : pointImage (l ≫ pZ) =
      (Dynamic.centralizer (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier]
    exact congrArg SubgroupFunctor.rationalPoints R.sourceLevi
  have hU : pointImage (r ≫ pZ) =
      (Dynamic.unipotent (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier]
    exact congrArg SubgroupFunctor.rationalPoints R.sourceRadical
  have hUQ : pointImage (rQ ≫ q) =
      (Dynamic.unipotent (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetRadical]
  have haZ : (inverseConjugateParabolicPoint (z := z) a : rationalPoints G) ∈
      pointImage (rQ ≫ q) := by
    have h := Subgroup.mem_map_equiv.mp ha
    simpa only [inverseConjugateParabolicPoint, MulAut.conj_apply,
      MulAut.conj_symm_apply, inv_inv] using h
  rw [hUQ] at haZ
  have hpres := (dZ).projection_mem_commonTorusUnipotent iT
    R.sourceCocharacter R.targetCocharacter hP hM hU
    (inverseConjugateParabolicPoint (z := z) a) haZ
  rw [← hUQ, sourceProjection_inverseConjugate (hp := hp) (hr := hr)
    (hmul := hmul)] at hpres
  apply Subgroup.mem_map_equiv.mpr
  simpa only [MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv] using hpres

local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))
local notation "fH" => stabilizerToLeviPoints p l r hp hr hl hmul q z

/-- The previously missing reverse image inclusion, for the original source
projection and the original target-kernel intersection. -/
theorem stabilizerKernel_image_le_sourceRadical :
    letI := leviPointTopology l hl
    Subgroup.map fH NQH ≤ pointImage (D.r' ≫ D.p') := by
  let := leviPointTopology l hl
  rintro m ⟨h, hh, rfl⟩
  have hu : ((h : pointImage q) : rationalPoints G) ∈ pointImage (rQ ≫ q) :=
    ((dQ).projection_eq_one_iff (h : pointImage q)).mp hh
  let a := Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹ h
  have ha : (a : rationalPoints G) ∈
      (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨((h : pointImage q) : rationalPoints G), hu, ?_⟩
    simp only [a, Geometric.stabilizerToInducing_apply, inv_inv,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hproj := R.sourceProjection_mem_conjugate_targetRadical a ha
  have hemb : rationalPoints.map (l ≫ p) (fH h) =
      ((dP).projection a : rationalPoints G) := by
    exact congrArg Subtype.val ((leviPointsEquiv p l hp hl).apply_symm_apply _)
  have hamb : rationalPoints.map (l ≫ p) (fH h) ∈
      pointImage (D.r' ≫ D.p' ≫ l ≫ p) := by
    rw [D.sourceRadicalPoints_eq, hemb]
    exact ⟨((dP).projection a).property, hproj⟩
  obtain ⟨n, hn⟩ := hamb
  refine ⟨n, ?_⟩
  apply (leviPointsEquiv p l hp hl).injective
  apply Subtype.ext
  change rationalPoints.map (l ≫ p) (rationalPoints.map (D.r' ≫ D.p') n) =
    rationalPoints.map (l ≫ p) (fH h)
  simpa only [pointMap_comp_apply] using hn

/-- The actual stabilizer-kernel image is the actual source intersection
radical on the source Levi's own points. -/
theorem stabilizerKernel_image_eq_sourceRadical :
    letI := leviPointTopology l hl
    Subgroup.map fH NQH = pointImage (D.r' ≫ D.p') := by
  let := leviPointTopology l hl
  exact le_antisymm R.stabilizerKernel_image_le_sourceRadical
    D.sourceRadical_le_stabilizerKernel_image

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
