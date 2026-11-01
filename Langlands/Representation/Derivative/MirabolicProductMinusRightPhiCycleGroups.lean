import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
import Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters

/-!
# Groups for the cyclic orbit of the right `Φ⁻` sequence

Split-stage data on the plus subgroup `Q = P_(t+1) V_(t+2)` of `P_(t+2)`, `t = k+r+1`,
at the cyclic representative of the `(H, Q)` orbits, `H` the transported right mixed
subgroup: the section preimage is the lower right mixed subgroup, the stabilizer's
intersection with the kernel of `plusProjection` is the kernel subgroup of the right
mixed subgroup, on which `thetaPlus` is the source character, and the Haar ratio of the
comparison is `|det a|`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  GeneralLinear.Mirabolic.MixedOrbit HarmonicAnalysis

universe uF uV

/-! ## Determinants of the right mixed subgroup -/

section Determinant

variable {R : Type*} [CommRing R] {k n : ℕ}

/-- The determinant of a case (III) element is the product of its diagonal block
determinants. -/
theorem det_rightSubgroup (g : rightSubgroup k n R) :
    (g : mirabolic (k + n) R).val.val.det =
      (rightProjection g).1.val.val.det * (rightProjection g).2.val.det := by
  conv_lhs => rw [← rightMatrix_parts g]
  change Matrix.det (Matrix.reindex (rightIndex k n) (rightIndex k n)
    (Matrix.fromBlocks (rightProjection g).1.val.val (extendRectangle (rightOffDiagonal g)) 0
      (rightProjection g).2.val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `ν(h) = ν(p) ν(a)` for `h ∈ rightSubgroup` with diagonal blocks `(p, a)`. -/
theorem determinantNorm_rightSubgroup (T : F.TopologicalData) (g : rightSubgroup k n F.Carrier) :
    T.determinantNorm (k + n + 1) (g : mirabolic (k + n) F.Carrier).val =
      T.determinantNorm (n + 1) (rightProjection g).1.val *
        T.determinantNorm k (rightProjection g).2 := by
  change T.normalizedAbsUnits (determinant _) =
    T.normalizedAbsUnits (determinant _) * T.normalizedAbsUnits (determinant _)
  rw [← map_mul]
  congr 1
  exact Units.ext (det_rightSubgroup g)

end Determinant

/-! ## The cyclic orbit -/

section Cycle

variable (k r : ℕ) (R : Type*) [CommRing R]

/-- The cyclic stabilizer `Q ∩ w H w⁻¹`, with the ambient group written
`mirabolic (k+r+1+1)` as in the orbit pieces of the plus-subgroup Mackey filtration. -/
abbrev rightCycStabilizer : Subgroup (plusSubgroup (k + r + 1) R) :=
  Geometric.orbitStabilizer (G := mirabolic (k + r + 1 + 1) R) (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 0)

theorem rightCycStabilizer_le_stages : rightCycStabilizer k r R ≤ rightStages k r R 0 :=
  rightStabilizer_le_stages k r R 0

theorem rightCycStabilizer_isClosed [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosed (rightCycStabilizer k r R : Set (plusSubgroup (k + r + 1) R)) :=
  rightStabilizer_isClosed k r R 0

/-- `K = P.comap plusSuccessor` at the cyclic orbit, in lower right mixed coordinates. -/
theorem mem_rightStages_zero_comap_iff (l : mirabolic (k + r + 1) R) :
    l ∈ (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R)) ↔
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm l ∈ rightSubgroup (k + 1) r R :=
  (mem_stagesSubgroup_comap_iff _ _ l).trans (mem_rightSection_zero_iff k r l)

/-- An element of `K` as an element of the right cyclic section. -/
def rightCycleToSection
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    MixedOrbit.rightSection k r R 0 :=
  ⟨l.val, (mem_stagesSubgroup_comap_iff _ _ l.val).mp l.property⟩

@[simp] theorem rightCycleToSection_val
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (rightCycleToSection k r R l : mirabolic (k + r + 1) R) = l.val :=
  Subtype.coe_mk _ _

/-- An element of `K` in lower right mixed coordinates `[[p, X], [0, a]]`. -/
def rightCycleLevi
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightSubgroup (k + 1) r R :=
  ⟨(rankCast (show k + 1 + r = k + r + 1 by omega)).symm l.val,
    (mem_rightStages_zero_comap_iff k r R l.val).mp l.property⟩

@[simp] theorem rightCycleLevi_val
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (rightCycleLevi k r R l : mirabolic (k + 1 + r) R) =
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm l.val := rfl

/-- The same element through the published right cyclic section equivalence. -/
theorem rightCycleLevi_eq
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightCycleLevi k r R l = rightCycleSectionEquiv k r R (rightCycleToSection k r R l) :=
  Subtype.ext ((congrArg _ (rightCycleToSection_val k r R l)).symm.trans
    (rightCycleSectionEquiv_val k r R (rightCycleToSection k r R l)).symm)

/-- The successor lies in the cyclic stabilizer over `K`. -/
theorem rightCycle_section_mem
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    plusSuccessor (l : mirabolic (k + r + 1) R) ∈ rightCycStabilizer k r R :=
  plusSuccessor_mem_orbitStabilizer _ _ l

/-- The cyclic stabilizer in the published right mixed coordinates, by inverse
conjugation with the cycle. -/
def rightCycleInclusion : rightCycStabilizer k r R →* rightSubgroup (k + 1) (r + 1) R :=
  (rightInducingHom k r R).comp (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) R)
    (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 0))

@[simp] theorem rightCycleInclusion_val (q : rightCycStabilizer k r R) :
    (rightCycleInclusion k r R q : mirabolic (k + 1 + (r + 1)) R) =
      (rankCast (totalRank_eq k r)).symm
        ((rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹ * q.val.val *
          (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)) := by
  change (rankCast (totalRank_eq k r)).symm ((Geometric.stabilizerToInducing
    (G := mirabolic (k + r + 1 + 1) R) (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 0) q : mirabolic (k + r + 1 + 1) R)) = _
  rw [Geometric.stabilizerToInducing_apply]

/-- The block coefficient of the stabilizer is the projection of its inclusion. -/
theorem rightCoefficient_zero_apply (q : rightStabilizer k r R 0) :
    rightCoefficient k r R 0 q = rightProjection (rightCycleInclusion k r R q) := by
  simp only [rightCoefficient, rightCycleInclusion, MonoidHom.comp_apply]

/-- The successor of `l ∈ K`, as an element of the cyclic stabilizer. -/
def rightCycleSectionElement
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightCycStabilizer k r R :=
  ⟨plusSuccessor (l : mirabolic (k + r + 1) R), rightCycle_section_mem k r R l⟩

/-- On the successor of `l ∈ K`, the blocks are `(successor p, a)`. -/
theorem rightCoefficient_rightCycleSectionElement
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightCoefficient k r R 0 (rightCycleSectionElement k r R l) =
      (successor (rightProjection (rightCycleLevi k r R l)).1,
        (rightProjection (rightCycleLevi k r R l)).2) := by
  have e : rightCycleSectionElement k r R l =
      (plusSuccessor.subgroupComap (rightStabilizer k r R 0)) (rightCycleToSection k r R l) :=
    Subtype.ext (congrArg plusSuccessor (rightCycleToSection_val k r R l).symm)
  rw [e, rightCycleLevi_eq]
  exact (MonoidHom.comp_apply (rightCoefficient k r R 0)
    (plusSuccessor.subgroupComap (rightStabilizer k r R 0)) _).symm.trans
      (rightSectionCoefficient_zero k r R (rightCycleToSection k r R l))

private theorem projection_conj_eq_one {n : ℕ} (w x : mirabolic n R) (hx : projection x = 1) :
    projection (w⁻¹ * x * w) = 1 := by
  rw [map_mul, map_mul, map_inv, hx, mul_one, inv_mul_cancel]

/-- `N = S ∩ ker plusProjection` is the kernel subgroup of the published right subgroup,
through inverse conjugation by the cycle. -/
def rightCycleKernelEquiv :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype ≃*
      rightPsiKernel (k + 1) (r + 1) R where
  toFun n := ⟨rightCycleInclusion k r R n.val, by
    change projection (rightCycleInclusion k r R n.val).val = 1
    rw [rightCycleInclusion_val, projection_rankCast_symm_eq_one_iff]
    exact projection_conj_eq_one R _ _ (congrArg Subtype.val (MonoidHom.mem_ker.mp n.property))⟩
  invFun g := ⟨⟨⟨(rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R) *
        rankCast (totalRank_eq k r) g.val.val *
        (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹, by
      have hg : projection (rankCast (totalRank_eq k r) g.val.val) = 1 :=
        (projection_rankCast_eq_one_iff _ _).mpr g.property
      rw [mem_plusSubgroup]
      have h := projection_conj_eq_one R (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹
        _ hg
      rw [inv_inv] at h
      rw [h]
      exact one_mem _⟩, by
      refine (mem_orbitStabilizer_iff _ _ _).mpr ?_
      change (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹ *
        ((rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R) *
          rankCast (totalRank_eq k r) g.val.val *
          (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹) *
        (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R) ∈ rightInducing k r R
      rw [show ∀ w x : mirabolic (k + r + 1 + 1) R, w⁻¹ * (w * x * w⁻¹) * w = x from
        fun w x => by group, mem_rightInducing_iff, MulEquiv.symm_apply_apply]
      exact g.val.property⟩,
    MonoidHom.mem_ker.mpr (Subtype.ext (by
      have hg : projection (rankCast (totalRank_eq k r) g.val.val) = 1 :=
        (projection_rankCast_eq_one_iff _ _).mpr g.property
      have h := projection_conj_eq_one R (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹
        _ hg
      rw [inv_inv] at h
      exact h))⟩
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R) *
      rankCast (totalRank_eq k r) (rightCycleInclusion k r R n.val).val *
      (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹ = n.val.val.val
    rw [rightCycleInclusion_val, MulEquiv.apply_symm_apply]
    group
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rightCycleInclusion_val]
    change (rankCast (totalRank_eq k r)).symm
      ((rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹ *
        ((rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R) *
          rankCast (totalRank_eq k r) g.val.val *
          (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)⁻¹) *
        (rightRepresentative k r R 0 : mirabolic (k + r + 1 + 1) R)) = _
    rw [show ∀ w x : mirabolic (k + r + 1 + 1) R, w⁻¹ * (w * x * w⁻¹) * w = x from
      fun w x => by group, MulEquiv.symm_apply_apply]
  map_mul' a b := Subtype.ext (map_mul (rightCycleInclusion k r R) a.val b.val)

@[simp] theorem rightCycleKernelEquiv_val
    (n : (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype) :
    (rightCycleKernelEquiv k r R n : rightSubgroup (k + 1) (r + 1) R) =
      rightCycleInclusion k r R n.val := rfl

section Theta

variable [TopologicalSpace R]

/-- On the cyclic kernel intersection, `thetaPlus` is the source character of the
radical `V_(r+2)` through the kernel identification. -/
theorem thetaPlus_rightCycle (ψ : UnitaryAdditiveCharacter R)
    (n : (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype) :
    Mirabolic.thetaPlus ψ (k + r + 1) n.val.val =
      Mirabolic.theta ψ r (rightPsiKernelEquiv (rightCycleKernelEquiv k r R n)) := by
  let x : radical (k + r + 1 + 1) R :=
    ⟨n.val.val.val, Mirabolic.plusKernel_val_mem ⟨n.val.val, n.property⟩⟩
  have hx : x ∈ rightRadicalIntersection k r R 0 :=
    (mem_radicalIntersection_iff _ _ x).mpr ((mem_orbitStabilizer_iff _ _ _).mp n.val.property)
  let u : rightRadicalIntersection k r R 0 := ⟨x, hx⟩
  have h : (Mirabolic.theta ψ (k + r + 1) u.val : ℂ) =
      (Mirabolic.theta ψ r (rightRadicalSource k r 0 u) : ℂ) :=
    congrArg Units.val (DFunLike.congr_fun (rightOrbitTheta_zero k r ψ) u)
  have hq : rightCycleInclusion k r R (rightRadicalInclusion k r R 0 u) =
      rightCycleInclusion k r R n.val := by
    apply Subtype.ext
    rw [rightCycleInclusion_val, rightCycleInclusion_val]
    rfl
  have hs : rightRadicalSource k r 0 u = rightPsiKernelEquiv (rightCycleKernelEquiv k r R n) := by
    apply Subtype.ext
    change (rightCoefficient k r R 0 (rightRadicalInclusion k r R 0 u)).1 =
      (rightProjection (rightCycleInclusion k r R n.val)).1
    rw [rightCoefficient_zero_apply, hq]
  apply Units.ext
  rw [Mirabolic.thetaPlus_apply, ← hs, ← h]
  rfl

end Theta

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The identification of the kernel intersections is a homeomorphism. -/
def rightCycleKernelContinuousEquiv :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightCycStabilizer k r R).subtype ≃ₜ*
      rightPsiKernel (k + 1) (r + 1) R where
  toMulEquiv := rightCycleKernelEquiv k r R
  continuous_toFun :=
    ((continuous_rightInducingHom k r R).comp
      ((continuous_stabilizerToInducing _ _).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((((continuous_const.mul ((continuous_rankCast (totalRank_eq k r)).comp
      (continuous_subtype_val.comp continuous_subtype_val))).mul continuous_const).subtype_mk
        _).subtype_mk _).subtype_mk _

end Cycle

/-! ## The split-stage data and its Haar ratio -/

section Stages

variable (k r : ℕ) (R : Type*) [CommRing R]

/-- The retraction `P → K` of the split-stage comparison at the cyclic orbit. -/
abbrev rightCycleRetraction :
    rightStages k r R 0 →* (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R)) :=
  Induction.splitStagesRetraction plusProjection plusSuccessor plusProjection_plusSuccessor _
    (plusKernel_le_stagesSubgroup _ _)

/-- The cyclic stabilizer inside the stages subgroup. -/
abbrev rightCycleInducing : Subgroup (rightStages k r R 0) :=
  (rightCycStabilizer k r R).subgroupOf (rightStages k r R 0)

theorem rightCycleInducing_section_mem
    (l : (rightStages k r R 0).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (plusSuccessor (n := k + r + 1) (F := R)).subgroupComap (rightStages k r R 0) l ∈
      rightCycleInducing k r R :=
  rightCycle_section_mem k r R l

end Stages

section Haar

open Induction QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `ν(l) = ν(p) ν(a)` for `l ∈ K` with lower right blocks `p`, `a`. -/
theorem determinantNorm_rightCycle (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val =
      T.determinantNorm (r + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).1.val *
        T.determinantNorm (k + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).2 := by
  have h := determinantNorm_rightSubgroup T (rightCycleLevi k r F.Carrier l)
  rw [rightCycleLevi_val, determinantNorm_rankCast_symm] at h
  exact h

/-- The Haar character of the comparison at the cyclic orbit is `|det a|` at
`l = [[p, X], [0, a]]`: conjugation scales the kernel intersection `≅ V_(r+2)` by
`|det p|⁻¹` and the kernel `≅ V_(k+r+3)` by `|det l|⁻¹ = |det p|⁻¹ |det a|⁻¹`. -/
theorem rightCycleHaarRatio_apply (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightCycleRetraction k r F.Carrier).ker]
      [BorelSpace (rightCycleRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightCycleRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)],
      (splitKernelHaarRatio (rightCycleRetraction k r F.Carrier)
          ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
            (rightStages k r F.Carrier 0))
          (rightCycleInducing k r F.Carrier) (rightCycleInducing_section_mem k r F.Carrier)
          ((rightCycStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val) l : ℝ≥0) =
        T.determinantNorm (k + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).2 := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  have := isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  let P := rightStages k r F.Carrier 0
  let rP := rightCycleRetraction k r F.Carrier
  let sP := (plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P
  let HP := rightCycleInducing k r F.Carrier
  let I := HP.comap rP.ker.subtype
  have hHPc : IsClosed (HP : Set P) :=
    (rightCycStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection rP HP hHPc).locallyCompactSpace
  -- The kernel: `ker rP ≃ ker plusProjection ≃ V_(k+r+3)`.
  let : LocallyCompactSpace (radical (k + r + 1 + 1) F.Carrier) :=
    radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical (k + r + 1 + 1) F.Carrier) := borel _
  have : BorelSpace (radical (k + r + 1 + 1) F.Carrier) := ⟨rfl⟩
  have hl : (levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹ ∈ Subgroup.normalizer
      (radical (k + r + 1 + 1) F.Carrier : Set (mirabolic (k + r + 1 + 1) F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  let eN : rP.ker ≃ₜ* radical (k + r + 1 + 1) F.Carrier :=
    (splitStagesKernelContinuousEquiv plusProjection plusSuccessor plusProjection_plusSuccessor P
      (plusKernel_le_stagesSubgroup _ _)).trans (plusKernelContinuousEquiv F.Carrier)
  have hN : mulEquivHaarChar (splitKernelConjugation rP sP l) =
      (T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eN (splitKernelConjugation rP sP l)
      (HaarModulus.normalizerConj (radical (k + r + 1 + 1) F.Carrier)
        ⟨(levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹, hl⟩) (fun g => Subtype.ext ?_)).trans
      (mulEquivHaarChar_conj_levi_inv T (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val hl)
    change ((((splitKernelConjugation rP sP l g : rP.ker) : P) : plusSubgroup (k + r + 1) F.Carrier) :
        mirabolic (k + r + 1 + 1) F.Carrier) =
      (levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹ *
        (((g : rP.ker) : P) : plusSubgroup (k + r + 1) F.Carrier).val *
          ((levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹)⁻¹
    rw [splitKernelConjugation_apply, inv_inv]
    rfl
  -- The intersection: `I ≃ S ∩ ker ≃ rightPsiKernel ≃ V_(r+2)`.
  let A := (rightProjection (rightCycleLevi k r F.Carrier l)).1.val
  let := T.generalLinearTopologicalGroup (r + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (r + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := r + 1) (F := F.Carrier)
  let : LocallyCompactSpace (radical (r + 1) F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical (r + 1) F.Carrier) := borel _
  have : BorelSpace (radical (r + 1) F.Carrier) := ⟨rfl⟩
  have hAn : (levi A)⁻¹ ∈ Subgroup.normalizer
      (radical (r + 1) F.Carrier : Set (mirabolic (r + 1) F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  let eI : I ≃ₜ* radical (r + 1) F.Carrier :=
    (splitStagesCoefficientIntersectionContinuousEquiv plusProjection plusSuccessor
      plusProjection_plusSuccessor P (rightCycStabilizer k r F.Carrier)
      (plusKernel_le_stagesSubgroup _ _) (rightCycStabilizer_le_stages k r F.Carrier)).trans
      ((rightCycleKernelContinuousEquiv k r F.Carrier).trans rightPsiKernelContinuousEquiv)
  have hq : (rightProjection (rightCycleInclusion k r F.Carrier
      (rightCycleSectionElement k r F.Carrier l))).1 = levi A := by
    rw [← rightCoefficient_zero_apply, rightCoefficient_rightCycleSectionElement]
    rfl
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightCycleInducing_section_mem k r F.Carrier) l)) =
      (T.determinantNorm (r + 1) A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eI
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightCycleInducing_section_mem k r F.Carrier) l))
      (HaarModulus.normalizerConj (radical (r + 1) F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T (r + 1) A hAn)
    let j : rightCycStabilizer k r F.Carrier := ⟨i.val.val.val, i.property⟩
    change (rightProjection (rightCycleInclusion k r F.Carrier
        ((rightCycleSectionElement k r F.Carrier l)⁻¹ * j *
          rightCycleSectionElement k r F.Carrier l))).1 =
      (levi A)⁻¹ * (rightProjection (rightCycleInclusion k r F.Carrier j)).1 * ((levi A)⁻¹)⁻¹
    simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hq, inv_inv]
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightCycle T k r l, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar

end Langlands.Derivative.MirabolicProductMinus
