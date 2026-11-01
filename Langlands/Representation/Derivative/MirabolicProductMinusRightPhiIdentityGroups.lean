import Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
import Langlands.Group.GL.MirabolicMixedOrbitStages
import Langlands.Representation.Derivative.MirabolicPhiMinusMackey
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
import Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
import Langlands.Representation.Induction.SplitStagesCharacterComparison

/-!
# Groups for the identity orbit of the right `Φ⁻` sequence

Split-stage data on the plus subgroup `Q = P_(t+1) V_(t+2)` of `P_(t+2)`, `t = k+r+1`,
at the identity representative of the `(H, Q)` orbits, `H` the transported right mixed
subgroup: the kernel of `plusProjection` lies in the stages subgroup, successors of its
section preimage lie in the stabilizer, `thetaPlus` is trivial on the stabilizer, the
stabilizer's intersection with the kernel is the kernel subgroup of the right mixed
subgroup, and the Haar ratio of the comparison is `|det D|`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  GeneralLinear.Mirabolic.MixedOrbit HarmonicAnalysis

universe uF uV

/-! ## Stages data at an arbitrary representative -/

section Generic

variable {R : Type*} [CommRing R] {t : ℕ} (H : Subgroup (mirabolic (t + 1) R))
  (w : mirabolic (t + 1) R)

/-- The kernel of `plusProjection` lies in every stages subgroup. -/
theorem plusKernel_le_stagesSubgroup :
    (plusProjection (n := t) (F := R)).ker ≤ stagesSubgroup H w := by
  intro q hq
  change plusProjection q ∈ sectionSubgroup H w
  rw [MonoidHom.mem_ker.mp hq]
  exact one_mem _

/-- The preimage of the stages subgroup under `plusSuccessor` is the section subgroup. -/
theorem mem_stagesSubgroup_comap_iff (l : mirabolic t R) :
    l ∈ (stagesSubgroup H w).comap (plusSuccessor (n := t) (F := R)) ↔
      l ∈ sectionSubgroup H w := by
  change plusProjection (plusSuccessor l) ∈ sectionSubgroup H w ↔ _
  rw [plusProjection_plusSuccessor]

/-- Successors of the section preimage lie in the stabilizer. -/
theorem plusSuccessor_mem_orbitStabilizer
    (l : (stagesSubgroup H w).comap (plusSuccessor (n := t) (F := R))) :
    plusSuccessor (l : mirabolic t R) ∈ Geometric.orbitStabilizer H (plusSubgroup t R) w :=
  (mem_stagesSubgroup_comap_iff H w l.val).mp l.property

end Generic

/-! ## The kernel character of the plus subgroup -/

section KernelTheta

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The restriction of `thetaPlus` to the kernel of `plusProjection`, as a smooth character. -/
def plusKernelThetaSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (Mirabolic.plusKernel t F.Carrier) :=
  letI := T.topology
  { toMonoidHom := Mirabolic.plusKernelTheta ψ t
    isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ t).preimage Mirabolic.continuous_plusKernelEquiv }

/-- The kernel character is fixed by inverse conjugation by successors. -/
theorem plusKernelThetaSmooth_sectionInvariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    Induction.SplitKernelLocalization.SectionInvariant (plusProjection (n := t) (F := F.Carrier))
      plusSuccessor (plusKernelThetaSmooth T ψ t).toMonoidHom := by
  let := T.topology
  intro l n
  change Mirabolic.thetaPlus ψ t ((plusSuccessor l)⁻¹ * (n : plusSubgroup t F.Carrier) *
    plusSuccessor l) = Mirabolic.thetaPlus ψ t (n : plusSubgroup t F.Carrier)
  rw [map_mul, map_mul, map_inv, Mirabolic.thetaPlus_plusSuccessor, inv_one, one_mul, mul_one]

end KernelTheta

/-! ## Rank casts and projections -/

section RankCast

variable {R : Type*} [CommRing R]

theorem rankCast_rfl_apply {m : ℕ} (g : mirabolic m R) : rankCast (R := R) (rfl : m = m) g = g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem rankCast_rfl_symm_apply {m : ℕ} (g : mirabolic m R) :
    (rankCast (R := R) (rfl : m = m)).symm g = g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem projection_rankCast_eq_one_iff {m n : ℕ} (h : m = n) (g : mirabolic m R) :
    projection (rankCast h g) = 1 ↔ projection g = 1 := by
  subst h
  rw [rankCast_rfl_apply]

theorem projection_rankCast_symm_eq_one_iff {m n : ℕ} (h : m = n) (g : mirabolic n R) :
    projection ((rankCast h).symm g) = 1 ↔ projection g = 1 := by
  subst h
  rw [rankCast_rfl_symm_apply]

end RankCast

/-! ## The identity orbit -/

section Identity

variable (k r : ℕ) (R : Type*) [CommRing R]

/-- The identity stabilizer `Q ∩ H`, with ambient Lean index `mirabolic (k+r+1+1)`,
namely source-convention `P_(k+r+3)`, in the plus-subgroup Mackey filtration. -/
abbrev rightIdStabilizer : Subgroup (plusSubgroup (k + r + 1) R) :=
  Geometric.orbitStabilizer (G := mirabolic (k + r + 1 + 1) R) (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 1)

theorem rightIdStabilizer_le_stages : rightIdStabilizer k r R ≤ rightStages k r R 1 :=
  rightStabilizer_le_stages k r R 1

theorem rightIdStabilizer_isClosed [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosed (rightIdStabilizer k r R : Set (plusSubgroup (k + r + 1) R)) :=
  rightStabilizer_isClosed k r R 1

/-- `K = P.comap plusSuccessor` at the identity orbit, in lower left mixed coordinates. -/
theorem mem_rightStages_one_comap_iff (l : mirabolic (k + r + 1) R) :
    l ∈ (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R)) ↔
      (rankCast (show r + 1 + k = k + r + 1 by omega)).symm l ∈ leftSubgroup (r + 1) k R :=
  (mem_stagesSubgroup_comap_iff _ _ l).trans (mem_rightSection_one_iff k r l)

/-- An element of `K` as an element of the right identity section. -/
def rightIdentityToSection
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    MixedOrbit.rightSection k r R 1 :=
  ⟨l.val, (mem_stagesSubgroup_comap_iff _ _ l.val).mp l.property⟩

/- The two subgroups `K` and `rightSection k r R 1` of `P_(k+r+2)` coincide, but not
definitionally; values are compared through `rightIdentityToSection_val`. -/
@[simp] theorem rightIdentityToSection_val
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (rightIdentityToSection k r R l : mirabolic (k + r + 1) R) = l.val :=
  Subtype.coe_mk _ _

/-- An element of `K` in lower left mixed coordinates `[[A, B], [0, D]]`. -/
def rightIdentityLevi
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    leftSubgroup (r + 1) k R :=
  ⟨(rankCast (show r + 1 + k = k + r + 1 by omega)).symm l.val,
    (mem_rightStages_one_comap_iff k r R l.val).mp l.property⟩

@[simp] theorem rightIdentityLevi_val
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (rightIdentityLevi k r R l : mirabolic (r + 1 + k) R) =
      (rankCast (show r + 1 + k = k + r + 1 by omega)).symm l.val := rfl

/-- The same element through the published right identity section equivalence. -/
theorem rightIdentityLevi_eq
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightIdentityLevi k r R l =
      rightIdentitySectionEquiv k r R (rightIdentityToSection k r R l) :=
  Subtype.ext ((congrArg _ (rightIdentityToSection_val k r R l)).symm.trans
    (rightIdentitySectionEquiv_val k r R (rightIdentityToSection k r R l)).symm)

/-- The successor lies in the identity stabilizer over `K`. -/
theorem rightIdentity_section_mem
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    plusSuccessor (l : mirabolic (k + r + 1) R) ∈ rightIdStabilizer k r R :=
  plusSuccessor_mem_orbitStabilizer _ _ l

/-- Row `k+r+1` of an element of the identity stabilizer vanishes in the last column. -/
theorem rightStabilizer_one_lastColumn (q : rightIdStabilizer k r R) :
    lastColumn (q : plusSubgroup (k + r + 1) R).val (Fin.last (k + r + 1)) = 0 := by
  have hq := (mem_orbitStabilizer_iff (rightInducing k r R)
    (rightRepresentative k r R 1) q.val).mp q.property
  rw [rightRepresentative_one, inv_one, one_mul, mul_one, mem_rightInducing_iff,
    mem_rightSubgroup_iff_entry] at hq
  have h := hq (Fin.last k) (Fin.last (r + 1))
  rw [rightIndex_last, rankCast_symm_apply] at h
  rw [lastColumn_apply]
  have e₁ : (Fin.last (k + r + 1)).castSucc = Fin.cast (by omega)
      (rightIndex (k + 1) (r + 1) (Sum.inr (Fin.last k))) :=
    Fin.ext (by
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_cast, rightIndex_middle_val]
      omega)
  have e₂ : Fin.last (k + r + 1 + 1) = Fin.cast (by omega) (Fin.last (k + 1 + (r + 1))) :=
    Fin.ext (by
      simp only [Fin.val_last, Fin.val_cast]
      omega)
  rw [e₁, e₂]
  exact h

section Theta

variable [TopologicalSpace R]

/-- `thetaPlus` is trivial on the identity stabilizer. -/
theorem thetaPlus_rightStabilizer_one (ψ : UnitaryAdditiveCharacter R)
    (q : rightIdStabilizer k r R) :
    Mirabolic.thetaPlus ψ (k + r + 1) q.val = 1 := by
  apply Units.ext
  rw [Mirabolic.thetaPlus_apply, rightStabilizer_one_lastColumn, AddChar.map_zero_eq_one,
    Units.val_one]

end Theta

/-- The identity stabilizer in the published right mixed coordinates. -/
def rightIdentityInclusion : rightIdStabilizer k r R →* rightSubgroup (k + 1) (r + 1) R :=
  (rightInducingHom k r R).comp (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) R)
    (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 1))

@[simp] theorem rightIdentityInclusion_val (q : rightIdStabilizer k r R) :
    (rightIdentityInclusion k r R q : mirabolic (k + 1 + (r + 1)) R) =
      (rankCast (totalRank_eq k r)).symm q.val.val := by
  change (rankCast (totalRank_eq k r)).symm ((Geometric.stabilizerToInducing
    (G := mirabolic (k + r + 1 + 1) R) (rightInducing k r R)
    (plusSubgroup (k + r + 1) R) (rightRepresentative k r R 1) q : mirabolic (k + r + 1 + 1) R)) = _
  rw [Geometric.stabilizerToInducing_apply]
  congr 1
  simp only [rightRepresentative_one, inv_one, one_mul, mul_one]

/-- The block coefficient of the stabilizer is the projection of its inclusion. -/
theorem rightCoefficient_one_apply (q : rightStabilizer k r R 1) :
    rightCoefficient k r R 1 q = rightProjection (rightIdentityInclusion k r R q) := by
  simp only [rightCoefficient, rightIdentityInclusion, MonoidHom.comp_apply]

/-- The successor of `l ∈ K`, as an element of the identity stabilizer. -/
def rightIdentitySectionElement
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightIdStabilizer k r R :=
  ⟨plusSuccessor (l : mirabolic (k + r + 1) R), rightIdentity_section_mem k r R l⟩

/-- On the successor of `l ∈ K`, the blocks are `(levi A, D)`. -/
theorem rightCoefficient_rightIdentitySectionElement
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    rightCoefficient k r R 1 (rightIdentitySectionElement k r R l) =
      (levi (leftProjection (rightIdentityLevi k r R l)).1,
        (leftProjection (rightIdentityLevi k r R l)).2.val) := by
  have e : rightIdentitySectionElement k r R l =
      (plusSuccessor.subgroupComap (rightStabilizer k r R 1)) (rightIdentityToSection k r R l) :=
    Subtype.ext (congrArg plusSuccessor (rightIdentityToSection_val k r R l).symm)
  rw [e, rightIdentityLevi_eq]
  exact (MonoidHom.comp_apply (rightCoefficient k r R 1)
    (plusSuccessor.subgroupComap (rightStabilizer k r R 1)) _).symm.trans
      (rightSectionCoefficient_one k r R (rightIdentityToSection k r R l))

/-- `N = S ∩ ker plusProjection` is the kernel subgroup of the published right subgroup. -/
def rightIdentityKernelEquiv :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightIdStabilizer k r R).subtype ≃*
      rightPsiKernel (k + 1) (r + 1) R where
  toFun n := ⟨rightIdentityInclusion k r R n.val, by
    change projection (rightIdentityInclusion k r R n.val).val = 1
    rw [rightIdentityInclusion_val, projection_rankCast_symm_eq_one_iff]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp n.property)⟩
  invFun g := ⟨⟨⟨rankCast (totalRank_eq k r) g.val.val, by
      have hg : projection g.val.val = 1 := g.property
      rw [mem_plusSubgroup, (projection_rankCast_eq_one_iff _ _).mpr hg]
      exact one_mem _⟩, by
      refine (mem_orbitStabilizer_iff _ _ _).mpr ?_
      change (rightRepresentative k r R 1)⁻¹ * rankCast (totalRank_eq k r) g.val.val *
        rightRepresentative k r R 1 ∈ rightInducing k r R
      rw [rightRepresentative_one, inv_one, one_mul, mul_one, mem_rightInducing_iff,
        MulEquiv.symm_apply_apply]
      exact g.val.property⟩,
    MonoidHom.mem_ker.mpr (Subtype.ext ((projection_rankCast_eq_one_iff _ _).mpr
      (show projection g.val.val = 1 from g.property)))⟩
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change rankCast (totalRank_eq k r) (rightIdentityInclusion k r R n.val).val = n.val.val.val
    rw [rightIdentityInclusion_val, MulEquiv.apply_symm_apply]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rightIdentityInclusion_val]
    exact (rankCast (totalRank_eq k r)).symm_apply_apply _
  map_mul' a b := Subtype.ext (map_mul (rightIdentityInclusion k r R) a.val b.val)

@[simp] theorem rightIdentityKernelEquiv_val
    (n : (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightIdStabilizer k r R).subtype) :
    (rightIdentityKernelEquiv k r R n : rightSubgroup (k + 1) (r + 1) R) =
      rightIdentityInclusion k r R n.val := rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The identification of the kernel intersections is a homeomorphism. -/
def rightIdentityKernelContinuousEquiv :
    (plusProjection (n := k + r + 1) (F := R)).ker.comap (rightIdStabilizer k r R).subtype ≃ₜ*
      rightPsiKernel (k + 1) (r + 1) R where
  toMulEquiv := rightIdentityKernelEquiv k r R
  continuous_toFun :=
    ((continuous_rightInducingHom k r R).comp
      ((continuous_stabilizerToInducing _ _).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((((continuous_rankCast (totalRank_eq k r)).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk
        _).subtype_mk _


end Identity

/-! ## The split-stage data and its Haar ratio -/

section Stages

variable (k r : ℕ) (R : Type*) [CommRing R]

/-- The retraction `P → K` of the split-stage comparison at the identity orbit. -/
abbrev rightIdentityRetraction :
    rightStages k r R 1 →* (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R)) :=
  Induction.splitStagesRetraction plusProjection plusSuccessor plusProjection_plusSuccessor _
    (plusKernel_le_stagesSubgroup _ _)

/-- The identity stabilizer inside the stages subgroup. -/
abbrev rightIdentityInducing : Subgroup (rightStages k r R 1) :=
  (rightIdStabilizer k r R).subgroupOf (rightStages k r R 1)

theorem rightIdentityInducing_section_mem
    (l : (rightStages k r R 1).comap (plusSuccessor (n := k + r + 1) (F := R))) :
    (plusSuccessor (n := k + r + 1) (F := R)).subgroupComap (rightStages k r R 1) l ∈
      rightIdentityInducing k r R :=
  rightIdentity_section_mem k r R l

end Stages

section RankCastNorm

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The normalized determinant norm is unchanged by a rank cast. -/
theorem determinantNorm_rankCast_symm (T : F.TopologicalData) {m n : ℕ} (h : m = n)
    (g : mirabolic n F.Carrier) :
    T.determinantNorm (m + 1) ((rankCast h).symm g).val = T.determinantNorm (n + 1) g.val := by
  subst h
  rw [rankCast_rfl_symm_apply]

end RankCastNorm

section Haar

open Induction QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The kernel of `plusProjection` and the radical, as topological groups. -/
def plusKernelContinuousEquiv {t : ℕ} (R : Type*) [CommRing R] [TopologicalSpace R] :
    Mirabolic.plusKernel t R ≃ₜ* radical (t + 1) R where
  toMulEquiv := Mirabolic.plusKernelEquiv
  continuous_toFun := Mirabolic.continuous_plusKernelEquiv
  continuous_invFun := Mirabolic.continuous_plusKernelEquiv_symm

/-- `ν(l) = ν(A) ν(D)` for `l ∈ K` with lower left blocks `A`, `D`. -/
theorem determinantNorm_rightIdentity (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val =
      T.determinantNorm (r + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).1 *
        T.determinantNorm (k + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val := by
  have h := T.determinantNorm_leftSubgroup (rightIdentityLevi k r F.Carrier l)
  rw [rightIdentityLevi_val, determinantNorm_rankCast_symm] at h
  exact h

/-- The Haar character of the comparison at the identity orbit is `|det D|` at
`l = [[A, B], [0, D]]`: conjugation scales the kernel intersection `≅ V_(r+2)` by
`|det A|⁻¹` and the kernel `≅ V_(k+r+3)` by `|det l|⁻¹ = |det A|⁻¹ |det D|⁻¹`. -/
theorem rightIdentityHaarRatio_apply (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightIdentityRetraction k r F.Carrier).ker]
      [BorelSpace (rightIdentityRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightIdentityRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)],
      (splitKernelHaarRatio (rightIdentityRetraction k r F.Carrier)
          ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
            (rightStages k r F.Carrier 1))
          (rightIdentityInducing k r F.Carrier) (rightIdentityInducing_section_mem k r F.Carrier)
          ((rightIdStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val) l : ℝ≥0) =
        T.determinantNorm (k + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  have := isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  let P := rightStages k r F.Carrier 1
  let rP := rightIdentityRetraction k r F.Carrier
  let sP := (plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P
  let HP := rightIdentityInducing k r F.Carrier
  let I := HP.comap rP.ker.subtype
  have hHPc : IsClosed (HP : Set P) :=
    (rightIdStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val
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
  let A := (leftProjection (rightIdentityLevi k r F.Carrier l)).1
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
      plusProjection_plusSuccessor P (rightIdStabilizer k r F.Carrier)
      (plusKernel_le_stagesSubgroup _ _) (rightIdStabilizer_le_stages k r F.Carrier)).trans
      ((rightIdentityKernelContinuousEquiv k r F.Carrier).trans rightPsiKernelContinuousEquiv)
  have hq : (rightProjection (rightIdentityInclusion k r F.Carrier
      (rightIdentitySectionElement k r F.Carrier l))).1 = levi A := by
    rw [← rightCoefficient_one_apply, rightCoefficient_rightIdentitySectionElement]
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightIdentityInducing_section_mem k r F.Carrier) l)) =
      (T.determinantNorm (r + 1) A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eI
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightIdentityInducing_section_mem k r F.Carrier) l))
      (HaarModulus.normalizerConj (radical (r + 1) F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T (r + 1) A hAn)
    let j : rightIdStabilizer k r F.Carrier := ⟨i.val.val.val, i.property⟩
    change (rightProjection (rightIdentityInclusion k r F.Carrier
        ((rightIdentitySectionElement k r F.Carrier l)⁻¹ * j *
          rightIdentitySectionElement k r F.Carrier l))).1 =
      (levi A)⁻¹ * (rightProjection (rightIdentityInclusion k r F.Carrier j)).1 * ((levi A)⁻¹)⁻¹
    simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hq, inv_inv]
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightIdentity T k r l, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar

end Langlands.Derivative.MirabolicProductMinus
