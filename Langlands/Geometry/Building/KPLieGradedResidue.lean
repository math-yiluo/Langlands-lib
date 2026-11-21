import Langlands.Geometry.Building.KPLieGradedPairing

/-! # Finite residue-field graded Lie pieces and their opposite-depth duality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {L : P.LieFiltrationData}

variable (L)

/-- The projection onto the image of the dual lattice in the ambient quotient. -/
def dualGradedLieProjection (x : P.Apartment) (r : ℝ) :
    ↥(L.dualLieFiltration x r) →ₗ[𝒪[F]] ↥(L.dualGradedLie x r) :=
  ((L.dualLieFiltrationPlus x r).mkQ.comp (L.dualLieFiltration x r).subtype).codRestrict
    (L.dualGradedLie x r) fun X => Submodule.mem_map.2 ⟨X.1, X.2, rfl⟩

theorem dualGradedLieProjection_surjective (x : P.Apartment) (r : ℝ) :
    Function.Surjective (L.dualGradedLieProjection x r) := by
  intro Y
  obtain ⟨X, hX, hXY⟩ := Submodule.mem_map.1 Y.2
  exact ⟨⟨X, hX⟩, Subtype.ext hXY⟩

theorem ker_dualGradedLieProjection (x : P.Apartment) (r : ℝ) :
    LinearMap.ker (L.dualGradedLieProjection x r) =
      (L.dualLieFiltrationPlus x r).comap (L.dualLieFiltration x r).subtype := by
  ext X
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- The residue-field action on the actual Lie grade, induced by its integral action. -/
@[instance_reducible]
def gradedLieResidueModule (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    Module 𝓀[F] (L.gradedLie x r) :=
  (isTorsionBySet_gradedLie hL x r).module

theorem gradedLieResidue_isScalarTower (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    let _ := L.gradedLieResidueModule hL x r
    IsScalarTower 𝒪[F] 𝓀[F] (L.gradedLie x r) :=
  (isTorsionBySet_gradedLie hL x r).isScalarTower

/-- The Lie grade is finite if its defining non-strict piece is finitely generated. -/
theorem finite_gradedLie (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    [Module.Finite 𝒪[F] (L.lieFiltrationReal x r)] : Finite (L.gradedLie x r) := by
  let _ := L.gradedLieResidueModule hL x r
  have := L.gradedLieResidue_isScalarTower hL x r
  have : Module.Finite 𝓀[F] (L.gradedLie x r) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  exact Module.finite_of_finite 𝓀[F]

variable {L}

/-- Under periodicity, multiplication by the maximal ideal shifts the dual filtration. -/
theorem smul_mem_dualLieFiltration_add_one (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    {a : 𝒪[F]} (ha : a ∈ 𝓂[F]) {X : Module.Dual F (GenericLie 𝒪[F] G)}
    (hX : X ∈ L.dualLieFiltration x r) : a • X ∈ L.dualLieFiltration x (r + 1) := by
  rw [mem_dualLieFiltration] at hX ⊢
  intro t ht Y hY
  rw [smul_apply_eq, ← apply_smul_eq]
  exact hX (t + 1) (by linarith) _ (smul_mem_lieFiltrationReal_add_one hL ha hY)

/-- Under periodicity, the maximal ideal kills the actual dual grade. -/
theorem isTorsionBySet_dualGradedLie (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    Module.IsTorsionBySet 𝒪[F] ↥(L.dualGradedLie x r) (𝓂[F] : Set 𝒪[F]) := by
  intro Y a
  obtain ⟨X, rfl⟩ := L.dualGradedLieProjection_surjective x r Y
  rw [← map_smul, ← LinearMap.mem_ker, ker_dualGradedLieProjection]
  exact L.mem_dualLieFiltrationPlus.2 ⟨r + 1, lt_add_one r,
    smul_mem_dualLieFiltration_add_one hL a.2 X.2⟩

variable (L)

/-- The residue-field action on the actual dual grade, induced by its integral action. -/
@[instance_reducible]
def dualGradedLieResidueModule (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    Module 𝓀[F] ↥(L.dualGradedLie x r) :=
  (isTorsionBySet_dualGradedLie hL x r).module

theorem dualGradedLieResidue_isScalarTower (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    let _ := L.dualGradedLieResidueModule hL x r
    IsScalarTower 𝒪[F] 𝓀[F] ↥(L.dualGradedLie x r) :=
  (isTorsionBySet_dualGradedLie hL x r).isScalarTower

/-- A chosen representative in the dual lattice of an element of the dual grade. -/
def dualGradedLieRep (x : P.Apartment) (r : ℝ) (Y : ↥(L.dualGradedLie x r)) :
    ↥(L.dualLieFiltration x r) :=
  Classical.choose (L.dualGradedLieProjection_surjective x r Y)

theorem dualGradedLieProjection_rep (x : P.Apartment) (r : ℝ) (Y : ↥(L.dualGradedLie x r)) :
    L.dualGradedLieProjection x r (L.dualGradedLieRep x r Y) = Y :=
  Classical.choose_spec (L.dualGradedLieProjection_surjective x r Y)

variable {L}

/-- The difference of two dual-lattice elements, formed in the ambient dual space. -/
private def dualDiff {x : P.Apartment} {r : ℝ} (X X' : L.dualLieFiltration x r) :
    L.dualLieFiltration x r :=
  ⟨X.1 - X'.1, sub_mem X.2 X'.2⟩

private theorem eq_dualDiff_add {x : P.Apartment} {r : ℝ} (X X' : L.dualLieFiltration x r) :
    X = dualDiff X X' + X' :=
  Subtype.ext (sub_add_cancel X.1 X'.1).symm

private theorem projection_eq_zero_iff {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) :
    L.dualGradedLieProjection x r X = 0 ↔
      (X : Module.Dual F (GenericLie 𝒪[F] G)) ∈ L.dualLieFiltrationPlus x r := by
  rw [← LinearMap.mem_ker, ker_dualGradedLieProjection]
  rfl

/-- Under left continuity, the opposite-depth pairing only depends on the dual grade. -/
theorem gradedLieDualPairing_eq_of_projection_eq (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (hc : L.IsLeftContinuousAt x (-r)) {X X' : L.dualLieFiltration x r}
    (h : L.dualGradedLieProjection x r X = L.dualGradedLieProjection x r X') :
    L.gradedLieDualPairing hL x r X = L.gradedLieDualPairing hL x r X' := by
  have hq : L.dualGradedLieProjection x r (dualDiff X X') = 0 := by
    have h' := h
    rw [eq_dualDiff_add X X', map_add] at h'
    exact add_right_cancel (h'.trans (zero_add _).symm)
  have hp : L.gradedLieDualPairing hL x r (dualDiff X X') = 0 :=
    (gradedLieDualPairing_eq_zero_iff hL hc _).2 ((projection_eq_zero_iff _).1 hq)
  calc L.gradedLieDualPairing hL x r X
      = L.gradedLieDualPairing hL x r (dualDiff X X' + X') := congrArg _ (eq_dualDiff_add X X')
    _ = L.gradedLieDualPairing hL x r X' := by rw [map_add, hp, zero_add]

/-- The projection is injective modulo the kernel of the pairing. -/
theorem projection_eq_of_gradedLieDualPairing_eq (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (hc : L.IsLeftContinuousAt x (-r)) {X X' : L.dualLieFiltration x r}
    (h : L.gradedLieDualPairing hL x r X = L.gradedLieDualPairing hL x r X') :
    L.dualGradedLieProjection x r X = L.dualGradedLieProjection x r X' := by
  have hp : L.gradedLieDualPairing hL x r (dualDiff X X') = 0 := by
    have h' := h
    rw [eq_dualDiff_add X X', map_add] at h'
    exact add_right_cancel (h'.trans (zero_add _).symm)
  have hq : L.dualGradedLieProjection x r (dualDiff X X') = 0 :=
    (projection_eq_zero_iff _).2 ((gradedLieDualPairing_eq_zero_iff hL hc _).1 hp)
  calc L.dualGradedLieProjection x r X
      = L.dualGradedLieProjection x r (dualDiff X X' + X') := congrArg _ (eq_dualDiff_add X X')
    _ = L.dualGradedLieProjection x r X' := by rw [map_add, hq, zero_add]

variable (L)

/-- The opposite-depth pairing on the actual dual grade. -/
def dualGradedLieToDual (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) :
    ↥(L.dualGradedLie x r) →ₗ[𝒪[F]] (L.gradedLie x (-r) →ₗ[𝒪[F]] 𝓀[F]) where
  toFun Y := L.gradedLieDualPairing hL x r (L.dualGradedLieRep x r Y)
  map_add' Y Z := by
    rw [← map_add]
    exact gradedLieDualPairing_eq_of_projection_eq hL hc (by
      rw [map_add, dualGradedLieProjection_rep, dualGradedLieProjection_rep,
        dualGradedLieProjection_rep])
  map_smul' c Y := by
    rw [RingHom.id_apply, ← map_smul]
    exact gradedLieDualPairing_eq_of_projection_eq hL hc (by
      rw [map_smul, dualGradedLieProjection_rep, dualGradedLieProjection_rep])

theorem dualGradedLieToDual_projection (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) (X : L.dualLieFiltration x r) :
    L.dualGradedLieToDual hL x r hc (L.dualGradedLieProjection x r X) =
      L.gradedLieDualPairing hL x r X :=
  gradedLieDualPairing_eq_of_projection_eq hL hc (L.dualGradedLieProjection_rep x r _)

theorem dualGradedLieToDual_bijective (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    Function.Bijective (L.dualGradedLieToDual hL x r hc) := by
  refine ⟨fun Y Z h => ?_, fun φ => ?_⟩
  · rw [← L.dualGradedLieProjection_rep x r Y, ← L.dualGradedLieProjection_rep x r Z]
    exact projection_eq_of_gradedLieDualPairing_eq hL hc h
  · obtain ⟨X, rfl⟩ := gradedLieDualPairing_surjective (x := x) (r := r) hL φ
    exact ⟨L.dualGradedLieProjection x r X, L.dualGradedLieToDual_projection hL x r hc X⟩

/-- Over the valuation ring, the existing opposite-depth pairing identifies the dual grade with
all integral-linear forms on the Lie grade into the residue field. -/
def dualGradedLieLinearEquiv (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    ↥(L.dualGradedLie x r) ≃ₗ[𝒪[F]] (L.gradedLie x (-r) →ₗ[𝒪[F]] 𝓀[F]) :=
  LinearEquiv.ofBijective (L.dualGradedLieToDual hL x r hc)
    (L.dualGradedLieToDual_bijective hL x r hc)

theorem dualGradedLieLinearEquiv_projection (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))]
    (X : L.dualLieFiltration x r) :
    L.dualGradedLieLinearEquiv hL x r hc (L.dualGradedLieProjection x r X) =
      L.gradedLieDualPairing hL x r X :=
  L.dualGradedLieToDual_projection hL x r hc X

/-- The identification intertwines the coadjoint action of the filtration stabilizer on the dual
grade with precomposition by the adjoint action of the inverse on the opposite Lie grade. -/
theorem dualGradedLieLinearEquiv_dualGradedAdjoint (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))]
    (g : L.filtrationStabilizer x) (Y : ↥(L.dualGradedLie x r)) (Z : L.gradedLie x (-r)) :
    L.dualGradedLieLinearEquiv hL x r hc (L.dualGradedAdjoint x r g Y) Z =
      L.dualGradedLieLinearEquiv hL x r hc Y (L.gradedAdjoint x (-r) g⁻¹ Z) := by
  obtain ⟨X, rfl⟩ := L.dualGradedLieProjection_surjective x r Y
  have hY : L.dualGradedAdjoint x r g (L.dualGradedLieProjection x r X) =
      L.dualGradedLieProjection x r ⟨coadjoint g.1 X, coadjoint_mem_dualLieFiltration g.2 X.2⟩ :=
    Subtype.ext rfl
  rw [hY, dualGradedLieLinearEquiv_projection, dualGradedLieLinearEquiv_projection,
    ← gradedLieDualPairing_gradedAdjoint hL g X]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- The dual grade at `r` is the residue-field dual of the Lie grade at `-r`. -/
def dualGradedLieResidueEquiv (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    let _ := L.gradedLieResidueModule hL x (-r)
    let _ := L.dualGradedLieResidueModule hL x r
    ↥(L.dualGradedLie x r) ≃ₗ[𝓀[F]] Module.Dual 𝓀[F] (L.gradedLie x (-r)) := by
  let _ := L.gradedLieResidueModule hL x (-r)
  let _ := L.dualGradedLieResidueModule hL x r
  have := L.gradedLieResidue_isScalarTower hL x (-r)
  have := L.dualGradedLieResidue_isScalarTower hL x r
  have hs : Function.Surjective (algebraMap 𝒪[F] 𝓀[F]) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  exact (L.dualGradedLieLinearEquiv hL x r hc |>.trans
    (LinearMap.extendScalarsOfSurjectiveEquiv hs)).extendScalarsOfSurjective hs

/-- The actual dual grade is finite under the hypotheses of the opposite-depth identification. -/
theorem finite_dualGradedLie (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ)
    (hc : L.IsLeftContinuousAt x (-r)) [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    Finite ↥(L.dualGradedLie x r) := by
  let _ := L.gradedLieResidueModule hL x (-r)
  have := L.finite_gradedLie hL x (-r)
  have : Finite (Module.Dual 𝓀[F] (L.gradedLie x (-r))) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  exact Finite.of_injective _ (L.dualGradedLieResidueEquiv hL x r hc).injective

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
