import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.LinearSetting
import Langlands.GroupScheme.IntegralModel.IntegralDiagonalRepresentation
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Model congruence subgroups as linear congruence subgroups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.SpecialCompact.CongruenceGL

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
  Langlands.GroupScheme.AffineLinearEmbedding Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel ↥𝒪[F] F G)

private instance modelCongruenceAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

section Matrices

variable {N : ℕ} (Mat : Matrix (Fin N) (Fin N) M.coordAlg)
  (hcomul : ∀ i j, comul M.coordCorep (Mat i j) =
    ∑ l, Mat i l ⊗ₜ[CommRingCat.of ↥𝒪[F]] Mat l j)
  (hcounit : ∀ i j, counit M.coordCorep (Mat i j) =
    (1 : Matrix (Fin N) (Fin N) (CommRingCat.of ↥𝒪[F])) i j)

/-- The integral matrix of coordinates `Mat` evaluated at an integral section of the model. -/
def sectionMatrix (x : M.integralSections) : Matrix (Fin N) (Fin N) ↥𝒪[F] :=
  fun i j => M.integralCoordinateAlgHom x (Mat i j)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The matrix of the model representation at the generic point of an integral section is the
image of its integral coordinate matrix. -/
theorem modelRep_integralPointMap (x : M.integralSections) :
    ((modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
        (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (M.modelPoint (M.integralPointMap x)) :
        Matrix (Fin N) (Fin N) F) =
      (sectionMatrix M Mat x).map (algebraMap ↥𝒪[F] F) := by
  ext i j
  rw [modelRep_entry, modelPoint, genericModelPointEquiv_integralPointMap,
    affineSchemePointEquiv_changeRing]
  rfl

include hcomul hcounit in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The coordinate matrix of the identity section is the identity matrix. -/
theorem sectionMatrix_one : sectionMatrix M Mat 1 = 1 := by
  have h := modelRep_integralPointMap M Mat hcomul hcounit 1
  rw [map_one, ← genericRep_rationalPointsEquiv, map_one, map_one, Units.val_one] at h
  have hinj : Function.Injective (algebraMap ↥𝒪[F] F) := IsFractionRing.injective _ _
  refine Matrix.ext fun i j => ?_
  have h' := congrFun (congrFun h i) j
  rw [Matrix.map_apply, ← ringHom_one_apply (algebraMap ↥𝒪[F] F)] at h'
  exact hinj h'.symm

variable (B : GL (Fin N) ↥𝒪[F])

/-- The generic representation obtained from the model representation after conjugation by an
integral matrix. -/
abbrev conjugatedRep : MatrixRepresentation G (Fin N) :=
  M.genericRep (modelRep M.group M.coordIso Mat hcomul hcounit ≫
    ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).innerIso
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint
        (R := CommRingCat.of ↥𝒪[F]) B)).hom)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem pointMatrix_conjugatedRep (g : rationalPoints G) :
    pointMatrix (conjugatedRep M Mat hcomul hcounit B) g =
      Matrix.GeneralLinearGroup.map (algebraMap ↥𝒪[F] F) B *
        (modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
          (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (M.modelPoint g) *
        (Matrix.GeneralLinearGroup.map (algebraMap ↥𝒪[F] F) B)⁻¹ := by
  change GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
    (rationalPoints.map (conjugatedRep M Mat hcomul hcounit B) g) = _
  rw [genericRep_rationalPointsEquiv, affineMatrix_comp_innerIso]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The conjugated generic representation is a closed embedding when the matrix coefficients
generate the coordinate ring. -/
theorem isClosedSubgroup_conjugatedRep
    (hadj : Algebra.adjoin (CommRingCat.of ↥𝒪[F])
      (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) = ⊤) :
    IsClosedSubgroup (conjugatedRep M Mat hcomul hcounit B) := by
  have h1 : IsClosedSubgroup (modelRep M.group M.coordIso Mat hcomul hcounit) :=
    (IsClosedSubgroup.of_iso (modelIso M.group M.coordIso).symm).comp
      (isClosedSubgroup_toGLHom _ Mat hcomul hcounit hadj)
  have h2 := (h1.comp (IsClosedSubgroup.of_iso
    ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).innerIso
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint
        (R := CommRingCat.of ↥𝒪[F]) B)))).baseChange (Spec.algebraMap ↥𝒪[F] F)
  exact (IsClosedSubgroup.of_iso M.genericIso.symm).comp (h2.comp (IsClosedSubgroup.of_iso
    (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] F))))

/-- **Model congruence subgroups are linear congruence subgroups.** -/
theorem congruenceSubgroupAt_eq_linearCongruence
    (hadj : Algebra.adjoin (CommRingCat.of ↥𝒪[F])
      (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) = ⊤) (n : ℕ+) :
    M.congruenceSubgroupAt n =
      linearCongruence (conjugatedRep M Mat hcomul hcounit B) (algebraMap ↥𝒪[F] F)
        (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ)) := by
  have hinj : Function.Injective (algebraMap ↥𝒪[F] F) := IsFractionRing.injective _ _
  have hinjGL : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap ↥𝒪[F] F)) := by
    intro C D h
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hinj (congrFun (congrFun (congrArg (fun X : GL (Fin N) F =>
      (X : Matrix (Fin N) (Fin N) F)) h) i) j)
  have hnormal : (kernel ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ)) :
      Subgroup (GL (Fin N) ↥𝒪[F])).Normal := MonoidHom.normal_ker _
  have hs : Algebra.adjoin ↥𝒪[F] (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) = ⊤ := hadj
  -- Membership of an integral section in the level-`n` kernel.
  have hkey : ∀ (x : M.integralSections) (C : GL (Fin N) ↥𝒪[F]),
      (C : Matrix (Fin N) (Fin N) ↥𝒪[F]) = sectionMatrix M Mat x →
        (M.reductionAt n x = 1 ↔
          C ∈ kernel ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ))) := by
    intro x C hC
    rw [← map_one (M.reductionAt n), M.reductionAt_eq_iff_of_adjoin_eq_top hs, mem_kernel_iff]
    constructor
    · intro h i j
      have := h (Mat i j) ⟨(i, j), rfl⟩
      rw [hC, ← sectionMatrix_one M Mat hcomul hcounit]
      exact this
    · rintro h _ ⟨⟨i, j⟩, rfl⟩
      have := h i j
      rw [hC, ← sectionMatrix_one M Mat hcomul hcounit] at this
      exact this
  ext g
  rw [mem_linearCongruence, pointMatrix_conjugatedRep]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨C, hC⟩ := (M.mem_integralPoints_iff_modelRep Mat hcomul hcounit hadj
      (M.integralPointMap x)).1 ⟨x, rfl⟩
    have hCx : (C : Matrix (Fin N) (Fin N) ↥𝒪[F]) = sectionMatrix M Mat x := by
      refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := congrArg (fun X : GL (Fin N) F => (X : Matrix (Fin N) (Fin N) F) i j) hC
      rw [modelRep_integralPointMap] at h1
      exact h1
    refine ⟨B * C * B⁻¹, hnormal.conj_mem _ ((hkey x C hCx).1 hx) B, ?_⟩
    rw [map_mul, map_mul, map_inv, hC]
  · rintro ⟨D, hD, hDg⟩
    have hA : (modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
        (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (M.modelPoint g) =
          Matrix.GeneralLinearGroup.map (algebraMap ↥𝒪[F] F) (B⁻¹ * D * B) := by
      rw [map_mul, map_mul, map_inv, hDg]
      group
    obtain ⟨x, rfl⟩ := (M.mem_integralPoints_iff_modelRep Mat hcomul hcounit hadj g).2
      ⟨_, hA.symm⟩
    have hCx : ((B⁻¹ * D * B : GL (Fin N) ↥𝒪[F]) : Matrix (Fin N) (Fin N) ↥𝒪[F]) =
        sectionMatrix M Mat x := by
      refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := congrArg (fun X : GL (Fin N) F => (X : Matrix (Fin N) (Fin N) F) i j) hA
      rw [modelRep_integralPointMap] at h1
      exact h1.symm
    refine ⟨x, (hkey x _ hCx).2 ?_, rfl⟩
    have := hnormal.conj_mem _ hD B⁻¹
    rwa [inv_inv] at this

end Matrices

/-- **A diagonal linear congruence model of the congruence tower.** For every cocharacter `χ` of
the integral model of a connected reductive group, there is a closed embedding `ρ` of the
generic fibre into `GL_N` which makes the generic cocharacter of `χ` diagonal and under which
every level-`n` congruence subgroup of the model is the preimage of the principal congruence
subgroup of level `𝔪ⁿ`. -/
theorem exists_model_linearCongruence (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (e : Fin N → ℤ),
      IsClosedSubgroup ρ ∧
      M.genericCocharacter χ ≫ ρ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e ∧
      ∀ n : ℕ+, M.congruenceSubgroupAt n =
        linearCongruence ρ (algebraMap ↥𝒪[F] F) (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ)) := by
  obtain ⟨N, Mat, hcomul, hcounit, hadj⟩ := M.exists_integral_matrixCoefficients hG
  obtain ⟨B, e, hB⟩ :=
    GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing ↥𝒪[F]
      (χ ≫ modelRep M.group M.coordIso Mat hcomul hcounit)
  refine ⟨N, conjugatedRep M Mat hcomul hcounit B, e,
    isClosedSubgroup_conjugatedRep M Mat hcomul hcounit B hadj, ?_,
    fun n => congruenceSubgroupAt_eq_linearCongruence M Mat hcomul hcounit B hadj n⟩
  rw [genericCocharacter_comp_genericRep, ← Category.assoc, hB,
    GeneralLinear.baseChangeCocharacter_diagonalCocharacter]

end Langlands.BruhatTits.SpecialCompact.CongruenceGL
