import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Aubert.General.RationalEndpoint

/-!
# Normalized induction from the full parabolic

If the parabolic subgroup of a semidirect decomposition `P = M ⋉ U` is the
whole group, evaluation at the identity is an injective intertwiner from
normalized induction into the inducing action, restricted from `P` to `G`.
Hence normalized induction from the full parabolic preserves finite length.

For the actual rational-point family, the standard-cocharacter statement makes
the full-index standard parabolic the whole group. This gives the full-index
case of `RationalSupercuspidalInductionFiniteLengthStatement`, for every
finite-length (in particular every irreducible) representation of the
full-index Levi; the proper indices are not treated here.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open scoped MonoidAlgebra

namespace Langlands.Aubert.General

universe uG uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- When every element of `G` lies in `P`, the identity of `G` as a map into `P`. -/
def fullParabolicInclusion (hP : ∀ g : G, g ∈ P) : G →* P :=
  MonoidHom.codRestrict (MonoidHom.id G) P hP

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
@[simp]
theorem fullParabolicInclusion_apply (hP : ∀ g : G, g ∈ P) (g : G) :
    ((fullParabolicInclusion hP g : P) : G) = g :=
  rfl

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem fullParabolicInclusion_surjective (hP : ∀ g : G, g ∈ P) :
    Function.Surjective (fullParabolicInclusion hP) :=
  fun p => ⟨p, rfl⟩

/-- Evaluation at the identity, from normalized induction along a parabolic
containing every element of `G` to the inducing action
`g ↦ δ_P(g)^{1/2} σ(m(g))`, read on `G` through `fullParabolicInclusion`. -/
def fullParabolicEvaluation (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj A).representation.IntertwiningMap
      ((inducingRepresentation h hU A).comp (fullParabolicInclusion hP)) where
  toFun f := Induction.eval P (inducingRepresentation h hU A) f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    change Induction.eval P (inducingRepresentation h hU A) f (1 * g) =
      (inducingRepresentation h hU A) (fullParabolicInclusion hP g)
        (Induction.eval P (inducingRepresentation h hU A) f 1)
    have hcov := normalizedInductionFunctor_covariant h hU A f (fullParabolicInclusion hP g) 1
    rw [fullParabolicInclusion_apply, mul_one] at hcov
    rw [one_mul, hcov]
    rfl

theorem fullParabolicEvaluation_apply (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) :
    fullParabolicEvaluation h hU hP A f =
      Induction.eval P (inducingRepresentation h hU A) f 1 :=
  rfl

/-- A normalized induced function from the full parabolic is determined by its
value at the identity, by covariance. -/
theorem fullParabolicEvaluation_injective (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Injective (fullParabolicEvaluation h hU hP A) := by
  intro f₁ f₂ hf
  rw [fullParabolicEvaluation_apply, fullParabolicEvaluation_apply] at hf
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h₁ := normalizedInductionFunctor_covariant h hU A f₁ ⟨x, hP x⟩ 1
  have h₂ := normalizedInductionFunctor_covariant h hU A f₂ ⟨x, hP x⟩ 1
  rw [mul_one] at h₁ h₂
  change Induction.eval P (inducingRepresentation h hU A) f₁ x =
    Induction.eval P (inducingRepresentation h hU A) f₂ x
  rw [h₁, h₂, hf]

/-- The inducing action has finite length over `G` when the Levi
representation has finite length: the scalar twist and the two surjective
changes of group `G → P → M` preserve finite length. -/
theorem inducingRepresentation_comp_fullParabolicInclusion_finiteLength
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.HasFiniteLength) :
    IsFiniteLength ℂ[G]
      (Representation.asModule ((inducingRepresentation h hU A).comp (fullParabolicInclusion hP))) := by
  have hproj : Function.Surjective h.projection :=
    fun m => ⟨⟨m, h.levi_le m.2⟩, h.projection_levi m⟩
  have hinfl : IsFiniteLength ℂ[P] (Representation.asModule (A.representation.comp h.projection)) :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff A.representation h.projection
      hproj).mp hA
  have htwist : IsFiniteLength ℂ[P] (inducingRepresentation h hU A).asModule :=
    (finiteLength_twist_iff _ _).mpr hinfl
  exact (FiniteLengthAssembly.finiteLength_comp_surjective_iff _ (fullParabolicInclusion hP)
    (fullParabolicInclusion_surjective hP)).mp htwist

/-- Normalized induction along a parabolic containing every element of `G`
preserves finite length. -/
theorem normalizedInduction_hasFiniteLength_of_forall_mem
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.HasFiniteLength) :
    ((normalizedInductionFunctor h hU).obj A).HasFiniteLength := by
  unfold SmoothRep.HasFiniteLength
  exact FiniteLengthAssembly.finiteLength_of_injective
    (ρ := ((normalizedInductionFunctor h hU).obj A).representation)
    (σ := (inducingRepresentation h hU A).comp (fullParabolicInclusion hP))
    (fullParabolicEvaluation h hU hP A) (fullParabolicEvaluation_injective h hU hP A)
    (inducingRepresentation_comp_fullParabolicInclusion_finiteLength h hU hP A hA)

end Generic

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe u

/-- Under the standard-cocharacter statement, every rational point lies in the
full-index standard parabolic; a membership form of the Library's
`parabolic_univ_eq_top`. -/
theorem mem_parabolic_univ {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hStandard : StandardCocharacterStatement.{u}) [Fintype (SimpleRoot i ν)]
    (g : RationalPoint k G.X) : g ∈ parabolic i ν Finset.univ := by
  rw [parabolic_univ_eq_top i ν hStandard hG hi hν]
  exact Subgroup.mem_top g

/-- The full-index case of `RationalSupercuspidalInductionFiniteLengthStatement`,
with the same telescope: for `I = Finset.univ`, normalized induction of every
finite-length (in particular every irreducible) smooth representation of the
full-index standard Levi has finite length. No cuspidality is needed. -/
theorem rationalSupercuspidalInductionFiniteLength_univ :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
      ∀ [LocallyCompactSpace (RationalPoint k G.X)]
        [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
        (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
        (hStandard : StandardCocharacterStatement.{u})
        (_hInter : StandardLeviIntersectionStatement.{u})
        (hRoots : HasRelativeRootSystem i)
        (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
        (_hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
        letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
        let h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν
        ∀ (σ : SmoothRep.{0, u, uV} ℂ (levi i ν Finset.univ)),
          σ.HasFiniteLength →
          ((normalizedInductionFunctor.{u, uV} (h Finset.univ) (hU Finset.univ)).obj σ).HasFiniteLength := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard _ hRoots hU _
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro h σ hσ
  exact normalizedInduction_hasFiniteLength_of_forall_mem (h Finset.univ) (hU Finset.univ)
    (mem_parabolic_univ hG i hi ν hν hStandard) σ hσ

/-- The literal `I = Finset.univ` instance of
`RationalSupercuspidalInductionFiniteLengthStatement`, with its complete
telescope and both representation hypotheses. Irreducibility already gives
finite length; the cuspidality hypothesis is not used. -/
theorem rationalSupercuspidalInductionFiniteLength_univ_of_isIrreducible :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
      ∀ [LocallyCompactSpace (RationalPoint k G.X)]
        [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
        (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
        (hStandard : StandardCocharacterStatement.{u})
        (hInter : StandardLeviIntersectionStatement.{u})
        (hRoots : HasRelativeRootSystem i)
        (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
        (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
        letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
        let h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν
        let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
        ∀ (σ : SmoothRep.{0, u, uV} ℂ (levi i ν Finset.univ)),
          σ.IsIrreducible →
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
            hU Finset.univ (hM Finset.univ) (hL Finset.univ) σ →
          ((normalizedInductionFunctor.{u, uV} (h Finset.univ) (hU Finset.univ)).obj σ).HasFiniteLength := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _ σ hσ _
  exact rationalSupercuspidalInductionFiniteLength_univ k G hG T i hi ν hν hStandard
    hInter hRoots hU hM σ (SmoothRep.hasFiniteLength_of_isIrreducible hσ)

end RationalPointFamily

end Langlands.Aubert.General
