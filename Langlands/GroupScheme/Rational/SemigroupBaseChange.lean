import Langlands.GroupScheme.Rational.ActionWeightBaseChange
import Langlands.GroupScheme.Rational.TangentImageBaseChange
import Langlands.GroupScheme.Rational.SemigroupRealizationGeometry
import Langlands.GroupScheme.GeometricConnectedness

/-! # Actual semigroup subgroups under field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AutomorphicAction

variable {B B' : Scheme.{u}} {H G : GroupScheme B}
    {a : AutomorphicAction H G} {F : SubgroupFunctor G}

/-- Stability on all tests persists after arbitrary scheme base change. -/
theorem IsStable.baseChange (hF : a.IsStable F) (b : B' ⟶ B) :
    (a.baseChange b).IsStable (F.baseChange b) := by
  intro T h g hg
  change baseChangePointsEquiv b G T ((a.baseChange b).act h g) ∈
    F.carrier ((Over.map b).obj T)
  rw [baseChangePointsEquiv_act]
  exact hF _ _ _ hg

end AutomorphicAction

namespace RelativeRoot

section SemigroupImage

variable {B B' : Scheme.{u}} (b : B' ⟶ B) (S : CommGroupScheme B)

/-- The positive additive semigroup transported by actual character pullback. -/
def characterSemigroupBaseChange (A : AddSubsemigroup (characterLattice S)) :
    AddSubsemigroup (characterLattice ((CommGroupScheme.baseChange b).obj S)) :=
  A.map (characterLattice.baseChange b S).toAddHom

@[simp] theorem mem_characterSemigroupBaseChange
    (A : AddSubsemigroup (characterLattice S))
    (ψ : characterLattice ((CommGroupScheme.baseChange b).obj S)) :
    ψ ∈ characterSemigroupBaseChange b S A ↔
      ∃ χ ∈ A, characterLattice.baseChange b S χ = ψ := Iff.rfl

/-- Positive generation commutes with actual character pullback. -/
theorem characterSemigroupBaseChange_closure (Ψ : Set (characterLattice S)) :
    characterSemigroupBaseChange b S (AddSubsemigroup.closure Ψ) =
      AddSubsemigroup.closure (characterLattice.baseChange b S '' Ψ) :=
  AddHom.map_mclosure (characterLattice.baseChange b S).toAddHom Ψ

end SemigroupImage

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G

local instance semigroupBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- Smooth connected closed all-test subgroups remain so after any field
extension. Connectedness follows from the geometric connectedness of the
smooth affine representative. -/
theorem IsSmoothConnectedClosed.baseChange {F : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) :
    IsSmoothConnectedClosed (F.baseChange b) := by
  obtain ⟨H, j, hj, hc, hs, hconn⟩ := hF
  have : IsClosedImmersion j.hom.hom.left := hc
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hconn
  have : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  refine ⟨(GroupScheme.baseChange b).obj H, (GroupScheme.baseChange b).map j,
    hj.baseChange b, hc.baseChange b, ?_,
    H.connectedSpace_baseChange_of_smooth_affine b⟩
  change Smooth (pullback.snd H.X.hom b)
  infer_instance

variable [LocallyOfFiniteType G.X.hom]

local instance semigroupBaseChangeFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

variable (a : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S))

include hS

/-- The full selected weight span commutes with field extension. -/
theorem extendedLieSubmodule_semigroupWeightSpan :
    extendedLieSubmodule (K := K) G (semigroupWeightSpan a A) =
      semigroupWeightSpan (a.baseChange b) (characterSemigroupBaseChange b S A) := by
  rw [semigroupWeightSpan, extendedLieSubmodule_iSup, semigroupWeightSpan]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    change extendedActionWeightSpace (K := K) a χ.val ≤ _
    rw [← actionWeightSpace_baseChange_eq_extendedActionWeightSpace (K := K) a hS χ.val]
    exact le_iSup_of_le
      (⟨characterLattice.baseChange b S χ.val, χ.val, χ.property, rfl⟩ :
        characterSemigroupBaseChange b S A) le_rfl
  · refine iSup_le fun ψ => ?_
    obtain ⟨χ, hχ, hψ⟩ := ψ.property
    change actionWeightSpace (k := K) (G := G_K)
      (S := (CommGroupScheme.baseChange b).obj S) (a.baseChange b) ψ.val ≤ _
    rw [← hψ]
    exact (actionWeightSpace_baseChange_eq_extendedActionWeightSpace
      (K := K) a hS χ).le.trans
      (le_iSup_of_le (⟨χ, hχ⟩ : A) le_rfl)

variable [Smooth G.X.hom]

local instance semigroupBaseChangeSmooth : Smooth (G_K).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

/-- Every field extension carries the original generated subgroup functor to
the generated subgroup for the transported positive semigroup. This is equality
on all test schemes, including nonreduced ones. -/
theorem semigroupSubgroup_baseChange :
    (semigroupSubgroup a A).baseChange b =
      semigroupSubgroup (k := K) (G := G_K)
        (S := (CommGroupScheme.baseChange b).obj S)
        (a.baseChange b) (characterSemigroupBaseChange b S A) := by
  have hF := isSmoothConnectedClosed_semigroupSubgroup a hS A
  have hF_K := hF.baseChange (K := K)
  obtain ⟨H, j, hj, hc, hs, hconn⟩ := hF
  have : IsClosedImmersion j.hom.hom.left := hc
  have : Smooth H.X.hom := hs
  have : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  have hLie := (hasLieImage_semigroupSubgroup a hS A).baseChange (K := K) j hj
  rw [extendedLieSubmodule_semigroupWeightSpan (K := K) a hS A] at hLie
  exact eq_semigroupSubgroup_of_exact_lieImage (k := K) (G := G_K)
    (S := (CommGroupScheme.baseChange b).obj S) (a.baseChange b) (hS.baseChange b)
    (characterSemigroupBaseChange b S A) hF_K
    ((semigroupSubgroup_isStable a A).baseChange b) hLie

/-- Any supplied representative of the original generated functor pulls back
to a representative of the transported generated functor. -/
theorem isRepresentedBy_semigroupSubgroup_baseChange
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (semigroupSubgroup a A).IsRepresentedBy j) :
    (semigroupSubgroup (k := K) (G := G_K)
      (S := (CommGroupScheme.baseChange b).obj S)
      (a.baseChange b) (characterSemigroupBaseChange b S A)).IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := by
  rw [← semigroupSubgroup_baseChange (K := K) a hS A]
  exact hj.baseChange b

end Field
end RelativeRoot
end Langlands.GroupScheme
