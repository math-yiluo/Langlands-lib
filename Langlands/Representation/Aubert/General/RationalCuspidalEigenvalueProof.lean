import Langlands.Representation.Aubert.General.RationalCuspidalEigenvalueTarget
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.Representation.Aubert.SubgroupInitialTerm

/-! # The rational-point cuspidal eigenvalue of Aubert's operator -/

noncomputable section

universe u v uG uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

section ElementaryClasses

variable {H : Type uG} [Group H] [TopologicalSpace H]

/-- A zero smooth object has zero class in the exact finite-length group. -/
private theorem class_eq_zero_of_isZero
    (A : SmoothRep.{0, uG, uV} ℂ H) (hA : A.HasFiniteLength)
    (hzero : Limits.IsZero A) :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA = 0 := by
  have hz (a : A) : a = 0 :=
    congrArg (fun f : A ⟶ A => SmoothRep.hom f a)
      (hzero.eq_of_src (𝟙 A) (SmoothRep.ofHom 0))
  let : Subsingleton A := ⟨fun a b => (hz a).trans (hz b).symm⟩
  let z : A.representation.IntertwiningMap A.representation := 0
  have hses : IsShortExact z z := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun a => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    ext a
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    exact iff_of_true ⟨0, Subsingleton.elim _ _⟩ (Subsingleton.elim _ _)
  have hadd := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hA hA hA hses
  exact add_left_cancel (show
      FiniteLengthGrothendieckGroup.ofRepresentation A hA +
          FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        FiniteLengthGrothendieckGroup.ofRepresentation A hA + 0 by
    simpa only [add_zero] using hadd.symm)

variable [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H}

/-- At the full group and trivial radical the actual normalized term has class `[A]`. -/
theorem inductionJacquetClass_of_top_bot (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set H)) (hδ : IsUnimodularModulus U hU)
    (hP : P = ⊤) (hbot : U = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ H) (hA : A.HasFiniteLength)
    (hterm : ((inductionJacquetFunctor.{uG, uV} h hU).obj A).HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} h hU).obj A) hterm =
      FiniteLengthGrothendieckGroup.ofRepresentation A hA := by
  subst P
  subst U
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((inductionJacquetTermIso h hU hδ A).trans
      (SmoothRep.mkIso (SubgroupTransition.initialEquiv A.representation A.isSmooth).symm))

end ElementaryClasses

section FullEndpoint

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)]

/-- The full literal root subset gives the whole rational-point group. -/
private theorem parabolic_univ_eq_top
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    parabolic i ν Finset.univ = ⊤ := by
  have hfull := (hStandard k G hG T i hi ν hν _ Set.Subset.rfl).2
    0 (isStandardCocharacter_simple_zero i ν)
  have hp : standardParabolic i ν (simpleRelativeRoots i ν) = ⊤ := by
    simpa only [groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.parabolic_trivialCocharacter] using hfull.1
  change (standardParabolic i ν (rootSet i ν Finset.univ)).carrier _ = ⊤
  rw [rootSet_univ, hp]
  rfl

/-- The full literal root subset has trivial unipotent subgroup. -/
private theorem unipotent_univ_eq_bot :
    unipotent i ν Finset.univ = ⊥ := by
  change (standardUnipotent i ν (rootSet i ν Finset.univ)).carrier _ = ⊥
  rw [rootSet_univ, standardUnipotent_simple_eq_bot]
  rfl

end FullEndpoint

/-- Aubert's cuspidal eigenvalue for the complete actual rational-point family. -/
theorem rationalCuspidalEigenvalue :
    RationalCuspidalEigenvalueStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro A hA hcuspidal
  let hfl := standardParabolicFiniteLength.{u, v}
    i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  rw [rationalAlternatingOperator_ofRepresentation.{u, v}]
  dsimp only [PreservesFiniteLength] at hiFl hrFl
  rw [Finset.sum_eq_single Finset.univ]
  · erw [inductionJacquetClass_of_top_bot.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν Finset.univ)
      (hU Finset.univ)
      (standardUnipotent_isUnimodular i ν hU hUc Finset.univ)
      (parabolic_univ_eq_top i ν hStandard hG hi hν)
      (unipotent_univ_eq_bot i ν) A (hasFiniteLength_of_isIrreducible hA)]
    simp only [Finset.card_univ]
  · intro I _ hI
    have hz := class_eq_zero_of_isZero
      ((jacquetFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)).obj A)
      ((hrFl I) A (hasFiniteLength_of_isIrreducible hA)) (hcuspidal I hI)
    erw [← inductionK0_ofRepresentation.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I) (hiFl I) (hfl I).2.1
      ((jacquetFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)).obj A)
      ((hrFl I) A (hasFiniteLength_of_isIrreducible hA))]
    rw [hz, map_zero, smul_zero]
  · simp

end Langlands.Aubert.General.RationalPointFamily
