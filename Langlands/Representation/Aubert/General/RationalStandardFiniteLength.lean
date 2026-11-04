import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.PrerequisiteStatements

/-! # Dynamic finite length on the actual standard rational-point families -/

noncomputable section

universe uG uV u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Equal subgroups give the same normalized Jacquet functor up to the proofs of
the decomposition and of closedness, so finite-length preservation transfers. -/
theorem jacquetFunctor_preservesFiniteLength_of_eq
    {P M U P' M' U' : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G))
    (eP : P = P') (eM : M = M') (eU : U = U')
    (hr : SmoothRep.PreservesFiniteLength (jacquetFunctor.{uG, uV} h' hU')) :
    SmoothRep.PreservesFiniteLength (jacquetFunctor.{uG, uV} h hU) := by
  subst eP eM eU
  exact hr

/-- Equal subgroups give the same normalized induction functor up to the proofs
of the decomposition and of closedness, so finite-length preservation transfers. -/
theorem normalizedInductionFunctor_preservesFiniteLength_of_eq
    {P M U P' M' U' : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G))
    (eP : P = P') (eM : M = M') (eU : U = U')
    (hi : SmoothRep.PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h' hU')) :
    SmoothRep.PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU) := by
  subst eP eM eU
  exact hi

/-- The composite `i ∘ r` preserves finite length when both factors do. -/
theorem inductionJacquetFunctor_preservesFiniteLength
    {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hr : SmoothRep.PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h hU))
    (hi : SmoothRep.PreservesFiniteLength
      (normalizedInductionFunctor.{uG, max uG uV} h hU)) :
    SmoothRep.PreservesFiniteLength (inductionJacquetFunctor.{uG, uV} h hU) :=
  SmoothRep.PreservesFiniteLength.comp hr hi

end Transport

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- A cocharacter whose dynamic subgroups are the standard subgroups of `I`:
the composite `ζ ≫ i` for the standard cocharacter `ζ` of `rootSet i ν I`
chosen from the standard-cocharacter statement. -/
def standardDynamicCocharacter (I : Finset (SimpleRoot i ν)) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  CommGroupScheme.groupHom
    (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1.choose ≫ i

/-- The standard-cocharacter statement identifies the three standard subgroups
of `I` with the rational points of the dynamic subgroups of
`standardDynamicCocharacter`. -/
theorem standardDynamicCocharacter_eq (I : Finset (SimpleRoot i ν)) :
    parabolic i ν I = (Dynamic.parabolic
      (standardDynamicCocharacter i ν hStandard hG hi hν I)).carrier (Over.mk (𝟙 _)) ∧
    levi i ν I = (Dynamic.centralizer
      (standardDynamicCocharacter i ν hStandard hG hi hν I)).carrier (Over.mk (𝟙 _)) ∧
    unipotent i ν I = (Dynamic.unipotent
      (standardDynamicCocharacter i ν hStandard hG hi hν I)).carrier (Over.mk (𝟙 _)) := by
  have hI := hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨eP, eM, eU⟩ := hI.2 _ hI.1.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · change (standardParabolic i ν (rootSet i ν I)).carrier _ = _
    rw [eP]
    rfl
  · change (standardLevi i ν (rootSet i ν I)).carrier _ = _
    rw [eM]
    rfl
  · change (standardUnipotent i ν (rootSet i ν I)).carrier _ = _
    rw [eU]
    rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local instance rationalStandardFiniteLengthPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)] [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

/-- The dynamic Jacquet finite-length statement gives finite-length
preservation by the actual normalized Jacquet functor of every standard
decomposition, at the same carrier universe. -/
theorem standardJacquet_preservesFiniteLength_of_dynamic
    (hr : DynamicJacquetFiniteLengthStatement.{u, uV}) (I : Finset (SimpleRoot i ν)) :
    SmoothRep.PreservesFiniteLength (jacquetFunctor.{u, uV}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)) := by
  obtain ⟨eP, eM, eU⟩ := standardDynamicCocharacter_eq i ν hStandard hG hi hν I
  have hUχ := eU ▸ hU I
  exact jacquetFunctor_preservesFiniteLength_of_eq _ _
    (dynamic_isSemidirectDecomposition _ _) hUχ eP eM eU (hr k G hG _ hUχ)

/-- The dynamic induction finite-length statement gives finite-length
preservation by the actual normalized induction functor of every standard
decomposition, at the same carrier universe. -/
theorem standardInduction_preservesFiniteLength_of_dynamic
    (hiD : DynamicInductionFiniteLengthStatement.{u, uV}) (I : Finset (SimpleRoot i ν)) :
    SmoothRep.PreservesFiniteLength (normalizedInductionFunctor.{u, uV}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)) := by
  obtain ⟨eP, eM, eU⟩ := standardDynamicCocharacter_eq i ν hStandard hG hi hν I
  have hUχ := eU ▸ hU I
  exact normalizedInductionFunctor_preservesFiniteLength_of_eq _ _
    (dynamic_isSemidirectDecomposition _ _) hUχ eP eM eU (hiD k G hG _ hUχ)

/-- The two dynamic finite-length statements give finite-length preservation by
the actual composite `i_I ∘ r_I` of every standard decomposition. -/
theorem standardInductionJacquet_preservesFiniteLength_of_dynamic
    (hiD : DynamicInductionFiniteLengthStatement.{u, max u uV})
    (hr : DynamicJacquetFiniteLengthStatement.{u, max u uV}) (I : Finset (SimpleRoot i ν)) :
    SmoothRep.PreservesFiniteLength (inductionJacquetFunctor.{u, uV}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)) :=
  inductionJacquetFunctor_preservesFiniteLength _ _
    (standardJacquet_preservesFiniteLength_of_dynamic i ν hStandard hG hi hν hU hr I)
    (standardInduction_preservesFiniteLength_of_dynamic i ν hStandard hG hi hν hU hiD I)

end RationalPointFamily

end Langlands.Aubert.General
