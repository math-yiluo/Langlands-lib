import Langlands.Representation.Aubert.General.NormalizedInductionUnitarity
import Langlands.Representation.Aubert.General.SemisimpleInductionIrreducibility
import Langlands.Representation.Aubert.General.RationalParabolicModulusStatement
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Irreducibility of actual unitary induction from a simple Jacquet module -/

noncomputable section

open CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

universe uG uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- Compact-quotient normalized induction of an admissible unitarizable object
is irreducible when its actual same-parabolic Jacquet module is irreducible. -/
theorem isIrreducible_induction_of_compactSpace_unitary_irreducible_jacquet
    (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
    [LocallyCompactSpace P] [CompactSpace (Induction.LeftQuotient P)]
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hmod : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hδ : IsUnimodularModulus U hU)
    (σ : SmoothRep.{0, uG, uV} ℂ M)
    (hσ : σ.IsAdmissible) (hunitary : IsUnitarizable σ.representation)
    (hJac : ((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible) :
    ((normalizedInductionFunctor h hU).obj σ).IsIrreducible :=
  isIrreducible_induction_of_unitary_irreducible_jacquet h hU hδ σ
    (compactOpenCofinal_of_nonarchimedean G)
    (normalizedInductionFunctor_obj_isAdmissible h hU hm σ hσ)
    (normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace
      h hU hP hG hmod σ hunitary)
    hJac

end Generic

namespace RationalPointFamily

universe u v

open _root_.AlgebraicGeometry GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance rationalUnitaryInductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
  (hmod : RationalParabolicModulusStatement.{u})
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hm : Continuous (isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I).projection)
  (σ : SmoothRep.{0, u, v} ℂ (levi i ν I))

include hcompact hmod hP hm

/-- The actual rational standard induction is irreducible from admissibility
and unitarizability of the inducing object and simplicity of its induced
same-parabolic Jacquet module. Quotient compactness and the full parabolic
modulus remain the two structural statement inputs. -/
theorem isIrreducible_standardInduction_of_unitary_irreducible_jacquet
    (hσ : σ.IsAdmissible) (hunitary : IsUnitarizable σ.representation)
    (hJac : ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU).obj σ)).IsIrreducible) :
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj σ).IsIrreducible := by
  obtain ⟨hunimod, hδ⟩ :=
    hmod k G hG T i hi ν hν hStandard I hU hP hm
  have : CompactSpace (Induction.LeftQuotient (parabolic i ν I)) :=
    compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν I
  have : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
  borelize (RationalPoint k G.X)
  exact isIrreducible_induction_of_compactSpace_unitary_irreducible_jacquet
    _ hU hP hm hunimod hδ
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU)
    σ hσ hunitary hJac

/-- Every specified nonzero invariant subspace of the actual rational
induction is equivalent to the whole induction by its inclusion. -/
def standardUnitaryInductionSubrepresentationEquiv
    (hσ : σ.IsAdmissible) (hunitary : IsUnitarizable σ.representation)
    (hJac : ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj σ).representation)
    (hS : S ≠ ⊥) :
    S.toRepresentation.Equiv ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj σ).representation := by
  letI := isIrreducible_standardInduction_of_unitary_irreducible_jacquet
    i ν hcompact hmod hStandard hG hi hν I hU hP hm σ hσ hunitary hJac
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  let j : S.toRepresentation.IntertwiningMap ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj σ).representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact j.ofBijective
    ⟨Subtype.val_injective, fun v => ⟨⟨v, by rw [htop]; trivial⟩, rfl⟩⟩

@[simp]
theorem standardUnitaryInductionSubrepresentationEquiv_apply
    (hσ : σ.IsAdmissible) (hunitary : IsUnitarizable σ.representation)
    (hJac : ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU).obj σ).representation)
    (hS : S ≠ ⊥) (v : S) :
    standardUnitaryInductionSubrepresentationEquiv
      i ν hcompact hmod hStandard hG hi hν I hU hP hm σ hσ hunitary hJac S hS v =
        v.val := rfl

end RationalPointFamily
end Langlands.Aubert.General
