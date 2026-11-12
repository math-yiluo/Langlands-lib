import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

/-! # Irreducible quotients of represented-parabolic induction

Nonzeroness follows from a compact local section. Finite-length preservation
is an explicit input to the irreducible quotient construction.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionQuotientAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Actual represented-parabolic induction of a nonzero smooth representation
is nonzero. No standardness, positivity or finite-length premise is needed. -/
theorem nontrivial_leviInduction
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    [Nontrivial σ] :
    letI := leviPointTopology l hl
    Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj σ) := by
  let := leviPointTopology l hl
  let : Nontrivial (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ) :=
    inferInstanceAs (Nontrivial σ)
  exact nontrivial_normalizedInduction
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)

/-- Finite-length preservation supplies an actual smooth irreducible quotient
of induction from irreducible input. The preservation assertion remains a
premise; irreducible input supplies finite length without admissibility. -/
theorem exists_irreducibleLeviInductionQuotient
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (hfinite : letI := leviPointTopology l hl
      SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    ∃ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
      Classification.IsIrreducibleQuotient
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
        π.representation := by
  let := leviPointTopology l hl
  let : Nontrivial σ :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible σ.representation hσ
  let : Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj σ) :=
    nontrivial_leviInduction p l r hp hl hr hmul σ
  exact RegularHeadExistence.exists_irreducibleQuotient_of_finiteLength _
    (hfinite σ (SmoothRep.hasFiniteLength_of_isIrreducible hσ))

/-- Choose the actual quotient and its irreducibility and surjection
certificate from the finite-length-preservation input. -/
def irreducibleLeviInductionQuotient
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (hfinite : letI := leviPointTopology l hl
      SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    {π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G) //
      Classification.IsIrreducibleQuotient
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
        π.representation} :=
  ⟨(exists_irreducibleLeviInductionQuotient p l r hp hl hr hmul hfinite σ hσ).choose,
    (exists_irreducibleLeviInductionQuotient p l r hp hl hr hmul hfinite σ hσ).choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic
