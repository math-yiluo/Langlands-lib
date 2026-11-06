import Langlands.GroupScheme.RelativeParabolicQuotientStatement
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.RelativeHomogeneousQuotientEmbedding

/-! # Relative parabolic quotient assembly with explicit structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.RelativeParabolicQuotient

/-- The precise generic properness implication consumed by the assembly below.
This definition records an input and does not assert that implication. -/
def ProperAmbientCriterion : Prop :=
  ∀ (S : Scheme.{u}) (X Y : Over S) (j : X ⟶ Y),
    Smooth X.hom → IsSeparated X.hom → QuasiCompact X.hom →
    IsProper Y.hom → LocallyOfFinitePresentation Y.hom → Mono j.left →
    (∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S),
      IsProper ((Over.pullback f).obj X).hom ∧
        ConnectedSpace ((Over.pullback f).obj X).left) →
    IsProper X.hom

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} {i : P ⟶ G}

/-- An actual homogeneous quotient whose structure morphism is proper. -/
structure ProperHomogeneousQuotient (i : P ⟶ G) where
  quotient : HomogeneousQuotient i
  proper : IsProper quotient.scheme.hom

/-- Construct a proper homogeneous quotient from the four explicit structural
statement inputs and the generic properness criterion. -/
def properQuotientOfStatements
    (hrelative : RelativeSelfNormalizerStatement.{u})
    (hfield : ParabolicSelfNormalizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hproper : ProperAmbientCriterion.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    ProperHomogeneousQuotient i := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let A := RelativeParabolicNormalizerReduction.properAmbientOfStatements
    hrelative hfield hPD hambient hG hPsmooth hi hP
  let : IsProper A.scheme.hom := A.proper
  let D := RelativeHomogeneousQuotient.quotientEmbeddingOfMapKernel
    i hi hPsmooth A.scheme A.map A.fibers
  have hsmooth : Smooth D.quotient.scheme.hom :=
    RelativeParabolicQuotientFibers.smooth D.quotient
  have hqproper : IsProper D.quotient.scheme.hom := by
    apply hproper _ D.quotient.scheme A.scheme D.embedding hsmooth
      D.quotient.separated D.quotient.quasiCompact A.proper
      A.locallyOfFinitePresentation D.mono_embedding
    intro k _ f
    exact ⟨RelativeParabolicQuotientFibers.proper_fieldBaseChange D.quotient hG f
        (RelativeParabolicQuotientFibers.parabolic_atFieldPoint hP f),
      RelativeParabolicQuotientFibers.connectedSpace_fieldBaseChange D.quotient hG f⟩
  exact ⟨D.quotient, hqproper⟩

/-- The conditional assembly has exactly the published conclusion, over every
ring and on every test scheme. Its structural inputs remain explicit. -/
theorem existenceStatement_of_statements
    (hrelative : RelativeSelfNormalizerStatement.{u})
    (hfield : ParabolicSelfNormalizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hproper : ProperAmbientCriterion.{u}) :
    ExistenceStatement.{u} := by
  intro R _ G P i hG hPsmooth hi hP
  let D := properQuotientOfStatements hrelative hfield hPD hambient hproper
    hG hPsmooth hi hP
  let : Smooth D.quotient.projection.left := D.quotient.smooth_projection
  exact ⟨D.quotient.scheme, D.quotient.projection, D.proper, inferInstance,
    D.quotient.surjective_projection, D.quotient.quasiCompact_projection,
    D.quotient.fibers⟩

end Langlands.GroupScheme.RelativeParabolicQuotient
