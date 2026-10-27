import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

/-!
# Finite length under the actual normalized parabolic functors

Proposition definitions asserting that the existing normalized parabolic
induction and normalized Jacquet functors of a p-adic field with selected
topological data send every smooth representation of finite group-algebra length
to one of finite group-algebra length. Every rank and block shape is included,
with independent field and carrier universes. Nothing here proves these
assertions.
-/

namespace Langlands.Parabolic

universe uF uV

open CategoryTheory

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every rank `n` and block shape `B`, normalized parabolic induction sends
each smooth representation of the actual product Levi with carrier in `Type uV`
and finite group-algebra length to a representation of `GL_n` with carrier in
`Type (max uF uV)` and finite group-algebra length. This is a proposition
definition, not its proof. -/
def NormalizedInductionFiniteLengthStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    A.HasFiniteLength →
      ((T.normalizedParabolicInductionFunctor B).obj A).HasFiniteLength

/-- For every rank `n` and block shape `B`, the normalized Jacquet functor sends
each smooth representation of `GL_n` with carrier in `Type uV` and finite
group-algebra length to a representation of the actual product Levi with carrier
in `Type uV` and finite group-algebra length. This is a proposition definition,
not its proof. -/
def NormalizedJacquetFiniteLengthStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
    A.HasFiniteLength →
      ((T.normalizedJacquetFunctor B).obj A).HasFiniteLength

/-- Both normalized parabolic functors preserve finite group-algebra length, for
the fixed field and topological data and every rank and block shape. -/
def NormalizedParabolicFiniteLengthStatement : Prop :=
  NormalizedInductionFiniteLengthStatement.{uF, uV} F T ∧
    NormalizedJacquetFiniteLengthStatement.{uF, uV} F T

/-! ### The saturated carrier universe

At `uV := max uF uV` the induction output universe `max uF (max uF uV)`
normalizes to `max uF uV`, so both functors act between the saturated carrier
categories of the published finite-length Grothendieck groups, and the clauses
are the published finite-length preservation predicates. -/

noncomputable example (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  T.normalizedParabolicInductionFunctor.{uF, max uF uV} B

noncomputable example (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) :=
  T.normalizedJacquetFunctor.{uF, max uF uV} B

example (h : NormalizedParabolicFiniteLengthStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B) ∧
      SmoothRep.PreservesFiniteLength (T.normalizedJacquetFunctor.{uF, max uF uV} B) :=
  ⟨h.1 n B, h.2 n B⟩

/- With a separately supplied short-exactness hypothesis, the clauses at the
saturated universe feed the published maps of specialized Grothendieck groups. -/
noncomputable example (h : NormalizedParabolicFiniteLengthStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact
        (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B) →
      (B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) :=
  letI := T.topology
  fun hx => B.finiteLengthMapToGeneralLinear F.Carrier _ (h.1 n B) hx

noncomputable example (h : NormalizedParabolicFiniteLengthStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact
        (T.normalizedJacquetFunctor.{uF, max uF uV} B) →
      (GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier) :=
  letI := T.topology
  fun hx => B.finiteLengthMapFromGeneralLinear F.Carrier _ (h.2 n B) hx

end Langlands.Parabolic
