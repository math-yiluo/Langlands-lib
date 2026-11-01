import Langlands.Representation.Category.Basic
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Induction.Parabolic

/-!
# Weyl conjugacy invariance of finite-length normalized induction

A derived `GL_n`-specific, finite-length form of the Weyl conjugacy
invariance of normalized parabolic induction (compare Ban–Jantzen (2016),
Proposition 4.1(3), and Zelevinsky (1980), Theorem 1.9).
This is a proposition definition, not a proof.
-/

namespace Langlands.Parabolic

open GeneralLinear

/-- Let a permutation `w` conjugate the whole standard block Levi of `B` onto
that of `C` inside `GL_n`. If a finite-length smooth representation `σ` of the
`B`-Levi, transported to the `C`-Levi through inverse conjugation, is equivalent
to a finite-length smooth representation `τ` of the `C`-Levi, then the
normalized upper block parabolic inductions of `σ` and `τ` to `GL_n` have the
same composition factors with multiplicities. -/
def WholeLeviInductionConjugacy.{uF, uV, uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w)
    (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
    σ.HasFiniteLength → τ.HasFiniteLength →
    Nonempty ((CuspidalSupport.transport B C w hw σ.representation).Equiv
      τ.representation) →
    letI := T.generalLinearTopologicalGroup n
    HaveSameJordanHolderFactors
      (Rep.of (T.normalizedParabolicInduced B σ.representation))
      (Rep.of (T.normalizedParabolicInduced C τ.representation))

end Langlands.Parabolic
