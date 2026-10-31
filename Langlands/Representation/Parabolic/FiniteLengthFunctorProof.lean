import Langlands.Representation.Parabolic.FiniteLengthFunctorStatement
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof

/-!
# Finite length under the actual normalized parabolic functors

Finite-length preservation for every smooth finite-length input, assembled
from the published finite-length admissibility and positive-rank induction
theorems, an elementary rank-zero argument, and the published Jacquet theorem.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Langlands.Parabolic.FiniteLengthFunctorAssembly

universe uK uG uV uF

/-- Finite group-algebra length implies finite group-algebra generation. -/
theorem finiteGeneration_of_finiteLength
    {k : Type uK} [Field k] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hρ : IsFiniteLength k[G] ρ.asModule) :
    Module.Finite k[G] ρ.asModule := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hρ).1
  infer_instance

/-- At total rank zero, evaluation at identity transfers finite length from
any actual product-Levi input to the actual normalized induced object. -/
theorem normalizedInductionFiniteLength_rankZero
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (B : GeneralLinear.BlockShape 0)
      (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      A.HasFiniteLength →
        ((T.normalizedParabolicInductionFunctor B).obj A).HasFiniteLength := by
  let := T.topology
  intro B A hA
  let := T.generalLinearTopologicalGroup 0
  let : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let : Subsingleton (B.Levi F.Carrier) := inferInstance
  let : Subsingleton (GeneralLinear 0 F.Carrier) :=
    ⟨fun _ _ => Units.ext (Matrix.ext fun i _ => i.elim0)⟩
  let f : GeneralLinear 0 F.Carrier →* B.Levi F.Carrier :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => (one_mul 1).symm }
  have hf : Function.Surjective f := fun m => ⟨1, Subsingleton.elim _ _⟩
  have hAf : IsFiniteLength ℂ[GeneralLinear 0 F.Carrier]
      (Representation.asModule (A.representation.comp f)) :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff A.representation f hf).mp hA
  let e : (T.normalizedParabolicInduced B A.representation).IntertwiningMap
      (A.representation.comp f) :=
    { toLinearMap :=
        { toFun := fun φ => Induction.eval _ _ φ 1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        rfl }
  have he : Function.Injective e := by
    intro φ ψ h
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change Induction.eval _ _ φ g = Induction.eval _ _ ψ g
    rw [Subsingleton.elim g 1]
    exact h
  exact FiniteLengthAssembly.finiteLength_of_injective e he hAf

/-- The actual normalized induction functor preserves finite length in every
rank, using the published arbitrary-Levi theorem in positive rank. -/
theorem normalizedInductionFunctorFiniteLength
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedInductionFiniteLengthStatement.{uF, uV} F T := by
  let := T.topology
  intro n B A hA
  cases n with
  | zero =>
    exact normalizedInductionFiniteLength_rankZero F T B A hA
  | succ n =>
    exact Classification.normalizedInductionFiniteLength.{uF, uV}
      F T (Nat.succ_pos n) B A.representation
      ((Langlands.finiteLengthAdmissibility.{uF, uV} F T).2 (n + 1) B A hA) hA

/-- The published Jacquet theorem applies to a finite-length input once its
admissibility is known, since finite length already gives finite generation. -/
theorem normalizedJacquetFiniteLength_of_admissible
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      A.IsAdmissible → A.HasFiniteLength →
        ((T.normalizedJacquetFunctor B).obj A).HasFiniteLength := by
  let := T.topology
  intro n B A hA hfin
  exact Parabolic.normalizedJacquetFiniteLength T B A.representation hA
    (finiteGeneration_of_finiteLength A.representation hfin)

/-- The actual normalized Jacquet functor preserves finite length for every
smooth input, by the published finite-length admissibility theorem. -/
theorem normalizedJacquetFunctorFiniteLength
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedJacquetFiniteLengthStatement.{uF, uV} F T := by
  let := T.topology
  intro n B A hA
  exact normalizedJacquetFiniteLength_of_admissible F T n B A
    ((Langlands.finiteLengthAdmissibility.{uF, uV} F T).1 n A hA) hA

example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedJacquetFiniteLengthStatement.{uF, max uF uV} F T :=
  normalizedJacquetFunctorFiniteLength F T

end Langlands.Parabolic.FiniteLengthFunctorAssembly

namespace Langlands.Parabolic

/-- Both actual normalized parabolic functors preserve finite group-algebra
length for every smooth input, every rank and arbitrary supplied topology. -/
theorem normalizedParabolicFiniteLength.{uField, uCarrier}
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uField} p) (T : F.TopologicalData) :
    NormalizedParabolicFiniteLengthStatement.{uField, uCarrier} F T :=
  ⟨FiniteLengthFunctorAssembly.normalizedInductionFunctorFiniteLength F T,
    FiniteLengthFunctorAssembly.normalizedJacquetFunctorFiniteLength F T⟩

universe uF uV

example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedParabolicFiniteLengthStatement.{uF, max uF uV} F T :=
  normalizedParabolicFiniteLength.{uF, max uF uV} F T

example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength
        (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B) ∧
      SmoothRep.PreservesFiniteLength
        (T.normalizedJacquetFunctor.{uF, max uF uV} B) :=
  ⟨(normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n B,
    (normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n B⟩

end Langlands.Parabolic
