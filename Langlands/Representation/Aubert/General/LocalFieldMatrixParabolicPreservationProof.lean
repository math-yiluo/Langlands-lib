import Langlands.Representation.Aubert.General.LocalFieldMatrixParabolicPreservationStatement
import Langlands.Representation.Aubert.General.LocalFieldProductLeviAdmissibility
import Langlands.AllField.Representation.Classification.FiniteLengthProof
import Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllField.Representation.Parabolic.InductionExactnessProof
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction

/-! Finite length and exactness for the actual normalized matrix parabolic functors. -/

noncomputable section

open scoped MonoidAlgebra

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.SmoothRep
open Langlands.FiniteLengthAssembly

universe u v w

variable {F : Type u} [Field F] (T : LocalFieldData F)

private theorem induction_finiteLength_rankZero :
    letI := T.topology
    ∀ (B : GeneralLinear.BlockShape 0)
      (A : SmoothRep.{0, u, w} ℂ (B.Levi F)), A.HasFiniteLength →
      ((T.normalizedParabolicInductionFunctor B).obj A).HasFiniteLength := by
  let := T.topology
  intro B A hA
  let := T.generalLinearTopologicalGroup 0
  let : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let : Subsingleton (B.Levi F) := inferInstance
  let : Subsingleton (GeneralLinear 0 F) :=
    ⟨fun _ _ => Units.ext (Matrix.ext fun i _ => i.elim0)⟩
  let f : GeneralLinear 0 F →* B.Levi F := 1
  have hf : Function.Surjective f := fun m => ⟨1, Subsingleton.elim _ _⟩
  have hAf : IsFiniteLength ℂ[GeneralLinear 0 F] (Representation.asModule (A.representation.comp f)) :=
    (finiteLength_comp_surjective_iff A.representation f hf).mp hA
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
  exact finiteLength_of_injective e he hAf

private theorem induction_finiteLength (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLength (T.normalizedParabolicInductionFunctor.{u, w} B) := by
  let := T.topology
  cases n with
  | zero => exact induction_finiteLength_rankZero T B
  | succ n =>
      intro A hA
      have ha := A.isAdmissible_of_finiteLength_of_irreducible
        (AllField.CuspidalSupport.irreducibleLeviAdmissibility T (n + 1) B) hA
      exact AllField.Classification.normalizedInductionFiniteLength F T (Nat.succ_pos n) B
        A.representation ha hA

private theorem jacquet_finiteLength (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLength (T.normalizedJacquetFunctor.{u, w} B) := by
  let := T.topology
  intro A hA
  have ha := SmoothRep.isAdmissible_of_finiteLength_of_irreducible
    (fun C hC => (AllField.CuspidalSupport.cuspidalEmbedding F T n C hC).1) A hA
  exact AllField.Parabolic.normalizedJacquetFiniteLength T B A.representation ha
    (Parabolic.FiniteLengthFunctorAssembly.finiteGeneration_of_finiteLength A.representation hA)

private theorem induction_shortExact (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedParabolicInductionFunctor.{u, w} B) := by
  let := T.topology
  intro A M C i q _ _ _ h
  obtain ⟨hi, hq, he⟩ := h
  obtain ⟨hi', he', hq'⟩ := AllField.Parabolic.normalizedInductionExactness F T B A M C
    A.representation M.representation C.representation (hom i) (hom q)
    A.isSmooth M.isSmooth C.isSmooth hi hq he
  exact ⟨hi', hq', he'⟩

private theorem jacquet_shortExact (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor.{u, w} B) := by
  let := T.topology
  intro _ M _ i q _ _ _ h
  obtain ⟨hi, hq, he⟩ := h
  obtain ⟨hi', he', hq'⟩ := T.normalizedJacquetMap_exact B (hom i) (hom q) M.isSmooth hi hq he
  exact ⟨hi', hq', he'⟩

/-- The actual matrix parabolic functors preserve length and exactness over
an arbitrary nonarchimedean local field. -/
theorem localFieldMatrixParabolicPreservation : LocalFieldMatrixParabolicPreservationStatement.{u, v} := by
  intro F _ T n
  let := T.topology
  intro B
  exact ⟨induction_finiteLength T n B, induction_shortExact T n B,
    jacquet_finiteLength T n B, jacquet_shortExact T n B⟩

end Langlands.Aubert.General.RationalPointFamily.GL
