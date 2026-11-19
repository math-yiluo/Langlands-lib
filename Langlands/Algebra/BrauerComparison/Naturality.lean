import Langlands.Algebra.BrauerComparison.AbsoluteComparison
import Langlands.Algebra.BrauerScalarExtension

/-! # Naturality of Serre's Brauer comparison -/

noncomputable section

open scoped TensorProduct

universe u

namespace Langlands.BrauerComparison

open CentralSimple ClassFieldTheory.Local

section Naturality

variable (K E S T : Type u) [Field K] [Field E] [Field S] [Field T]
  [Algebra K E] [Algebra K S] [Algebra E T] [Algebra K T] [IsScalarTower K E T]
  [IsSepClosure K S] [IsSepClosure E T]

section Tower

variable [Algebra S T] [IsScalarTower K S T]

/-- Extending an actual algebra restricts its continuous degree-two class. -/
theorem csaContinuousClass_baseChange (A : CSA.{u, u} K) :
    csaContinuousClass E T (Brauer.baseChange E A) =
      continuousUnitRestriction K E S T 2 (csaContinuousClass K S A) := by
  let L := separableSplittingStage K S A
  let e := separableSplittingChart K S A
  have : Nonempty (Fin (reducedDegree K A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos K A)
  let i : L →ₐ[K] T := (IsScalarTower.toAlgHom K S T).comp L.toIntermediateField.val
  obtain ⟨M, j, hj⟩ := exists_finiteStage_containing (E := E) i
  let : Algebra L M := j.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algHom j
  have hcompat (a : L) : algebraMap M T (algebraMap L M a) = algebraMap S T (algebraMap L S a) :=
    hj a
  let f := baseChangeSplittingChart (A := A) E M e
  rw [csaContinuousClass_at_stage E T (Brauer.baseChange E A) M f,
    csaContinuousClass_at_stage K S A L e,
    relativeToContinuous_restriction K E S T L M hcompat]
  exact congrArg (relativeToContinuous E M T 2) (relativeClass_baseChangeSplittingChart
    (A := A) E M e)

/-- The actual Brauer scalar-extension and continuous restriction square commutes. -/
theorem brauerContinuousEquiv_scalarExtension (a : BrauerGroup.{u, u} K) :
    brauerContinuousEquiv E T (Brauer.scalarExtension E a) =
      continuousUnitRestriction K E S T 2 (brauerContinuousEquiv K S a) := by
  induction a using Quotient.inductionOn with
  | _ A =>
    change csaContinuousClass E T (Brauer.baseChange E A) =
      continuousUnitRestriction K E S T 2 (csaContinuousClass K S A)
    exact csaContinuousClass_baseChange K E S T A

end Tower

/-- The actual degree-two cohomological restriction for a specified embedding
of the chosen separable closures over the smaller base. -/
def restrictionForEmbedding (i : S →ₐ[K] T) :
    continuousUnitCohomology K S 2 →+ continuousUnitCohomology E T 2 := by
  let : Algebra S T := i.toRingHom.toAlgebra
  have : IsScalarTower K S T := IsScalarTower.of_algHom i
  exact (continuousUnitRestriction K E S T 2).hom.toAddMonoidHom

/-- The cohomology map induced by a specified embedding computes Brauer scalar extension. -/
theorem restrictionForEmbedding_comparison (i : S →ₐ[K] T) (a : BrauerGroup.{u, u} K) :
    restrictionForEmbedding K E S T i (brauerContinuousEquiv K S a) =
      brauerContinuousEquiv E T (Brauer.scalarExtension E a) := by
  let : Algebra S T := i.toRingHom.toAlgebra
  have : IsScalarTower K S T := IsScalarTower.of_algHom i
  exact (brauerContinuousEquiv_scalarExtension K E S T a).symm

/-- The map on degree-two cohomology is independent of the compatible
embedding of separable closures. -/
theorem restrictionForEmbedding_eq (i j : S →ₐ[K] T) :
    restrictionForEmbedding K E S T i = restrictionForEmbedding K E S T j := by
  ext x
  obtain ⟨a, rfl⟩ := (brauerContinuousEquiv K S).surjective x
  rw [restrictionForEmbedding_comparison, restrictionForEmbedding_comparison]

end Naturality

section ClosureChoice

variable (K S T : Type u) [Field K] [Field S] [Field T] [Algebra K S] [Algebra K T]
  [IsSepClosure K S] [IsSepClosure K T]

/-- The canonical identification of continuous degree-two cohomology for two
choices of separable closure of the same field. -/
def cohomologyClosureEquiv : continuousUnitCohomology K S 2 ≃+ continuousUnitCohomology K T 2 :=
  (brauerContinuousEquiv K S).symm.trans (brauerContinuousEquiv K T)

/-- The canonical identification agrees with the actual cohomology map
induced by any embedding of the two separable closures. -/
theorem cohomologyClosureEquiv_apply (i : S →ₐ[K] T) (x : continuousUnitCohomology K S 2) :
    cohomologyClosureEquiv K S T x = restrictionForEmbedding K K S T i x := by
  obtain ⟨a, rfl⟩ := (brauerContinuousEquiv K S).surjective x
  rw [restrictionForEmbedding_comparison, Brauer.scalarExtension_self]
  change brauerContinuousEquiv K T ((brauerContinuousEquiv K S).symm
    (brauerContinuousEquiv K S a)) = brauerContinuousEquiv K T a
  rw [AddEquiv.symm_apply_apply]

@[simp] theorem cohomologyClosureEquiv_comparison (a : BrauerGroup.{u, u} K) :
    cohomologyClosureEquiv K S T (brauerContinuousEquiv K S a) = brauerContinuousEquiv K T a := by
  change brauerContinuousEquiv K T ((brauerContinuousEquiv K S).symm
    (brauerContinuousEquiv K S a)) = _
  rw [AddEquiv.symm_apply_apply]

variable (U : Type u) [Field U] [Algebra K U] [IsSepClosure K U]

/-- Changing the separable closure twice gives the direct identification. -/
theorem cohomologyClosureEquiv_trans :
    (cohomologyClosureEquiv K S T).trans (cohomologyClosureEquiv K T U) =
      cohomologyClosureEquiv K S U := by
  ext x
  obtain ⟨a, rfl⟩ := (brauerContinuousEquiv K S).surjective x
  simp only [AddEquiv.trans_apply, cohomologyClosureEquiv_comparison]

end ClosureChoice

/-- Restriction commutes with the canonical identifications for two choices
of the source and target separable closures. -/
theorem restrictionForEmbedding_change_closures
    (K E S S' T T' : Type u) [Field K] [Field E] [Field S] [Field S'] [Field T] [Field T']
    [Algebra K E] [Algebra K S] [Algebra K S'] [Algebra E T] [Algebra E T']
    [Algebra K T] [Algebra K T'] [IsScalarTower K E T] [IsScalarTower K E T']
    [IsSepClosure K S] [IsSepClosure K S'] [IsSepClosure E T] [IsSepClosure E T']
    (i : S →ₐ[K] T) (i' : S' →ₐ[K] T') (x : continuousUnitCohomology K S 2) :
    cohomologyClosureEquiv E T T' (restrictionForEmbedding K E S T i x) =
      restrictionForEmbedding K E S' T' i' (cohomologyClosureEquiv K S S' x) := by
  obtain ⟨a, rfl⟩ := (brauerContinuousEquiv K S).surjective x
  simp only [restrictionForEmbedding_comparison, cohomologyClosureEquiv_comparison]

/-- Canonical restriction for Mathlib's separable closures, with the extension
of the embedding chosen by the separably closed target field. -/
def separableRestriction (K E : Type u) [Field K] [Field E] [Algebra K E] :
    separableH2 K →+ separableH2 E := by
  let : Algebra K (SeparableClosure E) :=
    ((algebraMap E (SeparableClosure E)).comp (algebraMap K E)).toAlgebra
  have : IsScalarTower K E (SeparableClosure E) := IsScalarTower.of_algebraMap_eq' rfl
  exact restrictionForEmbedding K E (SeparableClosure K) (SeparableClosure E) IsSepClosed.lift

/-- Canonical scalar-extension naturality for Mathlib's two separable closures. -/
theorem brauerEquiv_scalarExtension (K E : Type u) [Field K] [Field E] [Algebra K E]
    (a : BrauerGroup.{u, u} K) :
    brauerEquiv E (Brauer.scalarExtension E a) = separableRestriction K E (brauerEquiv K a) := by
  let : Algebra K (SeparableClosure E) :=
    ((algebraMap E (SeparableClosure E)).comp (algebraMap K E)).toAlgebra
  have : IsScalarTower K E (SeparableClosure E) := IsScalarTower.of_algebraMap_eq' rfl
  exact (restrictionForEmbedding_comparison K E (SeparableClosure K) (SeparableClosure E)
    IsSepClosed.lift a).symm

end Langlands.BrauerComparison
