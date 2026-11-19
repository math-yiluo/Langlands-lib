import Langlands.Algebra.BrauerComparison.FiniteInflationInjective
import Langlands.Algebra.BrauerComparison.BaseChangeChart
import Langlands.Algebra.BrauerComparison.RelativeLaws
import Langlands.Algebra.BrauerComparison.RegularClass
import Langlands.Algebra.BrauerComparison.SeparableRestriction
import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting

/-! # The Brauer group and the continuous cohomology of separable-closure units -/

noncomputable section

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u v w

namespace Langlands.BrauerComparison

open CentralSimple ClassFieldTheory.Local

attribute [local instance] Classical.decEq

variable (K : Type u) [Field K]

local instance (A : CSA.{u, u} K) : Nonempty (Fin (reducedDegree K A)) :=
  Fin.pos_iff_nonempty.mp (reducedDegree_pos K A)

variable (S : Type u) [Field S] [Algebra K S] [IsSepClosure K S]

/-- Every actual central simple algebra has a finite Galois splitting stage
inside any chosen separable closure. -/
theorem exists_separableSplittingChart (A : CSA.{u, u} K) :
    ∃ F : FiniteGaloisIntermediateField K S,
      Nonempty (F ⊗[K] A ≃ₐ[F] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) F) := by
  let L := finiteGaloisSplittingField K A
  have : IsSepClosed S := IsSepClosure.sep_closed K
  let i : L →ₐ[K] S := IsSepClosed.lift
  obtain ⟨F, j, _⟩ := exists_finiteStage_containing (E := K) i
  let : Algebra L F := j.toRingHom.toAlgebra
  have : IsScalarTower K L F := IsScalarTower.of_algHom j
  exact ⟨F, ⟨enlargedSplittingChart (A := A) (I := Fin (reducedDegree K A)) F
    (finiteGaloisSplittingChart K A)⟩⟩

/-- A finite Galois splitting stage in the chosen closure. -/
def separableSplittingStage (A : CSA.{u, u} K) : FiniteGaloisIntermediateField K S :=
  (exists_separableSplittingChart K S A).choose

/-- An actual matrix splitting over the chosen stage. -/
def separableSplittingChart (A : CSA.{u, u} K) :
    separableSplittingStage K S A ⊗[K] A ≃ₐ[separableSplittingStage K S A]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) (separableSplittingStage K S A) :=
  (exists_separableSplittingChart K S A).choose_spec.some

section Extension

variable {K S} {F G : FiniteGaloisIntermediateField K S} {A : CSA.{u, u} K}
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

private def enlargeFiniteChart (h : F ≤ G) (e : F ⊗[K] A ≃ₐ[F] Matrix I I F) :
    G ⊗[K] A ≃ₐ[G] Matrix I I G := by
  let j : F →ₐ[K] G := IntermediateField.inclusion h
  let : Algebra F G := j.toRingHom.toAlgebra
  have : IsScalarTower K F G := IsScalarTower.of_algHom j
  exact enlargedSplittingChart (A := A) (I := I) G e

omit [IsSepClosure K S] in
private theorem inflatedClass_enlarge (h : F ≤ G)
    (e : F ⊗[K] A ≃ₐ[F] Matrix I I F) :
    relativeToContinuous K G S 2 (relativeClass (enlargeFiniteChart (A := A) (I := I) h e)) =
      relativeToContinuous K F S 2 (relativeClass e) := by
  let j : F →ₐ[K] G := IntermediateField.inclusion h
  let : Algebra F G := j.toRingHom.toAlgebra
  have : IsScalarTower K F G := IsScalarTower.of_algHom j
  have : IsScalarTower F G S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change relativeToContinuous K G S 2
    (relativeClass (enlargedSplittingChart (A := A) (I := I) G e)) = _
  rw [relativeClass_enlargedSplittingChart (A := A) (I := I) G e,
    relativeToContinuous_tower K F G S]

omit [IsSepClosure K S] in
private theorem inflatedClass_eq_of_charts
    {J : Type w} [Fintype J] [DecidableEq J] [Nonempty J]
    (e : F ⊗[K] A ≃ₐ[F] Matrix I I F) (f : G ⊗[K] A ≃ₐ[G] Matrix J J G) :
    relativeToContinuous K F S 2 (relativeClass e) =
      relativeToContinuous K G S 2 (relativeClass f) := by
  let H : FiniteGaloisIntermediateField K S := F ⊔ G
  let e' := enlargeFiniteChart (G := H) (A := A) (I := I) le_sup_left e
  let f' := enlargeFiniteChart (G := H) (A := A) (I := J) le_sup_right f
  calc
    _ = relativeToContinuous K H S 2 (relativeClass e') :=
      (inflatedClass_enlarge (A := A) (I := I) le_sup_left e).symm
    _ = relativeToContinuous K H S 2 (relativeClass f') :=
      congrArg (relativeToContinuous K H S 2) (relativeClass_eq_of_indices e' f')
    _ = _ := inflatedClass_enlarge (A := A) (I := J) le_sup_right f

end Extension

/-- The continuous class of an actual central simple algebra, computed on a
finite Galois matrix splitting. -/
def csaContinuousClass (A : CSA.{u, u} K) : continuousUnitCohomology K S 2 :=
  relativeToContinuous K (separableSplittingStage K S A) S 2
    (relativeClass (separableSplittingChart K S A))

/-- Every chart on a finite Galois intermediate field computes the same continuous class. -/
theorem csaContinuousClass_at_stage (A : CSA.{u, u} K) (F : FiniteGaloisIntermediateField K S)
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : F ⊗[K] A ≃ₐ[F] Matrix I I F) :
    csaContinuousClass K S A = relativeToContinuous K F S 2 (relativeClass e) :=
  inflatedClass_eq_of_charts (A := A) (I := Fin (reducedDegree K A)) (J := I)
    (separableSplittingChart K S A) e

/-- An arbitrary finite Galois splitting field embedded in the closure computes
its continuous class by the actual relative inflation map. -/
theorem csaContinuousClass_at_chart (A : CSA.{u, u} K) (L : Type u) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L S] [IsScalarTower K L S]
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    csaContinuousClass K S A = relativeToContinuous K L S 2 (relativeClass e) := by
  obtain ⟨F, j, hj⟩ := exists_finiteStage_containing (E := K) (IsScalarTower.toAlgHom K L S)
  let : Algebra L F := j.toRingHom.toAlgebra
  have : IsScalarTower K L F := IsScalarTower.of_algHom j
  have : IsScalarTower L F S := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  rw [← relativeToContinuous_tower K L F S 2 (relativeClass e),
    ← relativeClass_enlargedSplittingChart (A := A) (I := I) F e]
  exact csaContinuousClass_at_stage K S A F (enlargedSplittingChart (A := A) (I := I) F e)

private theorem csaContinuousClass_eq_zero_of_split (A : CSA.{u, u} K) (h : Brauer.IsSplit A) :
    csaContinuousClass K S A = 0 := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let F := separableSplittingStage K S A
  rw [csaContinuousClass_at_stage K S A F (splitPresentationChart (L := F) f),
    relativeClass_eq_zero_of_split _ f, map_zero]

private theorem csaContinuousClass_eq_of_equivalent (A B : CSA.{u, u} K) (h : IsBrauerEquivalent A B) :
    csaContinuousClass K S A = csaContinuousClass K S B := by
  let F := separableSplittingStage K S A ⊔ separableSplittingStage K S B
  let e := enlargeFiniteChart (G := F) (A := A) (I := Fin (reducedDegree K A))
    le_sup_left (separableSplittingChart K S A)
  let f := enlargeFiniteChart (G := F) (A := B) (I := Fin (reducedDegree K B))
    le_sup_right (separableSplittingChart K S B)
  rw [csaContinuousClass_at_stage K S A F e, csaContinuousClass_at_stage K S B F f,
    relativeClass_eq_of_brauerEquivalent h e f]

private theorem csaContinuousClass_tensor (A B : CSA.{u, u} K) :
    csaContinuousClass K S (Brauer.tensor A B) = csaContinuousClass K S A + csaContinuousClass K S B := by
  let F := separableSplittingStage K S A ⊔ separableSplittingStage K S B
  let e := enlargeFiniteChart (G := F) (A := A) (I := Fin (reducedDegree K A))
    le_sup_left (separableSplittingChart K S A)
  let f := enlargeFiniteChart (G := F) (A := B) (I := Fin (reducedDegree K B))
    le_sup_right (separableSplittingChart K S B)
  rw [csaContinuousClass_at_stage K S (Brauer.tensor A B) F (tensorSplittingChart e f),
    csaContinuousClass_at_stage K S A F e, csaContinuousClass_at_stage K S B F f]
  exact (congrArg (relativeToContinuous K F S 2) (relativeClass_tensor e f)).trans
    (map_add (relativeToContinuous K F S 2) _ _)

/-- Serre's comparison descends to the actual matrix-stable Brauer quotient
as an additive homomorphism. -/
def brauerContinuousHom : BrauerGroup.{u, u} K →+ continuousUnitCohomology K S 2 where
  toFun := Quotient.lift (csaContinuousClass K S) (csaContinuousClass_eq_of_equivalent K S)
  map_zero' := csaContinuousClass_eq_zero_of_split K S (Brauer.groundField K)
    ⟨1, Nat.one_pos, ⟨(Brauer.matrixOneEquiv K).symm⟩⟩
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    exact csaContinuousClass_tensor K S A B

@[simp] theorem brauerContinuousHom_classOf (A : CSA.{u, u} K) :
    brauerContinuousHom K S (Brauer.classOf A) = csaContinuousClass K S A := rfl

private theorem brauerContinuousHom_injective : Function.Injective (brauerContinuousHom K S) := by
  apply (injective_iff_map_eq_zero _).2
  intro a
  induction a using Quotient.inductionOn with
  | _ A =>
    intro h
    let F := separableSplittingStage K S A
    let e := separableSplittingChart K S A
    have hz : relativeToContinuous K F S 2 (relativeClass e) = 0 := h
    have hc : relativeClass e = 0 := (relativeToContinuous_injective K S F) (hz.trans (map_zero _).symm)
    exact (Brauer.classOf_eq_zero_iff A).2
      ⟨reducedDegree K A, reducedDegree_pos K A, split_of_relativeClass_eq_zero e hc⟩

private theorem brauerContinuousHom_surjective : Function.Surjective (brauerContinuousHom K S) := by
  intro x
  obtain ⟨F, y, hy⟩ := exists_finiteRelativeToContinuous K S 2 x
  obtain ⟨A, e, he⟩ := exists_relativeClass_eq (K := K) (L := F) y
  refine ⟨Brauer.classOf A, ?_⟩
  rw [brauerContinuousHom_classOf, csaContinuousClass_at_stage K S A F e, he, hy]

/-- The actual Brauer group is isomorphic to continuous degree-two unit
cohomology for any separable closure. -/
def brauerContinuousEquiv : BrauerGroup.{u, u} K ≃+ continuousUnitCohomology K S 2 :=
  AddEquiv.ofBijective (brauerContinuousHom K S)
    ⟨brauerContinuousHom_injective K S, brauerContinuousHom_surjective K S⟩

@[simp] theorem brauerContinuousEquiv_classOf (A : CSA.{u, u} K) :
    brauerContinuousEquiv K S (Brauer.classOf A) = csaContinuousClass K S A := rfl

/-- The Brauer isomorphism takes a split chart to the inflation of Serre's relative class. -/
theorem brauerContinuousEquiv_at_chart (A : CSA.{u, u} K) (L : Type u) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L S] [IsScalarTower K L S]
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    brauerContinuousEquiv K S (Brauer.classOf A) =
      relativeToContinuous K L S 2 (relativeClass e) :=
  csaContinuousClass_at_chart K S A L e

@[simp] theorem brauerContinuousEquiv_tensor (A B : CSA.{u, u} K) :
    brauerContinuousEquiv K S (Brauer.classOf (Brauer.tensor A B)) =
      brauerContinuousEquiv K S (Brauer.classOf A) + brauerContinuousEquiv K S (Brauer.classOf B) := by
  rw [Brauer.classOf_tensor, map_add]

@[simp] theorem brauerContinuousEquiv_opposite (A : CSA.{u, u} K) :
    brauerContinuousEquiv K S (Brauer.classOf (Brauer.opposite A)) =
      -brauerContinuousEquiv K S (Brauer.classOf A) := by
  rw [Brauer.classOf_opposite, map_neg]

@[simp] theorem brauerContinuousEquiv_matrix (n : ℕ) [NeZero n] :
    brauerContinuousEquiv K S (Brauer.classOf (Brauer.matrix (Brauer.groundField K) n)) = 0 := by
  rw [Brauer.classOf_matrix, Brauer.classOf_groundField, map_zero]

/-- The comparison for Mathlib's chosen separable closure. -/
abbrev brauerEquiv : BrauerGroup.{u, u} K ≃+ separableH2 K :=
  brauerContinuousEquiv K (SeparableClosure K)

end Langlands.BrauerComparison
