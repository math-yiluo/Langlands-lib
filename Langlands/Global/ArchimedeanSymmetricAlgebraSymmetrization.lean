import Langlands.Algebra.SymmetricAlgebraEnvelopingSymmetrization
import Langlands.Global.ArchimedeanCartanSymmetricInvariants
import Langlands.Global.ArchimedeanEnvelopingSymmetrization

/-! # Actual whole-algebra symmetrization and conjugation -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Normalized linear symmetrization of the actual whole Lie symmetric algebra. -/
def lieSymmetricAlgebraSymmetrize :
    LieSymmetricAlgebra K n →ₗ[ℂ] EnvelopingAlgebra K n :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize ℂ
    (ComplexLieAlgebra K n)

@[simp] theorem lieSymmetricAlgebraSymmetrize_one :
    lieSymmetricAlgebraSymmetrize K n 1 = 1 :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_one ℂ _

@[simp] theorem lieSymmetricAlgebraSymmetrize_ι (X : ComplexLieAlgebra K n) :
    lieSymmetricAlgebraSymmetrize K n (SymmetricAlgebra.ι ℂ _ X) =
      envelopingGenerator K n X :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_ι ℂ _ X

@[simp] theorem lieSymmetricAlgebraSymmetrize_algebraMap (z : ℂ) :
    lieSymmetricAlgebraSymmetrize K n (algebraMap ℂ (LieSymmetricAlgebra K n) z) =
      algebraMap ℂ (EnvelopingAlgebra K n) z :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_algebraMap ℂ _ z

theorem lieSymmetricAlgebraSymmetrize_prod (l : List (ComplexLieAlgebra K n)) :
    lieSymmetricAlgebraSymmetrize K n ((l.map (SymmetricAlgebra.ι ℂ _)).prod) =
      Langlands.Algebra.UniversalEnveloping.symmetricWord ℂ
        (ComplexLieAlgebra K n) l.length l.get :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_prod ℂ _ l

theorem lieSymmetricAlgebraSymmetrize_prod_mem (l : List (ComplexLieAlgebra K n)) :
    lieSymmetricAlgebraSymmetrize K n ((l.map (SymmetricAlgebra.ι ℂ _)).prod) ∈
      envelopingDegreeFiltration K n l.length :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_prod_mem ℂ _ l

/-- Whole symmetrization intertwines the actual full-group conjugation actions. -/
theorem lieSymmetricAlgebraSymmetrize_conjugation (g : InfiniteAdelicGL K n)
    (P : LieSymmetricAlgebra K n) :
    envelopingConjugation K n g (lieSymmetricAlgebraSymmetrize K n P) =
      lieSymmetricAlgebraSymmetrize K n (lieSymmetricConjugation K n g P) := by
  exact Langlands.Algebra.UniversalEnveloping.map_symmetricAlgebraSymmetrize ℂ
    (ComplexLieAlgebra K n) (envelopingConjugation K n g).toAlgHom
    (complexLieConjugation K n g).toLinearMap (envelopingConjugation_generator K n g) P

/-- Actual enveloping elements fixed by full standard compact conjugation. -/
def envelopingCompactInvariants : Subalgebra ℂ (EnvelopingAlgebra K n) where
  carrier := {a | ∀ k : standardInfiniteCompact K n, envelopingConjugation K n k.val a = a}
  zero_mem' := by intro k; exact map_zero _
  one_mem' := by intro k; exact map_one _
  add_mem' := by intro a b ha hb k; simp only [map_add, ha k, hb k]
  mul_mem' := by intro a b ha hb k; simp only [map_mul, ha k, hb k]
  algebraMap_mem' := by intro z k; exact AlgEquiv.commutes _ z

/-- Actual enveloping elements fixed by every archimedean group element. -/
def envelopingGroupInvariants : Subalgebra ℂ (EnvelopingAlgebra K n) where
  carrier := {a | ∀ g : InfiniteAdelicGL K n, envelopingConjugation K n g a = a}
  zero_mem' := by intro g; exact map_zero _
  one_mem' := by intro g; exact map_one _
  add_mem' := by intro a b ha hb g; simp only [map_add, ha g, hb g]
  mul_mem' := by intro a b ha hb g; simp only [map_mul, ha g, hb g]
  algebraMap_mem' := by intro z g; exact AlgEquiv.commutes _ z

@[simp] theorem mem_envelopingCompactInvariants (a : EnvelopingAlgebra K n) :
    a ∈ envelopingCompactInvariants K n ↔
      ∀ k : standardInfiniteCompact K n, envelopingConjugation K n k.val a = a := Iff.rfl

@[simp] theorem mem_envelopingGroupInvariants (a : EnvelopingAlgebra K n) :
    a ∈ envelopingGroupInvariants K n ↔
      ∀ g : InfiniteAdelicGL K n, envelopingConjugation K n g a = a := Iff.rfl

/-- Compact invariant symmetric tensors map linearly to compact invariant enveloping elements. -/
def lieSymmetricCompactInvariantSymmetrize :
    lieSymmetricCompactInvariants K n →ₗ[ℂ] envelopingCompactInvariants K n :=
  ((lieSymmetricAlgebraSymmetrize K n).comp
    (lieSymmetricCompactInvariants K n).val.toLinearMap).codRestrict
      (envelopingCompactInvariants K n).toSubmodule (by
        intro P k
        change envelopingConjugation K n k.val
          (lieSymmetricAlgebraSymmetrize K n P.val) =
            lieSymmetricAlgebraSymmetrize K n P.val
        rw [lieSymmetricAlgebraSymmetrize_conjugation, P.property k])

/-- Full-group invariant symmetric tensors map linearly to full-group fixed enveloping elements. -/
def lieSymmetricGroupInvariantSymmetrize :
    lieSymmetricGroupInvariants K n →ₗ[ℂ] envelopingGroupInvariants K n :=
  ((lieSymmetricAlgebraSymmetrize K n).comp
    (lieSymmetricGroupInvariants K n).val.toLinearMap).codRestrict
      (envelopingGroupInvariants K n).toSubmodule (by
        intro P g
        change envelopingConjugation K n g
          (lieSymmetricAlgebraSymmetrize K n P.val) =
            lieSymmetricAlgebraSymmetrize K n P.val
        rw [lieSymmetricAlgebraSymmetrize_conjugation, P.property g])

@[simp] theorem lieSymmetricCompactInvariantSymmetrize_coe
    (P : lieSymmetricCompactInvariants K n) :
    (lieSymmetricCompactInvariantSymmetrize K n P : EnvelopingAlgebra K n) =
      lieSymmetricAlgebraSymmetrize K n P.val := rfl

@[simp] theorem lieSymmetricGroupInvariantSymmetrize_coe
    (P : lieSymmetricGroupInvariants K n) :
    (lieSymmetricGroupInvariantSymmetrize K n P : EnvelopingAlgebra K n) =
      lieSymmetricAlgebraSymmetrize K n P.val := rfl

end Langlands.Global.ArchimedeanGL
