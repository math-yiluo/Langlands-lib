import Langlands.Algebra.NumberFieldBrauerSplitting
import Langlands.Algebra.BrauerComparison.AbsoluteComparison
import Langlands.ClassFieldTheory.Global.RelativeFiniteBrauerProfiles
import Langlands.Global.Arithmetic.NumberFieldLocalDegreeMultiples

/-! # Actual central simple algebras for relative finite Brauer profiles -/

noncomputable section

namespace Langlands.BrauerComparison

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Brauer Langlands.CentralSimple
open scoped TensorProduct FiniteExtension

universe u v

attribute [local instance] Classical.decEq

section Torsion

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]
  {A : CSA.{u, u} K} {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]

/-- Annihilation of a chart class implies annihilation of the actual Brauer class. -/
theorem nsmul_classOf_eq_zero_of_relativeClass
    (e : M ⊗[K] A ≃ₐ[M] Matrix J J M) (n : ℕ) (h : n • relativeClass e = 0) :
    n • classOf A = 0 := by
  let j : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let : Algebra M (SeparableClosure K) := j.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom j
  apply (brauerEquiv K).injective
  rw [map_nsmul, map_zero, brauerContinuousEquiv_at_chart K (SeparableClosure K) A M e,
    ← map_nsmul, h, map_zero]

end Torsion

section Relative

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L]
  [Algebra F L] [IsGalois F L]

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
variable {A : CSA.{u, u} F}
  (e : L ⊗[F] A ≃ₐ[L] Matrix (Fin (reducedDegree F A)) (Fin (reducedDegree F A)) L)
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace L)
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- The class-field invariant of the actual completed algebra computed in the scalar-extended
splitting chart. -/
def finiteRelativeBrauerInvariant : RationalModIntegers :=
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  (I (residuePrime v)).relative (padicField v) (FiniteCompletion L w)
    (relativeClass (baseChangeSplittingChart (FiniteCompletion F v) (FiniteCompletion L w) e))

theorem finiteRelativeBrauerInvariant_eq :
    finiteRelativeBrauerInvariant I e v w = Reciprocity.finiteLocalInvariant v w I (relativeClass e) := by
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  exact congrArg ((I (residuePrime v)).relative (padicField v) (FiniteCompletion L w))
    (unitsLocalMap_relativeClass e v w).symm

set_option maxHeartbeats 650000 in
theorem nsmul_classOf_baseChange_eq_zero_of_finiteRelativeBrauerInvariant
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    (n : ℕ) (hn : n • finiteRelativeBrauerInvariant I e v w = 0) :
    n • classOf (baseChange (FiniteCompletion F v) A) = 0 := by
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  let f := baseChangeSplittingChart (FiniteCompletion F v) (FiniteCompletion L w) e
  have h : n • relativeClass f = 0 := by
    apply (hI (residuePrime v) (padicField v) (FiniteCompletion L w)).1
    rw [map_nsmul, map_zero]
    exact hn
  exact nsmul_classOf_eq_zero_of_relativeClass
    (K := FiniteCompletion F v) (M := FiniteCompletion L w)
    (A := baseChange (FiniteCompletion F v) A) (J := Fin (reducedDegree F A)) f n h

/-- A compatible finite profile on a supplied Galois stage gives an actual global CSA and
a splitting chart with the prescribed local invariants. -/
theorem exists_csa_with_finiteRelativeInvariants
    (hCF : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (S : Finset (Langlands.Global.FinitePlace F)) (a : Langlands.Global.FinitePlace F →
      RationalModIntegers) (ha₀ : ∀ v ∉ S, a v = 0)
    (ha : ∀ v ∈ S, a v ∈ denominatorSubgroup
      (Module.finrank (FiniteCompletion F v) (FiniteCompletion L (placeAbove L v).val)))
    (hsum : ∑ v ∈ S, a v = 0) :
    ∃ (A : CSA.{u, u} F)
      (f : L ⊗[F] A ≃ₐ[L] Matrix (Fin (reducedDegree F A)) (Fin (reducedDegree F A)) L),
      ∀ v : Langlands.Global.FinitePlace F,
        finiteRelativeBrauerInvariant I f v (placeAbove L v).val = a v := by
  obtain ⟨x, hx⟩ :=
    exists_relativeCohomology_of_finiteInvariants (F := F) (L := L) I hCF S a ha₀ ha hsum
  obtain ⟨A, e, he⟩ := exists_relativeClass_eq x
  let G := L ≃ₐ[F] L
  let reindex := Fintype.equivFin G
  let f := e.trans (Matrix.reindexAlgEquiv L L reindex)
  have hsize : Fintype.card G = reducedDegree F A := matrix_size_eq_reducedDegree F A L _ f
  let r := reindex.trans (finCongr hsize)
  let f' := e.trans (Matrix.reindexAlgEquiv L L r)
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  have hrel : relativeClass f' = x := (relativeClass_reindex e r).trans he
  exact ⟨A, f', fun v => (finiteRelativeBrauerInvariant_eq I f' v (placeAbove L v).val).trans
    (hrel ▸ hx v)⟩

end Relative

/-- Choose a Galois stage and realize a zero-sum finite profile killed by `n`. -/
theorem exists_csa_with_finiteRelativeInvariants_of_exponent
    {F : Type u} [Field F] [NumberField F]
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hCF : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (S : Finset (Langlands.Global.FinitePlace F)) (a : Langlands.Global.FinitePlace F →
      RationalModIntegers) (ha₀ : ∀ v ∉ S, a v = 0)
    {n : ℕ} (hn : 0 < n) (ha : ∀ v ∈ S, n • a v = 0) (hsum : ∑ v ∈ S, a v = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : IsGalois F L)
      (A : CSA.{u, u} F)
      (f : L ⊗[F] A ≃ₐ[L] Matrix (Fin (reducedDegree F A)) (Fin (reducedDegree F A)) L),
      ∀ v : Langlands.Global.FinitePlace F,
        finiteRelativeBrauerInvariant I f v (placeAbove L v).val = a v := by
  obtain ⟨L, _, _, _, _, hL⟩ := numberFieldLocalDegreeMultiples F S n hn
  have hin (v : Langlands.Global.FinitePlace F) (hv : v ∈ S) :
      a v ∈ denominatorSubgroup
        (Module.finrank (FiniteCompletion F v) (FiniteCompletion L (placeAbove L v).val)) := by
    obtain ⟨m, hm⟩ := hL v hv (placeAbove L v).val
    change Module.finrank (FiniteCompletion F v) (FiniteCompletion L (placeAbove L v).val) • a v = 0
    rw [hm, mul_comm n m, mul_smul, ha v hv, smul_zero]
  obtain ⟨A, f, hf⟩ := exists_csa_with_finiteRelativeInvariants (L := L) I hCF S a ha₀ hin hsum
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, A, f, hf⟩

end Langlands.BrauerComparison
