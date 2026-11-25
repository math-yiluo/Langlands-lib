import Langlands.Algebra.NumberFieldBrauerProfileDegree
import Langlands.ClassFieldTheory.Local.PadicBrauerInvariantComparison
import Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof
import Langlands.LocalField.LocalFieldData

/-! # Realization of finite Brauer profiles over totally complex number fields -/

noncomputable section

universe u

namespace Langlands.BrauerComparison

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Local Langlands.LocalField
open Langlands.Brauer Langlands.CentralSimple
open scoped FiniteExtension TensorProduct

private theorem localFieldData_eq {K : Type u} [Field K] (D₁ D₂ : LocalFieldData K)
    (ht : D₁.topology = D₂.topology) (hv : D₁.valuativeRel = D₂.valuativeRel) :
    D₁ = D₂ := by
  cases D₁
  cases D₂
  cases ht
  cases hv
  rfl

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L]
  [Algebra F L] [IsGalois F L]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

set_option maxHeartbeats 800000 in
/-- The chart value agrees with the Brauer invariant for the original completion topology
and normalized completion valuation. -/
theorem finiteRelativeBrauerInvariant_eq_localBrauerInvariant
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hA : ∀ (p : ℕ) [Fact p.Prime], (I p).ArithmeticNormalization)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    {A : CSA.{u, u} F}
    (e : L ⊗[F] A ≃ₐ[L] Matrix (Fin (reducedDegree F A)) (Fin (reducedDegree F A)) L)
    (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] :
    letI := FiniteCompletion.valuativeRel v
    letI := FiniteCompletion.isNonarchimedeanLocalField v
    finiteRelativeBrauerInvariant I e v w =
      localBrauerInvariant (FiniteCompletion F v) (classOf (baseChange (FiniteCompletion F v) A)) := by
  let K := FiniteCompletion F v
  let M := FiniteCompletion L w
  let P := padicField v
  let B := baseChange K A
  let J := Fin (reducedDegree F A)
  let : Nonempty J := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  let f : M ⊗[K] B ≃ₐ[M] Matrix J J M := baseChangeSplittingChart K M e
  let D₁ : LocalFieldData K :=
    { topology := P.canonicalTopologicalData.topology
      valuativeRel := P.canonicalTopologicalData.valuativeRel
      localField := P.canonicalTopologicalData.localField }
  let D₂ : LocalFieldData K :=
    { topology := inferInstanceAs (TopologicalSpace (FiniteCompletion F v))
      valuativeRel := FiniteCompletion.valuativeRel v
      localField := FiniteCompletion.isNonarchimedeanLocalField v }
  have hD : D₁ = D₂ := localFieldData_eq D₁ D₂ (completion_topology_eq v).symm
    (FiniteCompletion.topologicalData_valuativeRel_eq v)
  let value (D : LocalFieldData K) : RationalModIntegers :=
    letI := D.topology
    letI := D.valuativeRel
    letI := D.localField
    localBrauerInvariant K (classOf B)
  change finiteRelativeBrauerInvariant I e v w = value D₂
  calc
    _ = value D₁ := relativeInvariant_eq_localBrauerInvariant P (I (residuePrime v))
      (hA _) (hInf _) M B f
    _ = _ := congrArg value hD

end Langlands.BrauerComparison

namespace Langlands.Brauer

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local Langlands.BrauerComparison

/-- An actual degree-`n` CSA over a totally complex number field with
prescribed finite Brauer invariant values. -/
def NumberFieldBrauerProfileRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    (S : Finset (Langlands.Global.FinitePlace F)) (a : Langlands.Global.FinitePlace F →
      RationalModIntegers), (∀ v ∉ S, a v = 0) →
    ∀ (n : ℕ), 0 < n → (∀ v ∈ S, n • a v = 0) → (∑ v ∈ S, a v = 0) →
      ∃ A : CSA.{u, u} F, Module.finrank F A = n * n ∧
        ∀ v : Langlands.Global.FinitePlace F,
          letI := FiniteCompletion.valuativeRel v
          letI := FiniteCompletion.isNonarchimedeanLocalField v
          localBrauerInvariant (FiniteCompletion F v)
            (classOf (baseChange (FiniteCompletion F v) A)) = a v

theorem numberFieldBrauerProfileRealization : NumberFieldBrauerProfileRealizationStatement.{u} := by
  intro F _ _ _ S a ha₀ n hn ha hsum
  let I (p : ℕ) [Fact p.Prime] := localInvariantFamily unramifiedH2Exhaustion.{u} p
  have hCF (p : ℕ) [Fact p.Prime] : (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    ⟨FiniteArtinTransferReduction.canonicalClassFormation,
      localInvariantFamilyArithmetic unramifiedH2Exhaustion p⟩
  obtain ⟨L, _, _, _, _, A, e, hdim, h⟩ :=
    exists_csa_degree_with_finiteRelativeInvariants F I hCF S a ha₀ n hn ha hsum
  refine ⟨A, hdim, fun v => ?_⟩
  exact (finiteRelativeBrauerInvariant_eq_localBrauerInvariant I
    (fun p _ => (hCF p).2) (fun p _ => (hCF p).1.2.2.1)
    e v (placeAbove L v).val).symm.trans (h v)

end Langlands.Brauer
