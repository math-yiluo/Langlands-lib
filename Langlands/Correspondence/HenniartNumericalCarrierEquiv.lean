import Langlands.Correspondence.HenniartNumericalStatement
import Langlands.Representation.Classification.SupercuspidalCarrierEquiv

/-!
# Changing the supercuspidal carrier of numerical injections

Reindexing supercuspidal classes preserves the first fixed level and commutes
with determinant twists. Postcomposition then compares numerical injections
at different supercuspidal carrier universes, including surjectivity.
-/

noncomputable section

namespace Langlands

universe uK uW uV uX

namespace PadicField.TopologicalData

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uK} p} (T : K.TopologicalData)

/-- Changing the carrier of a supercuspidal class commutes with an open-kernel
twist by a character of the determinant. -/
theorem supercuspidalClassCarrierEquiv_twist (n : ℕ) :
    letI := T.topology
    ∀ (χ : GeneralLinear n K.Carrier →* ℂˣ)
      (hχ : IsOpen (χ.ker : Set (GeneralLinear n K.Carrier)))
      (hdet : (determinant : GeneralLinear n K.Carrier →* K.Carrierˣ).ker ≤ χ.ker)
      (a : GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := n)),
      T.supercuspidalClassCarrierEquiv.{uK, uV, uX} n (SupercuspidalClass.twist χ hχ hdet a) =
        SupercuspidalClass.twist χ hχ hdet (T.supercuspidalClassCarrierEquiv n a) := by
  let := T.topology
  intro χ hχ hdet a
  induction a using Quotient.inductionOn with
  | h A =>
    obtain ⟨B, hB⟩ := Quotient.exists_rep (T.supercuspidalClassCarrierEquiv.{uK, uV, uX} n
      A.isoClass)
    change B.isoClass = T.supercuspidalClassCarrierEquiv n A.isoClass at hB
    obtain ⟨e⟩ := (T.supercuspidalClassCarrierEquiv_isoClass_eq_iff n A B).mp hB.symm
    change T.supercuspidalClassCarrierEquiv n (SupercuspidalClass.twist χ hχ hdet A.isoClass) =
      SupercuspidalClass.twist χ hχ hdet (T.supercuspidalClassCarrierEquiv n A.isoClass)
    rw [← hB, SupercuspidalClass.twist_isoClass, SupercuspidalClass.twist_isoClass]
    exact (T.supercuspidalClassCarrierEquiv_isoClass_eq_iff n
      (SupercuspidalRep.twist χ hχ hdet A) (SupercuspidalRep.twist χ hχ hdet B)).mpr
        ⟨twistEquiv χ e⟩

/-- The first fixed level is preserved across carrier universes, including its
value at infinity. -/
theorem supercuspidalFirstFixedLevel_carrierEquiv (k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    ∀ a : GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := k + 1),
      SupercuspidalClass.firstFixedLevel (T.supercuspidalClassCarrierEquiv.{uK, uV, uX}
        (k + 1) a) = SupercuspidalClass.firstFixedLevel a := by
  let := T.topology
  let := T.valuativeRel
  intro a
  induction a using Quotient.inductionOn with
  | h A =>
    obtain ⟨B, hB⟩ := Quotient.exists_rep (T.supercuspidalClassCarrierEquiv.{uK, uV, uX}
      (k + 1) A.isoClass)
    change B.isoClass = T.supercuspidalClassCarrierEquiv (k + 1) A.isoClass at hB
    obtain ⟨e⟩ := (T.supercuspidalClassCarrierEquiv_isoClass_eq_iff (k + 1) A B).mp hB.symm
    change SupercuspidalClass.firstFixedLevel (T.supercuspidalClassCarrierEquiv (k + 1)
      A.isoClass) = SupercuspidalClass.firstFixedLevel A.isoClass
    rw [← hB]
    exact (Conductor.firstFixedLevel_eq_of_equiv e).symm

end PadicField.TopologicalData

namespace Henniart.Numerical

open Correspondence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

private theorem carrierEquiv_unramifiedTwist (k : ℕ) (z : ℂˣ)
    (a : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    K.canonicalTopologicalData.supercuspidalClassCarrierEquiv.{uK, uV, uX}
        (k + 1) (supercuspidalUnramifiedTwist K k z a) =
      supercuspidalUnramifiedTwist K k z
        (K.canonicalTopologicalData.supercuspidalClassCarrierEquiv (k + 1) a) :=
  K.canonicalTopologicalData.supercuspidalClassCarrierEquiv_twist (k + 1) _ _ _ a

/-- The numerical injection predicate is invariant under changing the
supercuspidal carrier universe. -/
theorem isNumericalInjection_comp_carrierEquiv_iff {k : ℕ}
    (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    IsNumericalInjection K
      (K.canonicalTopologicalData.supercuspidalClassCarrierEquiv.{uK, uV, uX} (k + 1) ∘ φ) ↔
      IsNumericalInjection K φ := by
  let e : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat ≃
      SupercuspidalAutomorphicClass.{uK, uX} K k.succPNat :=
    K.canonicalTopologicalData.supercuspidalClassCarrierEquiv (k + 1)
  change IsNumericalInjection K (e ∘ φ) ↔ IsNumericalInjection K φ
  refine and_congr (e.injective.of_comp_iff φ) (and_congr ?_ ?_)
  · have hconductor (a : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
        conductor K (e a) = conductor K a :=
      K.canonicalTopologicalData.supercuspidalFirstFixedLevel_carrierEquiv k a
    simp only [Function.comp_apply, hconductor]
  · refine forall_congr' fun z => forall_congr' fun σ => ?_
    have htwist : e (supercuspidalUnramifiedTwist K k z (φ σ)) =
        supercuspidalUnramifiedTwist K k z (e (φ σ)) :=
      carrierEquiv_unramifiedTwist K k z (φ σ)
    change e (φ (weilUnramifiedTwist K k z σ)) = supercuspidalUnramifiedTwist K k z (e (φ σ)) ↔ _
    rw [← htwist]
    exact e.injective.eq_iff

/-- At a fixed rank and Weil carrier universe, postcomposing with the class
bijection identifies the numerical injections in any two supercuspidal
carrier universes. -/
def numericalInjectionCarrierEquiv (k : ℕ) :
    {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat // IsNumericalInjection K φ} ≃
    {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uX} K k.succPNat // IsNumericalInjection K φ} :=
  (Equiv.arrowCongr (Equiv.refl _)
    (K.canonicalTopologicalData.supercuspidalClassCarrierEquiv (k + 1))).subtypeEquiv
      fun φ => (isNumericalInjection_comp_carrierEquiv_iff K φ).symm

/-- A numerical injection is surjective exactly when its transported injection
is surjective. -/
theorem surjective_numericalInjectionCarrierEquiv_iff {k : ℕ}
    (φ : {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat // IsNumericalInjection K φ}) :
    Function.Surjective ((numericalInjectionCarrierEquiv.{uK, uW, uV, uX} K k) φ).val ↔
      Function.Surjective φ.val := by
  let e := K.canonicalTopologicalData.supercuspidalClassCarrierEquiv.{uK, uV, uX} (k + 1)
  change Function.Surjective (e ∘ φ.val) ↔ Function.Surjective φ.val
  exact ⟨fun h => h.of_comp_left e.injective, fun h => e.surjective.comp h⟩

end Henniart.Numerical

namespace Henniart

open Correspondence Numerical

/-- The numerical surjectivity proposition is independent of the choice of
supercuspidal carrier universe. -/
theorem numericalSurjectivity_carrierEquiv_iff :
    NumericalSurjectivityStatement.{uK, uW, uV} ↔
      NumericalSurjectivityStatement.{uK, uW, uX} := by
  constructor
  · intro h p hp K k φ hφ
    let e := numericalInjectionCarrierEquiv.{uK, uW, uV, uX} K k
    let ψ := e.symm ⟨φ, hφ⟩
    have hs : Function.Surjective ψ.val := h p K k ψ.val ψ.property
    have ht : Function.Surjective (e ψ).val :=
      (surjective_numericalInjectionCarrierEquiv_iff K ψ).mpr hs
    have hψ : e ψ = ⟨φ, hφ⟩ := e.apply_symm_apply _
    exact Eq.mp (congrArg (fun a => Function.Surjective a.val) hψ) ht
  · intro h p hp K k φ hφ
    let ψ := numericalInjectionCarrierEquiv.{uK, uW, uV, uX} K k ⟨φ, hφ⟩
    exact (surjective_numericalInjectionCarrierEquiv_iff K ⟨φ, hφ⟩).mp
      (h p K k ψ.val ψ.property)

end Henniart

end Langlands
