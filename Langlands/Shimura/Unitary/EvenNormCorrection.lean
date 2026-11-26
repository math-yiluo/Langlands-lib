import Langlands.Shimura.Unitary.SymmetricProfileElement
import Langlands.Shimura.Unitary.FiniteNormTwist
import Langlands.Shimura.Unitary.QuadraticNormProfileDescent
import Langlands.Shimura.Unitary.PositiveSymmetricTwist
import Langlands.Global.Arithmetic.SplitFieldGenerator

/-! # Correcting an even finite set of signed determinant defects -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra _root_.Polynomial Langlands.CentralSimple
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.LocalClassField
open scoped TensorProduct FiniteExtension

universe u v

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n) (he : Even n)
  (s S : Finset (Langlands.Global.FinitePlace E))
  (hz : ∀ p ∉ s, ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)
  (hS : ∀ p ∈ S, ¬ IsSplitPlace E K p) (hdisj : Disjoint S s) (hcard : Even S.card)
  (hprofile : ∀ (p : Langlands.Global.FinitePlace E) (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p),
    (nonsplitSignedDeterminant p hp D hn (hz p hps)).val ∈
      normSubgroup (FiniteCompletion E p) (FiniteCompletion K (placeAbove K p).val) ↔ p ∉ S)
  (r : (E →+* ℝ) → ℕ) (hr : ∀ τ, HasSignature D.toSecondKindInvolution τ n (r τ))

attribute [local instance] FiniteExtension.local_finite

set_option maxRecDepth 8192 in
include hn he hz hS hdisj hcard hprofile hr in
private theorem exists_evenNormCorrection :
    ∃ t : Aˣ, ∃ ht : D.involution (t : A) = t,
      (∀ τ, HasSignature (D.toSecondKindInvolution.twist t ht) τ n (r τ)) ∧
      (∀ p ∉ s, IsQuasiSplitAt (D.toSecondKindInvolution.twist t ht) n p) := by
  classical
  let x := symmetricProfileElement D s S hS hz hdisj
  obtain ⟨hx, hxi, hp₀, hreal⟩ := x.property
  let f := (symmetricReducedCharpoly D hx).val
  have hf : f.Monic := symmetricReducedCharpoly_monic D hx
  have hdeg : f.natDegree = n := symmetricReducedCharpoly_natDegree D hx
  let : Fact (Irreducible f) := ⟨symmetricReducedCharpoly_irreducible D hx hxi⟩
  let : Fact (Irreducible (f.map (algebraMap E K))) :=
    ⟨(symmetricReducedCharpoly D hx).property.symm ▸ hxi⟩
  let F := symmetricRootField K f
  let M := AdjoinRoot (f.map (algebraMap E K))
  let : NumberField F := symmetricRootField_numberField K f hf
  let : FiniteDimensional K M := (hf.map (algebraMap E K)).finite_adjoinRoot
  let : NumberField M := NumberField.of_module_finite K M
  let : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  let : IsQuadraticExtension F M := symmetricRootField_quadratic K f hf
  let e := symmetricRootFieldEquiv K f
  let b : F := e (AdjoinRoot.root f)
  have hgen (y : F) : ∃ g : E[X], aeval b g = y := by
    obtain ⟨z, hz⟩ := e.surjective y
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨g, ?_⟩
    change aeval (e.toAlgHom (AdjoinRoot.root f)) g = y
    rw [aeval_algHom_apply e.toAlgHom, AdjoinRoot.aeval_eq]
    exact hz
  have hb : aeval b f = 0 := by
    change aeval (e.toAlgHom (AdjoinRoot.root f)) f = 0
    rw [aeval_algHom_apply e.toAlgHom, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  let : IsTotallyReal F := totallyReal_of_splitGenerator hgen hb hf.ne_zero hreal
  have hsplit (p : Langlands.Global.FinitePlace E) (hp : p ∈ S) :
      Module.finrank (FiniteCompletion E p) (FiniteCompletion F (placeAbove F p).val) = 1 := by
    let J := completionEquivOfSplitGenerator hgen hb hf.ne_zero p (placeAbove F p) (hp₀ p hp)
    exact J.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self _)
  let t := positiveQuadraticNormProfileDescend (K := K) (M := M) S hS hcard hsplit
  let ha := symmetricReducedCharpoly_aeval D hx
  let g := rootAlgebraEvaluation ha
  let i : F →ₐ[E] A := (g.restrictScalars E).comp (symmetricRootField K f).val
  have hi (y : F) : D.involution (i y) = i y := rootAlgebraEvaluation_symmetric D.involution hx ha y
  let u := Units.map i.toMonoidHom t.val
  have hu : D.involution (u : A) = u := hi (t.val : F)
  let D' : CentralSimpleUnitaryData E K A n :=
    { D with toSecondKindInvolution := D.toSecondKindInvolution.twist u hu }
  let d := normUnits E F t.val
  have hred : reducedNorm K A K (1 ⊗ₜ[K] (u : A)) = algebraMap E K (d : E) :=
    reducedNorm_symmetricRootField D hf hdeg ha (t.val : F)
  refine ⟨u, hu, fun τ => ?_, fun p hp => ?_⟩
  · exact hasSignature_twist_of_positive D.toSecondKindInvolution i hi t.val
      (fun q => t.property.1 q (IsTotallyReal.isReal q)) τ (hr τ)
  · by_cases hsplit : IsSplitPlace E K p
    · exact hsplit.some.isQuasiSplitAt_of_zeroCompletedBrauerInvariant (placeAbove K p) D'
        (hz p hp (placeAbove K p))
    · have h := (hprofile p hp hsplit).trans (t.property.2 p hsplit).symm
      let W := maximalWittChartOfNormTwist p hsplit D hn (hz p hp) u hu he d hred h
      exact ⟨W.val, W.property⟩

set_option maxRecDepth 8192 in
/-- Correct a supplied even finite set of signed determinant norm defects by
one symmetric unit, retaining all prescribed real signature charts. -/
def evenNormCorrection :
    {t : Aˣ // ∃ ht : D.involution (t : A) = t,
      (∀ τ, HasSignature (D.toSecondKindInvolution.twist t ht) τ n (r τ)) ∧
      (∀ p ∉ s, IsQuasiSplitAt (D.toSecondKindInvolution.twist t ht) n p)} :=
  let h := exists_evenNormCorrection D hn he s S hz hS hdisj hcard hprofile r hr
  ⟨h.choose, h.choose_spec⟩

end Langlands.Shimura.FiniteUnitary
