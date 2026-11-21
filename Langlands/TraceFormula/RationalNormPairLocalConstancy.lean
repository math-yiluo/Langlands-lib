import Langlands.BaseChange.ConcordanceRingEquiv
import Langlands.BaseChange.NormNeighbourhood
import Langlands.TraceFormula.RationalNormPairApproximation
import Mathlib.Topology.LocallyConstant.Basic

/-! # Rational approximation preserving local comparison at a distinguished place -/

noncomputable section

namespace Langlands.TraceFormula

open BaseChange Global JacquetLanglands _root_.Topology
open scoped PlaceCompletion

universe w u v

variable (K L : Type w) [Field K] [Field L] [NumberField K] [Algebra K L]

set_option hygiene false in
local notation "Fᵥ" => FiniteCompletion K v

set_option hygiene false in
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (.inr v)

local instance (v : FinitePlace K) : Algebra Fᵥ Eᵥ :=
  LocalBaseChangeAlgebra.algebra K L (.inr v)

set_option hygiene false in
local notation "θ" => localGalois K L

set_option hygiene false in
local notation "upperAt" => fun (p : FinitePlace K) (x : GeneralLinear n L) =>
  Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr p)).toRingHom x

set_option hygiene false in
local notation "lowerAt" => fun (p : FinitePlace K) (x : GeneralLinear n K) =>
  Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K p)) x

/-- One rational norm pair can meet all the supplied finite-place neighbourhoods
while retaining the value of a locally constant predicate at the distinguished
regular associated pair in isomorphic local coordinates. -/
def RationalNormPairLocalConstancyStatement : Prop :=
  ∀ (K L : Type w) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σK : L ≃ₐ[K] L) (l n : ℕ),
    IsCyclicAlgebra σK l →
    ∀ (S : Finset (FinitePlace K)) (v₀ : S),
    ∀ (δ₀ : ∀ v : S, GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v.val)))
      (γ₀ : ∀ v : S, GeneralLinear n (FiniteCompletion K v.val)),
      (∀ v, IsNormAssociated (θ σK (.inr v.val)) l (δ₀ v) (γ₀ v)) →
      (∀ v, IsRegularSemisimple (γ₀ v)) →
    ∀ (F : Type u) [Field F] [CharZero F] [TopologicalSpace F] [ValuativeRel F]
      [IsNonarchimedeanLocalField F]
      (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
      [IsModuleTopology F E] (σ : E ≃ₐ[F] E), IsCyclicAlgebra σ l →
      ∀ (eF : FiniteCompletion K v₀.val ≃+* F)
        (eE : LocalBaseChangeAlgebra K L (.inr v₀.val) ≃+* E)
        (heF : Continuous eF) (heF' : Continuous eF.symm)
        (heE : Continuous eE) (heE' : Continuous eE.symm),
        (∀ a : FiniteCompletion K v₀.val, eE (algebraMap _ _ a) = algebraMap F E (eF a)) →
        (∀ a, eE (θ σK (.inr v₀.val) a) = σ (eE a)) →
      ∀ (P : GeneralLinear n E → GeneralLinear n F → Prop),
        (let D := {q : GeneralLinear n E × GeneralLinear n F //
          IsNormAssociated σ l q.1 q.2 ∧ IsRegularSemisimple q.2}
         IsLocallyConstant (fun q : D => P q.val.1 q.val.2)) →
      ∀ (U : ∀ v : S, Set (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v.val))))
        (V : ∀ v : S, Set (GeneralLinear n (FiniteCompletion K v.val))),
        (∀ v, U v ∈ nhds (δ₀ v)) → (∀ v, V v ∈ nhds (γ₀ v)) →
        let κF := generalLinearRingEquiv (n := n) eF heF heF'
        let κE := generalLinearRingEquiv (n := n) eE heE heE'
        ∃ (δ : GeneralLinear n L) (γ : GeneralLinear n K),
          IsNormAssociated σK l δ γ ∧ IsRegularSemisimple γ ∧
          (∀ v : S, upperAt v.val δ ∈ U v ∧ lowerAt v.val γ ∈ V v) ∧
          (P (κE (upperAt v₀.val δ)) (κF (lowerAt v₀.val γ)) ↔ P (κE (δ₀ v₀)) (κF (γ₀ v₀)))

set_option maxHeartbeats 1400000 in
theorem rationalNormPairLocalConstancy : RationalNormPairLocalConstancyStatement.{w, u, v} := by
  classical
  intro K L _ _ _ _ _ _ σK l n hσK S v₀ δ₀ γ₀ hAssoc hReg F _ _ _ _ _
    E _ _ _ _ _ σ hσ eF eE heF heF' heE heE' hι hθ P hP U V hU hV
  let κF := generalLinearRingEquiv (n := n) eF heF heF'
  let κE := generalLinearRingEquiv (n := n) eE heE heE'
  let D := {q : GeneralLinear n E × GeneralLinear n F //
    IsNormAssociated σ l q.1 q.2 ∧ IsRegularSemisimple q.2}
  have hTransport (δ : GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v₀.val)))
      (γ : GeneralLinear n (FiniteCompletion K v₀.val)) :
      IsNormAssociated σ l (κE δ) (κF γ) ↔
        IsNormAssociated (θ σK (.inr v₀.val)) l δ γ :=
    generalLinearRingEquiv_isNormAssociated_iff eF eE heF heF' heE heE' hι hθ δ γ
  have hAssoc₀ := (hTransport (δ₀ v₀) (γ₀ v₀)).2 (hAssoc v₀)
  have hReg₀ := (generalLinearRingEquiv_isRegularSemisimple_iff eF heF heF' (γ₀ v₀)).2 (hReg v₀)
  let q₀ : D := ⟨(κE (δ₀ v₀), κF (γ₀ v₀)), hAssoc₀, hReg₀⟩
  obtain ⟨W, hWo, hq₀W, hW⟩ := hP.exists_open q₀
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hWo
  have hq₀O : (κE (δ₀ v₀), κF (γ₀ v₀)) ∈ O := hq₀W
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hO.mem_nhds hq₀O)
  let R := {γ : GeneralLinear n F | IsRegularSemisimple γ ∧ IsNorm σ l γ}
  have hR : IsOpen R := ((normNeighbourhood F n).2 E σ l hσ).2
  have hR₀ : κF (γ₀ v₀) ∈ R := ⟨hReg₀, κE (δ₀ v₀), hAssoc₀⟩
  let U' := Function.update U v₀ (U v₀ ∩ κE ⁻¹' A)
  let V' := Function.update V v₀ (V v₀ ∩ κF ⁻¹' (B ∩ R))
  have hU' (v : S) : U' v ∈ nhds (δ₀ v) := by
    by_cases hv : v = v₀
    · subst v
      simp only [U', Function.update_self]
      exact Filter.inter_mem (hU v₀) (κE.continuous.continuousAt.preimage_mem_nhds hA)
    · simpa only [U', Function.update_of_ne hv] using hU v
  have hV' (v : S) : V' v ∈ nhds (γ₀ v) := by
    by_cases hv : v = v₀
    · subst v
      simp only [V', Function.update_self]
      exact Filter.inter_mem (hV v₀) (κF.continuous.continuousAt.preimage_mem_nhds
        (Filter.inter_mem hB (hR.mem_nhds hR₀)))
    · simpa only [V', Function.update_of_ne hv] using hV v
  obtain ⟨δ, γ, hδγ, hmem⟩ :=
    rationalNormPairApproximation K L σK l n hσK S δ₀ γ₀ hAssoc hReg U' V' hU' hV'
  have hmem₀ : upperAt v₀.val δ ∈ U v₀ ∩ κE ⁻¹' A ∧
      lowerAt v₀.val γ ∈ V v₀ ∩ κF ⁻¹' (B ∩ R) := by
    simpa only [U', V', Function.update_self] using hmem v₀
  have hAssoc' := (hTransport _ _).2 (localize_normAssociated K L σK l n
    (.inr v₀.val) δ γ hδγ)
  have hReg' : IsRegularSemisimple (κF (lowerAt v₀.val γ)) := hmem₀.2.2.2.1
  have hRegLocal := (generalLinearRingEquiv_isRegularSemisimple_iff eF heF heF'
    (lowerAt v₀.val γ)).1 hReg'
  have hRegK : IsRegularSemisimple γ := by
    apply (Polynomial.separable_map (algebraMap K (FiniteCompletion K v₀.val))).1
    rw [← Matrix.charpoly_map]
    exact hRegLocal
  let q : D := ⟨(κE (upperAt v₀.val δ), κF (lowerAt v₀.val γ)), hAssoc', hReg'⟩
  have hq : q ∈ Subtype.val ⁻¹' O := hAB ⟨hmem₀.1.2, hmem₀.2.2.1⟩
  refine ⟨δ, γ, hδγ, hRegK, ?_, Iff.of_eq (hW q hq)⟩
  intro v
  by_cases hv : v = v₀
  · subst v
    exact ⟨hmem₀.1.1, hmem₀.2.1⟩
  · simpa only [U', V', Function.update_of_ne hv] using hmem v

end Langlands.TraceFormula
