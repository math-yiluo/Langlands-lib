import Langlands.BaseChange.NormalizedProductEntrywiseAut
import Langlands.BaseChange.SigmaOrbitConjugates
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationForwardFactorsProof
import Langlands.Representation.Filtration.IrreducibleExactComparison

/-! # Sigma-stability of an irreducible supercuspidal orbit product -/

noncomputable section

namespace Langlands.LocalFieldData

open GeneralLinear CuspidalSupport

universe v uW

variable {E : Type v} [Field E] (T : LocalFieldData E)

set_option maxHeartbeats 600000 in
/-- Permuting irreducible supercuspidal factors of an irreducible normalized product
preserves its actual isomorphism class. -/
theorem normalizedProductInduced_equiv_permute_of_irreducible {n : ℕ} (hn : 0 < n)
    (B : BlockShape n) {V : Fin B.length → Type uW}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (V i))
    (hρ : ∀ i, (ρ i).IsIrreducible)
    (hsc : letI := T.topology; ∀ i, IsSupercuspidal (ρ i))
    (h : (T.normalizedProductInduced B ρ).IsIrreducible) (e : Equiv.Perm (Fin B.length)) :
    letI : ∀ i : Fin (B.permute e).length, AddCommGroup (V (e i)) := fun i =>
      inferInstanceAs (AddCommGroup (V (e i)))
    letI : ∀ i : Fin (B.permute e).length, Module ℂ (V (e i)) := fun i =>
      inferInstanceAs (Module ℂ (V (e i)))
    Nonempty (Representation.Equiv (T.normalizedProductInduced B ρ)
      (T.normalizedProductInduced (B.permute e) (fun i => ρ (e i)))) := by
  let := T.topology
  let K := AllFieldBZ.LocalFieldPackage.ofField E
  let T' : K.TopologicalData := T
  let A (i : Fin B.length) : SupercuspidalRep.{v,uW} (F := E) (n := B.size i) :=
    ⟨SmoothRep.of (ρ i) (hsc i).1.1, hρ i, hsc i⟩
  let Ξ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
  let Ξ' := FiniteTensor.externalSmoothObject (fun i => (A (e i)).obj)
  have hΞ := AllFieldBZ.CuspidalSupport.glCuspidalTensor K T' n hn B A
  have hΞ' := AllFieldBZ.CuspidalSupport.glCuspidalTensor K T' n hn (B.permute e) (fun i => A (e i))
  have hassoc : RepresentationsAssociated B (B.permute e) Ξ.representation Ξ'.representation :=
    ⟨B.blockPermutation e, conjugatesLevi_blockPermutation B e,
      ⟨blockPermutationTensorEquiv B e (conjugatesLevi_blockPermutation B e) ρ⟩⟩
  have hJH := AllFieldBZ.CuspidalSupport.associatedCuspidalInductionFactorsTheorem
    K T' n hn B (B.permute e) Ξ Ξ' hΞ.1 hΞ.2 hΞ'.1 hΞ'.2 hassoc
  exact RepresentationExactComparison.nonempty_equiv_of_sameFactors _ _ h hJH

end Langlands.LocalFieldData

namespace Langlands.BaseChange

open GeneralLinear

universe u v uW

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

set_option maxHeartbeats 600000 in
/-- Construct a σ-intertwiner on the actual normalized orbit product by rotating its
supercuspidal factors. -/
def sigmaOrbitIntertwiner (σ : E ≃ₐ[F] E) {l s n : ℕ}
    (hσ : IsCyclicAlgebra σ l) (hn : 0 < n) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W) (hirr : P.IsIrreducible)
    (hsc : IsSupercuspidal P)
    (hperiod : ∀ j : ℕ,
      Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ j) n).toMonoidHom)) ↔ s ∣ j)
    (hprod : (sigmaOrbitProduct σ s hn P).IsIrreducible) :
    SigmaIntertwiner σ (s * n) (sigmaOrbitProduct σ s hn P) := by
  classical
  let B := BlockShape.uniform s n hn
  let T := LocalFieldData.ofInstances E
  let ρ (i : Fin B.length) : Representation ℂ (GeneralLinear n E) W :=
    P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom
  have hpos := (sigmaConjugate_period_pos_dvd σ P hperiod hσ).1
  have hρ (i : Fin B.length) : Representation.IsIrreducible (ρ i) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff P (entrywiseAut _ _)).mpr hirr
  have hρsc (i : Fin B.length) : IsSupercuspidal (ρ i) :=
    isSupercuspidal_comp_entrywiseAut (σ ^ (i : ℕ)) P hsc
  let e₁ := (T.normalizedProductInduced_equiv_permute_of_irreducible
    (Nat.mul_pos hpos hn) B ρ hρ hρsc hprod (finRotate s)).some
  let e₂ := normalizedProductInducedEntrywiseAutEquiv σ B ρ
  let e₃ := T.normalizedProductInducedEquiv B
    (fun i => (sigmaConjugate_entrywiseAut_equiv_finRotate σ P hperiod i).some)
  exact e₁.trans (e₂.trans e₃).symm

end Langlands.BaseChange
