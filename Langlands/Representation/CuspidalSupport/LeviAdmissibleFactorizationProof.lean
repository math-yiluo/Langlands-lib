import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Finite iteration of admissible irreducible two-factor existence, specialized
to the actual standard p-adic Levi groups with the supplied topology. -/

namespace Langlands.CuspidalSupport

universe uF uW

private theorem fieldTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    TotallyDisconnectedSpace F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

private theorem generalLinearTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    TotallyDisconnectedSpace (GeneralLinear m F.Carrier) := by
  let := T.topology
  let := fieldTotallyDisconnected T
  let : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → F.Carrier))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem leviTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    TotallyDisconnectedSpace (B.Levi F.Carrier) := by
  let := T.topology
  let (i : Fin B.length) :
      TotallyDisconnectedSpace (GeneralLinear (B.size i) F.Carrier) :=
    generalLinearTotallyDisconnected T (B.size i)
  infer_instance

section Equivalences

variable {G H : Type*} [Group G] [Group H]
  {V₁ V₂ W₁ W₂ : Type*}
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup W₁] [AddCommGroup W₂]
  [Module ℂ V₁] [Module ℂ V₂] [Module ℂ W₁] [Module ℂ W₂]

private noncomputable def tensorEquiv
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {τ₁ : Representation ℂ G W₁} {τ₂ : Representation ℂ G W₂}
    (E₁ : ρ₁.Equiv τ₁) (E₂ : ρ₂.Equiv τ₂) :
    (Representation.tprod ρ₁ ρ₂).Equiv (Representation.tprod τ₁ τ₂) :=
  Representation.Equiv.mk (TensorProduct.congr E₁.toLinearEquiv E₂.toLinearEquiv)
    fun g => (E₁.toIntertwiningMap.tensor E₂.toIntertwiningMap).isIntertwining' g

private def equivOfPullback
    {ρ : Representation ℂ G V₁} {τ : Representation ℂ G V₂}
    (e : H ≃* G)
    (E : Representation.Equiv (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom)) :
    ρ.Equiv τ :=
  Representation.Equiv.mk E.toLinearEquiv fun g => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using E.isIntertwining' (e.symm g)

end Equivalences

private theorem factorAlongProduct
    {G H K : Type uF} [Group G] [Group H] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]
    (e : (G × H) ≃ₜ* K) (σ : SmoothRep.{0, uF, uW} ℂ K)
    (hi : σ.IsIrreducible) (ha : σ.IsAdmissible) :
    ∃ (A : SmoothRep.{0, uF, uW} ℂ G) (B : SmoothRep.{0, uF, uW} ℂ H),
      A.IsIrreducible ∧ A.IsAdmissible ∧ B.IsIrreducible ∧ B.IsAdmissible ∧
      Nonempty (Representation.Equiv (σ.representation.comp e.toMonoidHom)
        (Representation.tprod
          (A.representation.comp (MonoidHom.fst G H))
          (B.representation.comp (MonoidHom.snd G H)))) := by
  let := hi
  have hpullA := isAdmissible_comp_continuousMulEquiv σ.representation e ha
  have hpullI := isIrreducible_comp_of_surjective σ.representation
    e.toMonoidHom e.surjective
  obtain ⟨V, W, ρ, τ, hρa, hρi, hτa, hτi, E⟩ :=
    admissibleProductFactorization G H σ
      (σ.representation.comp e.toMonoidHom) hpullA hpullI
  exact ⟨SmoothRep.of ρ hρa.1, SmoothRep.of τ hτa.1,
    hρi, hρa, hτi, hτa, E⟩

private theorem finiteFactorization :
    ∀ (r : ℕ) (H : Fin (r + 1) → Type uF) [∀ i, Group (H i)]
      [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
      [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
      [∀ i, TotallyDisconnectedSpace (H i)]
      (σ : SmoothRep.{0, uF, uW} ℂ (∀ i, H i)),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ A : ∀ i, SmoothRep.{0, uF, uW} ℂ (H i),
        (∀ i, (A i).IsIrreducible) ∧ (∀ i, (A i).IsAdmissible) ∧
        Nonempty (σ.representation.Equiv
          (FiniteTensor.external (fun i => (A i).representation))) := by
  intro r
  induction r with
  | zero =>
      intro H _ _ _ _ _ _ σ hi ha
      let e := (FiniteTensor.evalOneContinuous H).symm
      let := hi
      have hA := isAdmissible_comp_continuousMulEquiv σ.representation e ha
      have hI := isIrreducible_comp_of_surjective σ.representation
        e.toMonoidHom e.surjective
      let A0 : SmoothRep.{0, uF, uW} ℂ (H 0) :=
        SmoothRep.of (σ.representation.comp e.toMonoidHom) hA.1
      let A : ∀ i, SmoothRep.{0, uF, uW} ℂ (H i) :=
        Fin.cons A0 (fun i => Fin.elim0 i)
      refine ⟨A, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hI (fun j => Fin.elim0 j) i
      · intro i
        exact Fin.cases hA (fun j => Fin.elim0 j) i
      · exact ⟨equivOfPullback e.toMulEquiv
          (FiniteTensor.singletonEquiv (fun i => (A i).representation)).symm⟩
  | succ r ih =>
      intro H _ _ _ _ _ _ σ hi ha
      let e := (FiniteTensor.headTailContinuous H).symm
      obtain ⟨A0, B, hA0i, hA0a, hBi, hBa, ⟨E⟩⟩ :=
        factorAlongProduct e σ hi ha
      obtain ⟨Atail, hAi, hAa, ⟨F⟩⟩ :=
        ih (fun j : Fin (r + 1) => H j.succ) B hBi hBa
      let A : ∀ i, SmoothRep.{0, uF, uW} ℂ (H i) := Fin.cons A0 Atail
      refine ⟨A, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hA0i hAi i
      · intro i
        exact Fin.cases hA0a hAa i
      · have E' := tensorEquiv
          (Representation.Equiv.refl
            (A0.representation.comp
              (MonoidHom.fst (H 0) (∀ j : Fin (r + 1), H j.succ))))
          (equivComp F (MonoidHom.snd (H 0) (∀ j : Fin (r + 1), H j.succ)))
        exact ⟨equivOfPullback e.toMulEquiv
          ((E.trans E').trans
            (FiniteTensor.headTailEquiv (fun i => (A i).representation)).symm)⟩

/-- Finite admissible irreducible tensor factorization for the actual standard
p-adic Levi groups, with every factor in the source carrier universe. -/
theorem padicLeviAdmissibleFactorization :
    PadicLeviAdmissibleFactorizationStatement.{uF, uW} := by
  intro p _ F T n hn B
  let := T.topology
  intro σ hi ha
  let (i : Fin B.length) :
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearTopologicalGroup (B.size i)
  let (i : Fin B.length) : T2Space (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearT2Space (B.size i)
  let (i : Fin B.length) :
      LocallyCompactSpace (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (B.size i)
  let (i : Fin B.length) :
      TotallyDisconnectedSpace (GeneralLinear (B.size i) F.Carrier) :=
    generalLinearTotallyDisconnected T (B.size i)
  have hf := finiteFactorization.{uF, uW} B.length.pred
  have he : B.length.pred + 1 = B.length :=
    Nat.succ_pred_eq_of_pos (length_pos_of_pos B hn)
  rw [he] at hf
  exact hf (fun i => GeneralLinear (B.size i) F.Carrier) σ hi ha

end Langlands.CuspidalSupport
