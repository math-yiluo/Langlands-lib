import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.FrobeniusDetection
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.RankinSelberg.AdjacentRankUpperFamilyTransport
import Langlands.Representation.CompactCoefficient.AdmissibleLifting
import Langlands.Representation.CompactCoefficient.AdmissibleRetraction
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# Assembly of Whittaker completeness against products of supercuspidals

The completeness statement follows from two inputs, stated here as propositions:

* `GelfandGraevJacquetStatement`: the Jacquet module of the Gelfand–Graev representation along a
  standard block parabolic is the Gelfand–Graev representation of the Levi;
* `DeltaPairingStatement`: a `G`-invariant bilinear form on the Gelfand–Graev representation and
  a smooth representation `Π` is given by integration against the coefficient functions of an
  inverse-character Whittaker functional of `Π`.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration Induction

universe uF uW uE

/-- Invariant pairings with the Gelfand–Graev representation are Whittaker integrals: for a
smooth representation `π` of `GL_(n+1)(F)` and a `G`-invariant bilinear form `β` on
`c-Ind_N^G ψ × π`, there is an inverse-character Whittaker functional `ℓ'` of `π` such that
`β x e = ∫_{N \ G} x(g) ℓ'(π(g) e) dμ` for every compatible quotient measure `μ`. -/
def DeltaPairingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ →
      ∀ (E : Type uE) [AddCommGroup E] [Module ℂ E]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) E), IsSmooth π →
      ∀ β : GelfandGraevFunctions ψ n →ₗ[ℂ] E →ₗ[ℂ] ℂ,
        (∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x e,
          β (gelfandGraev ψ n g x) (π g e) = β x e) →
        ∃ ℓ' : glInverseFunctionals ψ n π,
          ∀ x e, β x e =
            ∫ q, whittakerProductIntegrand ψ (toWhittaker ψ n x) (coefficientMap π ℓ' e) q ∂μ

/-- An equivalence of representations followed by its inverse is the identity. -/
theorem equiv_symm_apply_apply {G : Type*} [Group G] {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : ρ.Equiv σ) (v : V) : e.symm (e v) = v :=
  e.toLinearEquiv.symm_apply_apply v

section DualPairing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W Q : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Q] [Module ℂ Q]
  (ρ : Representation ℂ G V) (π0 : Representation ℂ G W) (κ : Representation ℂ G Q)
  (Tf : ρ.IntertwiningMap π0) (e : (smoothContragredient π0).Equiv κ)

/-- The bilinear form `(x, φ) ↦ e⁻¹(φ)(Tf x)`, for an intertwiner `Tf : ρ → π0` and an
identification `e` of the smooth dual of `π0` with `κ`. -/
def dualPairing : V →ₗ[ℂ] Q →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x φ => (e.symm φ).val (Tf x))
    (fun x y φ => by simp only [map_add])
    (fun c x φ => by simp only [map_smul, smul_eq_mul])
    (fun x φ φ' => by
      simp only [map_add]
      rfl)
    (fun c x φ => by
      simp only [map_smul]
      rfl)

theorem dualPairing_apply (x : V) (φ : Q) :
    dualPairing ρ π0 κ Tf e x φ = (e.symm φ).val (Tf x) := rfl

theorem dualPairing_invariant (g : G) (x : V) (φ : Q) :
    dualPairing ρ π0 κ Tf e (ρ g x) (κ g φ) = dualPairing ρ π0 κ Tf e x φ := by
  rw [dualPairing_apply, dualPairing_apply]
  have h1 : e.symm (κ g φ) = smoothContragredient π0 g (e.symm φ) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g φ
  have h2 : Tf (ρ g x) = π0 g (Tf x) :=
    Representation.IntertwiningMap.isIntertwining _ _ Tf g x
  rw [h1, h2]
  change (e.symm φ).val (π0 g⁻¹ (π0 g (Tf x))) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem dualPairing_self (x : V) (lam : SmoothDual π0) :
    dualPairing ρ π0 κ Tf e x (e lam) = lam.val (Tf x) := by
  rw [dualPairing_apply, equiv_symm_apply_apply]

end DualPairing

/-- Properties transfer along a cast of the rank. -/
theorem cast_rep_prop {F : Type*} [CommRing F] {a b : ℕ} (h : a = b) {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (P : ∀ k : ℕ, Representation ℂ (Langlands.GeneralLinear k F) V → Prop)
    (ρ : Representation ℂ (Langlands.GeneralLinear a F) V) (hρ : P a ρ) : P b (h ▸ ρ) := by
  subst h
  exact hρ

set_option maxHeartbeats 1600000 in
/-- Whittaker completeness against normalized products of supercuspidals, from the Jacquet
module of the Gelfand–Graev representation and the delta-function pairing lemma. -/
theorem supercuspidalProductCompleteness_of (hJ : GelfandGraevJacquetStatement.{uF})
    (hδ : DeltaPairingStatement.{uF, max uF uW}) :
    SupercuspidalProductCompletenessStatement.{uF, uW} := by
  classical
  intro p _ F ψ n
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let _ : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let _ : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro _ μ hμ H hH hyp
  by_contra hH0
  obtain ⟨h, rfl⟩ := exists_toWhittaker_eq ψ n H hH
  have hh : h ≠ 0 := fun h0 => hH0 (by rw [h0, map_zero])
  obtain ⟨B, A, Tf, hTf⟩ := exists_frobenius_ne_zero.{uF, uW} F hJ ψ n h hh
  let T := F.canonicalTopologicalData
  let := T.generalLinearTopologicalGroup (n + 1)
  let P0 := T.normalizedProductInduced B (fun i => (A i).obj.representation)
  have hP0 : IsSmooth P0 := Induction.smoothInduced_smooth _ _
  -- a smooth functional detecting `Tf h`
  obtain ⟨ℓ, hℓs, hℓ⟩ := CompactSplitting.exists_smooth_functional_ne_zero
    (GeneralLinear.compactOpen_cofinal F T (n + 1)) P0 hP0 hTf
  let lam0 : SmoothDual P0 := ⟨ℓ, hℓs⟩
  -- the smooth dual of the product is the product of the contragredients
  obtain ⟨E⟩ := Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv
    T B (fun i => (A i).obj.representation) (fun i => (A i).property.2.1)
  let m : Fin B.length → ℕ := fun i => B.size i - 1
  have hsize : ∀ i, B.size i = m i + 1 := fun i => (Nat.succ_pred_eq_of_pos (B.positive i)).symm
  have hm : ∑ i, (m i + 1) = n + 1 :=
    (Finset.sum_congr rfl fun i _ => (hsize i).symm).trans B.sum_eq
  let τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier)
      (SmoothDual (A i).obj.representation) :=
    fun i => hsize i ▸ smoothContragredient (A i).obj.representation
  let e2 := RankinSelberg.Padic.normalizedProductInducedEquiv_of_sizes F B m hsize hm
    (fun i => smoothContragredient (A i).obj.representation) τ
    (fun i => Representation.Equiv.refl _)
  let Pi1 := F.canonicalNormalizedProductInduced (succBlockShape m hm) τ
  have hPi1 : IsSmooth Pi1 := Induction.smoothInduced_smooth _ _
  -- the invariant pairing
  let e3 := E.trans e2
  let β := dualPairing (gelfandGraev ψ n) P0 Pi1 Tf e3
  have hβ : ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x φ,
      β (gelfandGraev ψ n g x) (Pi1 g φ) = β x φ :=
    dualPairing_invariant (gelfandGraev ψ n) P0 Pi1 Tf e3
  obtain ⟨ℓ', hℓ'⟩ := hδ p F ψ n μ hμ _ Pi1 hPi1 β hβ
  -- the detecting test vector
  let φ0 := e3 lam0
  have hφ0 : β h φ0 = ℓ (Tf h) := dualPairing_self (gelfandGraev ψ n) P0 Pi1 Tf e3 h lam0
  -- the block hypotheses
  have hcof := GeneralLinear.compactOpen_cofinal F T
  have hsm : ∀ i, IsSmooth (τ i) := fun i =>
    cast_rep_prop (hsize i) (fun k ρ => letI := T.generalLinearTopologicalGroup k; IsSmooth ρ)
      _ (isSmooth_smoothContragredient _)
  have hirr : ∀ i, Representation.IsIrreducible (τ i) := fun i =>
    cast_rep_prop (hsize i) (fun k ρ => Representation.IsIrreducible ρ) _
      (CompactSplitting.isIrreducible_smoothContragredient (hcof (B.size i)) _
        (A i).property.2.1 (A i).property.1)
  have hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i) := fun i =>
    cast_rep_prop (hsize i) (fun k ρ => letI := T.generalLinearTopologicalGroup k;
      GeneralLinear.IsSupercuspidal ρ) _
      (GeneralLinear.isSupercuspidal_smoothContragredient F T (B.size i) _ _ (A i).property.2)
  have hzero := hyp B.length m hm (fun i => SmoothDual (A i).obj.representation) τ hsm hirr hsc
    ℓ' ⟨coefficientMap Pi1 ℓ' φ0, φ0, rfl⟩
  apply hℓ
  rw [← hφ0, hℓ' h φ0]
  exact hzero

end Langlands.RankinSelberg.SupercuspidalCompleteness
