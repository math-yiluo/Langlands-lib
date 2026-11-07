import Langlands.Representation.Aubert.General.NaturalIntegralDuality
import Langlands.Representation.Aubert.General.InductionLimits
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Category.ChainUnitAdjunction
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Langlands.Representation.Aubert.General.IwahoriJacquetStableLift
import Langlands.Representation.Aubert.General.AlternatingOperator

/-!
# Second adjointness from open-cell functions

Let `P = M ⋉ U` be an actual semidirect decomposition, `O` a closed subgroup normalized by
`M` with `P ∩ O = 1`, `i` normalized induction and `r`, `r̄` the normalized Jacquet functors
along `U` and `O`. Renard 2026, VI.9.6 (printed p.202, PDF p.208), deduces second
adjointness `i ⊣ r̄` from the chain (VI.9.6.3). By `SmoothRep.nonempty_adjunction_of_frobeniusChain_unit`
it suffices that the unit of the chain at every `τ` factors through `r̄` of bidual
evaluation of `i τ`.

This file proves that factorization from two inputs: a natural isomorphism `C : (i A)~ ≅ i(A~)`
characterized by an integral of coefficients (`IsNaturalIntegralDuality`), and a natural
isomorphism `Ψ : r̄(V~) ≅ (r V)~` with Casselman's stable-lift property
(`IsStableLiftDuality`). The proof evaluates both sides on the open-cell functions `f_{t,K}`,
supported on `P K` with `f_{t,K}(p k) = δ_P^{1/2}(p) τ(p) t`, for small compact open `K`
with opposite Iwahori contractions, so that `K = (K ∩ P)(K ∩ O)`.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

section Cell

/-- The open-cell function of `t` at level `K`: the compactly supported covariant function
on `P * K` with value `t` at `1`, so `f (p * k) = δ_P^{1/2}(p) τ(p) t`. It exists when
`P ∩ K` fixes `t` under the inducing representation. -/
def cellFunction (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup) :
    (normalizedInductionFunctor.{uG, uV} h hU).obj A :=
  (Induction.compactDoubleCosetSection P (inducingRepresentation h hU A) K hK 1 t ht).val

/-- The weight of the cell `P * K` at `y`: the square of `δ_P^{1/2}(p)` for a chosen
decomposition `y = p * k` with `p ∈ P` and `k ∈ K`, and `0` off the cell. -/
def cellWeight (K : OpenSubgroup G) (y : G) : ℂ := by
  classical
  exact if hy : ∃ p : P, ∃ k : K, y = (p : G) * (k : G) then
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer hy.choose : ℂˣ) : ℂ) ^ 2 else 0

/-- The pairing constant of level `K`: the integral of the cell weight. -/
def cellConstant (S : Subgroup G) [MeasurableSpace S] (μ : Measure S) (K : OpenSubgroup G) :
    ℂ :=
  ∫ k : S, cellWeight h hU K k ∂μ

variable {h hU}

/-- The open-cell function at `p * k` is `δ_P^{1/2}(p) τ(p) t`. -/
theorem cellFunction_apply (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup) (p : P) (k : K) :
    Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht)
        ((p : G) * (k : G)) = inducingRepresentation h hU A p t := by
  have e := Induction.compactDoubleCosetSection_apply P (inducingRepresentation h hU A) K hK 1
    t ht p k
  rw [mul_one] at e
  exact e

/-- The open-cell function vanishes off `P * K`. -/
theorem cellFunction_eq_zero (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup) (y : G)
    (hy : ¬ ∃ p : P, ∃ k : K, y = (p : G) * (k : G)) :
    Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht) y = 0 := by
  by_contra hne
  have hmem : Induction.quotientMap P y ∈ Induction.quotientSupport P
      (Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht)) :=
    ⟨y, hne, rfl⟩
  obtain ⟨k, hk, hq⟩ := Induction.compactDoubleCosetSection_support_subset P
    (inducingRepresentation h hU A) K hK 1 t ht hmem
  have hp : y * (1 * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  exact hy ⟨⟨y * (1 * k)⁻¹, hp⟩, ⟨k, hk⟩, by simp⟩

/-- The open-cell function is fixed by `K`. -/
theorem cellFunction_mem_fixedVectors (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup) :
    cellFunction h hU A K hK t ht ∈
      fixedVectors ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
        K.toSubgroup := by
  intro k
  apply Subtype.ext
  apply Subtype.ext
  funext y
  exact Induction.compactDoubleCosetSection_mul P (inducingRepresentation h hU A) K hK 1 t ht
    k y

/-- The value of the open-cell function at `1` is `t`. -/
theorem cellFunction_apply_one (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup) :
    Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht) 1 = t := by
  have e := cellFunction_apply A K hK t ht 1 1
  rw [OneMemClass.coe_one, OneMemClass.coe_one, mul_one, map_one, Module.End.one_apply] at e
  exact e

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The coefficient pairing is invariant under the contragredient pair of actions. -/
theorem smoothDualPairing_smoothContragredient_apply_apply {H : Type uG} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (A : SmoothRep.{0, uG, uV} ℂ H) (m : H)
    (ψ : SmoothDual A.representation) (t : A) :
    smoothDualPairing A.representation (smoothContragredient A.representation m ψ)
        (A.representation m t) = smoothDualPairing A.representation ψ t := by
  change smoothDualPairing A.representation ψ (A.representation m⁻¹ (A.representation m t)) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The value at `k ∈ K` of the image of a `K`-fixed vector in an induced representation is
its value at `1`. -/
theorem eval_hom_of_mem_fixedVectors {X : SmoothRep.{0, uG, max uG uV} ℂ G}
    (B : SmoothRep.{0, uG, uV} ℂ M) (φ : X ⟶ (normalizedInductionFunctor.{uG, uV} h hU).obj B)
    {K : OpenSubgroup G} {x : X} (hx : x ∈ fixedVectors X.representation K.toSubgroup)
    (k : K) :
    Induction.eval P (inducingRepresentation h hU B) (SmoothRep.hom φ x) k =
      Induction.eval P (inducingRepresentation h hU B) (SmoothRep.hom φ x) 1 := by
  have e1 := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom φ) (k : G) x
  have hk : X.representation (k : G) x = x := hx k
  rw [hk] at e1
  have e2 : Induction.eval P (inducingRepresentation h hU B)
      (((normalizedInductionFunctor.{uG, uV} h hU).obj B).representation (k : G)
        (SmoothRep.hom φ x)) 1 =
      Induction.eval P (inducingRepresentation h hU B) (SmoothRep.hom φ x) (1 * (k : G)) :=
    rfl
  rw [one_mul, ← e1] at e2
  exact e2.symm

/-- The integrand of the coefficient pairing with an open-cell function: for `F ∈ i(A~)`
with `F(k) = F(1)` on `K`, `⟨F(y), f_{t,K}(y)⟩ = w_K(y) ⟨F(1), t⟩`. -/
theorem smoothDualPairing_eval_cellFunction (A : SmoothRep.{0, uG, uV} ℂ M)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (F : (normalizedInductionFunctor.{uG, uV} h hU).obj A.contragredient)
    (hF : ∀ k : K, Induction.eval P (inducingRepresentation h hU A.contragredient) F k =
      Induction.eval P (inducingRepresentation h hU A.contragredient) F 1) (y : G) :
    smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) F y)
        (Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht) y) =
      cellWeight h hU K y * smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) F 1) t := by
  classical
  by_cases hy : ∃ p : P, ∃ k : K, y = (p : G) * (k : G)
  · obtain ⟨p, k, hpk, hw⟩ : ∃ (p : P) (k : K), y = (p : G) * (k : G) ∧
        cellWeight h hU K y =
          ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) ^ 2 :=
      ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec, by
        rw [cellWeight, dite_eq_left hy]⟩
    rw [hw]
    subst hpk
    rw [cellFunction_apply]
    have hcov := normalizedInductionFunctor_covariant h hU A.contragredient F p (k : G)
    erw [hcov, hF k]
    change smoothDualPairing A.representation
        (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
          smoothContragredient A.representation (h.projection p)
            (Induction.eval P (inducingRepresentation h hU A.contragredient) F 1))
        (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
          A.representation (h.projection p) t) = _
    rw [map_smul, map_smul, LinearMap.smul_apply,
      smoothDualPairing_smoothContragredient_apply_apply, smul_eq_mul, smul_eq_mul, pow_two,
      mul_assoc]
  · rw [cellFunction_eq_zero A K hK t ht y hy, map_zero, cellWeight, dite_eq_right hy, zero_mul]

/-- The pairing of a `K`-fixed `ℓ ∈ (i A)~` with the open-cell function `f_{t,K}`:
`⟨ℓ, f_{t,K}⟩ = c_K ⟨(C ℓ)(1), t⟩`, where `c_K` is the integral of the cell weight. -/
theorem smoothDualPairing_cellFunction (S : Subgroup G) [MeasurableSpace S] (μ : Measure S)
    (C : (normalizedInductionFunctor.{uG, uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV} ≅
      SmoothRep.contragredientFunctor.{0, uG, uV} ⋙ normalizedInductionFunctor.{uG, uV} h hU)
    (hC : IsNaturalIntegralDuality.{uG, uV} h hU S μ C)
    (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (ℓ : ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient)
    (hℓ : ℓ ∈ fixedVectors
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient.representation
      K.toSubgroup) :
    smoothDualPairing ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation ℓ
        (cellFunction h hU A K hK t ht) =
      cellConstant h hU S μ K * smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient)
          (SmoothRep.hom (C.hom.app (Opposite.op A)) ℓ) 1) t := by
  rw [hC A ℓ, cellConstant, ← integral_mul_const]
  refine congrArg (fun F : S → ℂ => ∫ k : S, F k ∂μ) (funext fun k => ?_)
  exact smoothDualPairing_eval_cellFunction A K hK t ht _
    (eval_hom_of_mem_fixedVectors A.contragredient (C.hom.app (Opposite.op A)) hℓ) (k : G)

end Cell

section Coset

variable {h hU} {O : Subgroup G}

/-- The pointwise coset decomposition of an open-cell function: if `K ≤ K₀` both factor as
`k = p o` with `p ∈ P` and `o ∈ O` in the subgroup, and `P ∩ O = 1`, then
`f_{t,K₀}(y) = Σ_{q ∈ (K₀ ∩ O)/(K ∩ O)} f_{t,K}(y q)`. -/
theorem eval_cellFunction_eq_sum (A : SmoothRep.{0, uG, uV} ℂ M)
    (hPO : ∀ x : G, x ∈ P → x ∈ O → x = 1) {K K₀ : OpenSubgroup G} (hKK₀ : K ≤ K₀)
    (hK : IsCompact (K : Set G)) (hK₀ : IsCompact (K₀ : Set G))
    (hfac : ∀ k : G, k ∈ K → ∃ p ∈ P, ∃ o ∈ O, o ∈ K ∧ k = p * o)
    (hfac₀ : ∀ k : G, k ∈ K₀ → ∃ p ∈ P, ∃ o ∈ O, o ∈ K₀ ∧ k = p * o) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (ht₀ : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K₀ 1).toSubgroup)
    [Fintype (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O))] (y : G) :
    Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K₀ hK₀ t ht₀) y =
      ∑ q : ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O),
        Induction.eval P (inducingRepresentation h hU A) (cellFunction h hU A K hK t ht)
          (y * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G)) := by
  classical
  by_cases hy : ∃ p : P, ∃ k : K₀, y = (p : G) * (k : G)
  · obtain ⟨p, k₀, rfl⟩ := hy
    obtain ⟨p₁, hp₁, o₁, ho₁, ho₁K₀, hk₀⟩ := hfac₀ k₀ k₀.2
    have ho₁' : o₁⁻¹ ∈ K₀.toSubgroup ⊓ O := Subgroup.mem_inf.mpr ⟨inv_mem ho₁K₀, inv_mem ho₁⟩
    rw [Finset.sum_eq_single
      (QuotientGroup.mk ⟨o₁⁻¹, ho₁'⟩ :
        ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O))]
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul
        (K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)) (⟨o₁⁻¹, ho₁'⟩ : ↥(K₀.toSubgroup ⊓ O))
      have hcK : ((c : ↥(K₀.toSubgroup ⊓ O)) : G) ∈ K := Subgroup.mem_subgroupOf.mp c.2
      have hp₁K₀ : p₁ ∈ K₀ := by
        have e : p₁ = (k₀ : G) * o₁⁻¹ := by rw [hk₀]; group
        rw [e]
        exact mul_mem k₀.2 (inv_mem ho₁K₀)
      have hval : (p : G) * (k₀ : G) *
          ((Quotient.out (QuotientGroup.mk ⟨o₁⁻¹, ho₁'⟩ :
            ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)) :
              ↥(K₀.toSubgroup ⊓ O)) : G) =
          ((p * ⟨p₁, hp₁⟩ : P) : G) * ((⟨_, hcK⟩ : K) : G) := by
        rw [hc, Subgroup.coe_mul, hk₀, Subgroup.coe_mul]
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [hval, cellFunction_apply, cellFunction_apply, map_mul, Module.End.mul_apply]
      congr 1
      exact (ht₀ ⟨⟨p₁, hp₁⟩, Induction.mem_conjOpenSubgroup.mpr (by simpa using hp₁K₀)⟩).symm
    · intro q _ hq
      apply cellFunction_eq_zero
      rintro ⟨p₂, k, hpk⟩
      obtain ⟨p₃, hp₃, o₃, ho₃, ho₃K, hk⟩ := hfac k k.2
      have hqO : ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) ∈ O :=
        (Subgroup.mem_inf.mp (Quotient.out q).2).2
      have e₁ : o₁ * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) =
          p₁⁻¹ * (p : G)⁻¹ * ((p₂ : G) * (p₃ * o₃)) := by
        rw [← hk, ← hpk, hk₀]
        group
      have hxP : o₁ * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) * o₃⁻¹ ∈ P := by
        rw [e₁]
        have e₂ : p₁⁻¹ * (p : G)⁻¹ * ((p₂ : G) * (p₃ * o₃)) * o₃⁻¹ =
            p₁⁻¹ * (p : G)⁻¹ * (p₂ : G) * p₃ := by group
        rw [e₂]
        exact mul_mem (mul_mem (mul_mem (inv_mem hp₁) (inv_mem p.2)) p₂.2) hp₃
      have hxO : o₁ * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) * o₃⁻¹ ∈ O :=
        mul_mem (mul_mem ho₁ hqO) (inv_mem ho₃)
      have hx := mul_inv_eq_one.mp (hPO _ hxP hxO)
      apply hq
      have hmk : (QuotientGroup.mk (Quotient.out q) :
          ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)) =
          QuotientGroup.mk ⟨o₁⁻¹, ho₁'⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          ← mul_inv_rev, hx]
        exact inv_mem ho₃K
      rwa [QuotientGroup.out_eq'] at hmk
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [cellFunction_eq_zero A K₀ hK₀ t ht₀ y hy]
    symm
    apply Finset.sum_eq_zero
    intro q _
    apply cellFunction_eq_zero
    rintro ⟨p₂, k, hpk⟩
    apply hy
    refine ⟨p₂, ⟨(k : G) * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G)⁻¹,
      mul_mem (hKK₀ k.2) (inv_mem (Subgroup.mem_inf.mp (Quotient.out q).2).1)⟩, ?_⟩
    change y = (p₂ : G) * ((k : G) * ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G)⁻¹)
    rw [← mul_assoc, ← hpk]
    group

/-- The coset decomposition of an open-cell function as a finite sum of translates:
`f_{t,K₀} = Σ_{q ∈ (K₀ ∩ O)/(K ∩ O)} q · f_{t,K}`. -/
theorem cellFunction_eq_sum (A : SmoothRep.{0, uG, uV} ℂ M)
    (hPO : ∀ x : G, x ∈ P → x ∈ O → x = 1) {K K₀ : OpenSubgroup G} (hKK₀ : K ≤ K₀)
    (hK : IsCompact (K : Set G)) (hK₀ : IsCompact (K₀ : Set G))
    (hfac : ∀ k : G, k ∈ K → ∃ p ∈ P, ∃ o ∈ O, o ∈ K ∧ k = p * o)
    (hfac₀ : ∀ k : G, k ∈ K₀ → ∃ p ∈ P, ∃ o ∈ O, o ∈ K₀ ∧ k = p * o) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (ht₀ : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K₀ 1).toSubgroup)
    [Fintype (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O))] :
    cellFunction h hU A K₀ hK₀ t ht₀ =
      ∑ q : ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O),
        ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
          ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) (cellFunction h hU A K hK t ht) := by
  apply Induction.FiniteProductTensorBijective.smoothFunctions_ext
  intro y
  refine (eval_cellFunction_eq_sum A hPO hKK₀ hK hK₀ hfac hfac₀ t ht ht₀ y).trans ?_
  exact (Induction.FiniteProductTensorBijective.eval_sum P (inducingRepresentation h hU A)
    (Finset.univ : Finset (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)))
    (fun q => ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
      ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) (cellFunction h hU A K hK t ht)) y).symm

/-- The coset relation in the Jacquet module along `O`: the classes of the open-cell
functions at levels `K ≤ K₀` differ by the index `[K₀ ∩ O : K ∩ O]`. -/
theorem exists_mk_cellFunction_eq_smul (hO : IsClosed (O : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (hPO : ∀ x : G, x ∈ P → x ∈ O → x = 1) {K K₀ : OpenSubgroup G} (hKK₀ : K ≤ K₀)
    (hK : IsCompact (K : Set G)) (hK₀ : IsCompact (K₀ : Set G))
    (hfac : ∀ k : G, k ∈ K → ∃ p ∈ P, ∃ o ∈ O, o ∈ K ∧ k = p * o)
    (hfac₀ : ∀ k : G, k ∈ K₀ → ∃ p ∈ P, ∃ o ∈ O, o ∈ K₀ ∧ k = p * o) (t : A)
    (ht : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (ht₀ : t ∈ fixedVectors (inducingRepresentation h hU A)
      (Induction.conjOpenSubgroup P K₀ 1).toSubgroup) :
    ∃ N : ℕ,
      Jacquet.Localization.mk ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
          O 1 (cellFunction h hU A K₀ hK₀ t ht₀) =
        (N : ℂ) • Jacquet.Localization.mk
          ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation O 1
            (cellFunction h hU A K hK t ht) := by
  classical
  have hc : IsCompact ((K₀.toSubgroup ⊓ O : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hK₀.inter_right hO
  have : CompactSpace ↥(K₀.toSubgroup ⊓ O) := isCompact_iff_compactSpace.mp hc
  have : Finite (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)) :=
    Subgroup.quotient_finite_of_isOpen _
      (Subgroup.subgroupOf_isOpen _ _ K.isOpen)
  let := Fintype.ofFinite (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O))
  refine ⟨Fintype.card (↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O)),
    ?_⟩
  rw [cellFunction_eq_sum A hPO hKK₀ hK hK₀ hfac hfac₀ t ht ht₀, map_sum]
  have hterm : ∀ q : ↥(K₀.toSubgroup ⊓ O) ⧸ K.toSubgroup.subgroupOf (K₀.toSubgroup ⊓ O),
      Jacquet.Localization.mk ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
          O 1 (((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
            ((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G) (cellFunction h hU A K hK t ht)) =
        Jacquet.Localization.mk ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
          O 1 (cellFunction h hU A K hK t ht) := fun q => by
    have e := Jacquet.Localization.mk_apply_subgroup
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation O 1
      ⟨((Quotient.out q : ↥(K₀.toSubgroup ⊓ O)) : G), (Subgroup.mem_inf.mp (Quotient.out q).2).2⟩
      (cellFunction h hU A K hK t ht)
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact e
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    Nat.cast_smul_eq_nsmul]

end Coset

section Lift

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- On a compact open level, the fixed smooth functionals separate fixed vectors. -/
theorem eq_zero_of_forall_fixed_smoothDualPairing {H : Type uG} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X : SmoothRep.{0, uG, uV} ℂ H} {K : OpenSubgroup H}
    (hK : IsCompact (K : Set H)) {f : X} (hf : f ∈ fixedVectors X.representation K.toSubgroup)
    (h0 : ∀ ℓ ∈ fixedVectors X.contragredient.representation K.toSubgroup,
      smoothDualPairing X.representation ℓ f = 0) :
    f = 0 := by
  have hv : (⟨f, hf⟩ : fixedVectors X.representation K.toSubgroup) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
    obtain ⟨ℓ, rfl⟩ :=
      (smoothDualFixedRestriction_bijective X.representation X.isSmooth K hK).2 φ
    exact h0 ℓ.1 ℓ.2
  exact congrArg Subtype.val hv

variable {h hU}

/-- A vector of the inducing representation is fixed by `P ∩ K` for all small `K`. -/
theorem exists_openSubgroup_forall_mem_fixedVectors (hproj : Continuous h.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M) (t : A) :
    ∃ W : OpenSubgroup G, ∀ K : OpenSubgroup G, K ≤ W →
      t ∈ fixedVectors (inducingRepresentation h hU A)
        (Induction.conjOpenSubgroup P K 1).toSubgroup := by
  have hs : IsSmooth (inducingRepresentation h hU A) :=
    (isSmooth_twist_iff _ _ (HaarModulus.isOpen_ker_closedHalfCharacter U hU P
      h.le_normalizer)).mpr (isSmooth_comp h.projection hproj A.isSmooth)
  obtain ⟨H, hH⟩ := hs t
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp H.isOpen
  have h1 : (1 : G) ∈ V := by
    have : (1 : P) ∈ (Subtype.val ⁻¹' V : Set P) := by
      rw [hV]
      exact H.one_mem
    exact this
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean V (hVopen.mem_nhds h1)
  refine ⟨W, fun K hK p => ?_⟩
  have hpK : ((p : P) : G) ∈ K := by
    have := (Induction.mem_conjOpenSubgroup (P := P) (K := K) (i := 1) (p := (p : P))).mp p.2
    simpa using this
  have hpH : (p : P) ∈ H := by
    have : (p : P) ∈ (Subtype.val ⁻¹' V : Set P) := hW (hK hpK)
    rw [hV] at this
    exact this
  exact hH ⟨p, hpH⟩

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- An intertwiner carries vectors fixed by a subgroup to vectors fixed by it. -/
theorem hom_mem_fixedVectors {H : Type uG} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X Y : SmoothRep.{0, uG, uV} ℂ H} (φ : X ⟶ Y) {S : Subgroup H}
    {x : X} (hx : x ∈ fixedVectors X.representation S) :
    SmoothRep.hom φ x ∈ fixedVectors Y.representation S := by
  intro s
  change Y.representation (s : H) (SmoothRep.hom φ x) = SmoothRep.hom φ x
  rw [← (SmoothRep.hom φ).isIntertwining]
  exact congrArg (SmoothRep.hom φ) (hx s)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The underlying intertwiner of an isomorphism is injective. -/
theorem hom_injective_of_iso {H : Type uG} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X Y : SmoothRep.{0, uG, uV} ℂ H} (e : X ≅ Y) :
    Function.Injective (SmoothRep.hom e.hom) := by
  have h1 : ∀ a, SmoothRep.hom e.inv (SmoothRep.hom e.hom a) = a := fun a =>
    congrArg (fun f => SmoothRep.hom f a) e.hom_inv_id
  intro a b hab
  rw [← h1 a, hab, h1 b]

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A morphism `ζ : X ⟶ Z` whose values all lie in the image of an injective morphism
`φ : Y ⟶ Z` factors through `φ`. -/
theorem exists_comp_eq_of_injective {H : Type uG} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X Y Z : SmoothRep.{0, uG, uV} ℂ H} (φ : Y ⟶ Z)
    (hφ : Function.Injective (SmoothRep.hom φ)) (ζ : X ⟶ Z)
    (hζ : ∀ x, ∃ y, SmoothRep.hom φ y = SmoothRep.hom ζ x) : ∃ η : X ⟶ Y, η ≫ φ = ζ := by
  choose s hs using hζ
  refine ⟨SmoothRep.ofHom
    { toFun := s
      map_add' := fun a b => hφ (by simp only [map_add, hs])
      map_smul' := fun c a => hφ (by simp only [map_smul, hs, RingHom.id_apply])
      isIntertwining' := fun k => LinearMap.ext fun a => hφ ?_ }, ?_⟩
  · change SmoothRep.hom φ (s (X.representation k a)) =
      SmoothRep.hom φ (Y.representation k (s a))
    rw [hs, (SmoothRep.hom φ).isIntertwining, hs, (SmoothRep.hom ζ).isIntertwining]
  · apply SmoothRep.hom_ext'
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact hs x

/-- Scalar normalization of the open-cell classes. Let `e_K` be classes indexed by good
levels `K`, cofinal for `≤`, with `e_{K₀} = N e_K` for some natural `N` when `K ≤ K₀`, and
let `Φ` be a pairing such that for each `x`, `Φ(e_K, x) = c_K ξ(x)` for all small good `K`.
If `c_K = 0` for a good `K` forces `ξ = 0`, then `ξ = Φ(b, ·)` for some `b`. -/
theorem exists_eq_of_cellRelations {I B X : Type*} [SemilatticeInf I] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup X] [Module ℂ X] (Φ : B →ₗ[ℂ] X →ₗ[ℂ] ℂ) (ξ : X →ₗ[ℂ] ℂ)
    (Good : I → Prop) (hcof : ∀ W, ∃ K, Good K ∧ K ≤ W) (e : ∀ K, Good K → B) (c : I → ℂ)
    (hkey : ∀ x, ∃ W, ∀ K (hK : Good K), K ≤ W → Φ (e K hK) x = c K * ξ x)
    (hcoset : ∀ K K₀ (hK : Good K) (hK₀ : Good K₀), K ≤ K₀ →
      ∃ N : ℕ, e K₀ hK₀ = (N : ℂ) • e K hK)
    (hnz : ∀ K, Good K → c K = 0 → ξ = 0) :
    ∃ b, Φ b = ξ := by
  classical
  by_cases hξ0 : ξ = 0
  · exact ⟨0, by rw [map_zero, hξ0]⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ξ x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ0 (LinearMap.ext hcon)
  obtain ⟨W₀, hW₀⟩ := hkey x₀
  obtain ⟨K₀, hK₀, hK₀W⟩ := hcof W₀
  have hc₀ : c K₀ ≠ 0 := fun h0 => hξ0 (hnz K₀ hK₀ h0)
  refine ⟨(c K₀)⁻¹ • e K₀ hK₀, LinearMap.ext fun x => ?_⟩
  obtain ⟨Wx, hWx⟩ := hkey x
  obtain ⟨K, hK, hKW⟩ := hcof (K₀ ⊓ Wx ⊓ W₀)
  have hKK₀ : K ≤ K₀ := hKW.trans (inf_le_left.trans inf_le_left)
  have hKx : K ≤ Wx := hKW.trans (inf_le_left.trans inf_le_right)
  have hK0 : K ≤ W₀ := hKW.trans inf_le_right
  obtain ⟨N, hN⟩ := hcoset K K₀ hK hK₀ hKK₀
  have e₀ := hW₀ K₀ hK₀ hK₀W
  have e₁ := hW₀ K hK hK0
  have e₂ := hWx K hK hKx
  rw [hN, map_smul, LinearMap.smul_apply, e₁, smul_eq_mul] at e₀
  have hc : (N : ℂ) * c K = c K₀ := by
    apply mul_right_cancel₀ hx₀
    rw [mul_assoc]
    exact e₀
  rw [map_smul, LinearMap.smul_apply, hN, map_smul, LinearMap.smul_apply, e₂, smul_eq_mul,
    smul_eq_mul, ← mul_assoc (N : ℂ), hc, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]

variable {O : Subgroup G}

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- An Iwahori factorization `K = (K ∩ U)(K ∩ M)(K ∩ O)` writes every `k ∈ K` as `k = p o`
with `p ∈ P = M U` and `o ∈ K ∩ O`. -/
theorem exists_mul_of_isIwahoriContraction (hMP : M ≤ P) (hUP : U ≤ P) {K : OpenSubgroup G}
    {g : G} (hI : Jacquet.IsIwahoriContraction K O M U g) (k : G) (hk : k ∈ K) :
    ∃ p ∈ P, ∃ o ∈ O, o ∈ K ∧ k = p * o := by
  obtain ⟨l, hl, m, hm, o, ho, rfl⟩ := hI.factor k hk
  exact ⟨l * m, mul_mem (hUP (Subgroup.mem_inf.mp hl).2) (hMP (Subgroup.mem_inf.mp hm).2), o,
    (Subgroup.mem_inf.mp ho).2, (Subgroup.mem_inf.mp ho).1, rfl⟩

/-- The stable-lift formula on bidual open-cell functions. Let `x` be a class of the
Jacquet module of `(i A)~` along `U`, and `ξ` the functional `[v] ↦ ⟨(C v)(1), t⟩`. Then
for every small compact open `K` with the two opposite Iwahori contractions,
`⟨Ψ(r̄(ι)[f_{t,K}]), x⟩ = c_K ξ(x)`. -/
theorem exists_forall_smoothDualPairing_cellFunction (hO : IsClosed (O : Set G))
    (hMO : M ≤ Subgroup.normalizer (O : Set G)) (g : G)
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, max uG uV} ⋙
        normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO ≅
      (jacquetFunctor.{uG, max uG uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV})
    (hΨ : IsStableLiftDuality.{uG, max uG uV} O M U hO hU hMO h.levi_le_normalizer g Ψ)
    (S : Subgroup G) [MeasurableSpace S] (μ : Measure S)
    (C : (normalizedInductionFunctor.{uG, uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV} ≅
      SmoothRep.contragredientFunctor.{0, uG, uV} ⋙ normalizedInductionFunctor.{uG, uV} h hU)
    (hC : IsNaturalIntegralDuality.{uG, uV} h hU S μ C)
    (A : SmoothRep.{0, uG, uV} ℂ M) (t : A)
    (ξ : SmoothDual ((jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient).representation)
    (hξ : ∀ v : ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient,
      smoothDualPairing _ ξ (Jacquet.Localization.mk
          ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient.representation
          U 1 v) =
        smoothDualPairing A.representation
          (Induction.eval P (inducingRepresentation h hU A.contragredient)
            (SmoothRep.hom (C.hom.app (Opposite.op A)) v) 1) t)
    (x : (jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient) :
    ∃ W : OpenSubgroup G, ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      Jacquet.IsIwahoriContraction K O M U g → Jacquet.IsIwahoriContraction K U M O g⁻¹ →
      K ≤ W → ∀ ht : t ∈ fixedVectors (inducingRepresentation h hU A)
        (Induction.conjOpenSubgroup P K 1).toSubgroup,
      smoothDualPairing _
          (SmoothRep.hom (Ψ.hom.app
            (Opposite.op ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient))
            (SmoothRep.hom ((normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO).map
              (SmoothRep.bidualHom.{0, uG, max uG uV}
                ((normalizedInductionFunctor.{uG, uV} h hU).obj A)))
              (Jacquet.Localization.mk
                ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation
                O 1 (cellFunction h hU A K hK t ht)))) x =
        cellConstant h hU S μ K * smoothDualPairing _ ξ x := by
  obtain ⟨W, hW⟩ := hΨ ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient x
  refine ⟨W, fun K hK hI hI' hKW ht => ?_⟩
  obtain ⟨v, hv, hvx, hΛ⟩ := hW K hK hI hI' hKW
  have hf := hom_mem_fixedVectors (SmoothRep.bidualHom.{0, uG, max uG uV}
    ((normalizedInductionFunctor.{uG, uV} h hU).obj A)) (cellFunction_mem_fixedVectors A K hK t ht)
  refine (hΛ _ hf).trans ?_
  rw [← hvx, hξ]
  exact smoothDualPairing_cellFunction S μ C hC A K hK t ht v hv

/-- The functional `[v] ↦ ⟨(C v)(1), t⟩` on the Jacquet module of `(i A)~` along `U` is the
image under `Ψ ∘ r̄(ι)` of a class in `r̄(i A)`, namely a multiple of the class of an
open-cell function `f_{t,K}`. -/
theorem exists_hom_map_bidualHom_eq (hproj : Continuous h.projection)
    (hPO : ∀ x : G, x ∈ P → x ∈ O → x = 1) (hO : IsClosed (O : Set G))
    (hMO : M ≤ Subgroup.normalizer (O : Set G)) (g : G)
    (hB : Jacquet.HasOppositeIwahoriContractionBasis O M U g)
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, max uG uV} ⋙
        normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO ≅
      (jacquetFunctor.{uG, max uG uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV})
    (hΨ : IsStableLiftDuality.{uG, max uG uV} O M U hO hU hMO h.levi_le_normalizer g Ψ)
    (S : Subgroup G) [MeasurableSpace S] (μ : Measure S)
    (C : (normalizedInductionFunctor.{uG, uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV} ≅
      SmoothRep.contragredientFunctor.{0, uG, uV} ⋙ normalizedInductionFunctor.{uG, uV} h hU)
    (hC : IsNaturalIntegralDuality.{uG, uV} h hU S μ C)
    (A : SmoothRep.{0, uG, uV} ℂ M) (t : A)
    (ξ : SmoothDual ((jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient).representation)
    (hξ : ∀ v : ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient,
      smoothDualPairing _ ξ (Jacquet.Localization.mk
          ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient.representation
          U 1 v) =
        smoothDualPairing A.representation
          (Induction.eval P (inducingRepresentation h hU A.contragredient)
            (SmoothRep.hom (C.hom.app (Opposite.op A)) v) 1) t) :
    ∃ b : (normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO).obj
        ((normalizedInductionFunctor.{uG, uV} h hU).obj A),
      SmoothRep.hom (Ψ.hom.app
          (Opposite.op ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient))
        (SmoothRep.hom ((normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO).map
          (SmoothRep.bidualHom.{0, uG, max uG uV}
            ((normalizedInductionFunctor.{uG, uV} h hU).obj A))) b) = ξ := by
  classical
  obtain ⟨Wt, hWt⟩ := exists_openSubgroup_forall_mem_fixedVectors hproj A t
  let Good : OpenSubgroup G → Prop := fun K => IsCompact (K : Set G) ∧
    Jacquet.IsIwahoriContraction K O M U g ∧ Jacquet.IsIwahoriContraction K U M O g⁻¹ ∧
      K ≤ Wt
  suffices hsuff : ∃ b, ((smoothDualPairing _).comp
      ((SmoothRep.hom (Ψ.hom.app (Opposite.op
          ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient))).toLinearMap.comp
        (SmoothRep.hom ((normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO).map
          (SmoothRep.bidualHom.{0, uG, max uG uV}
            ((normalizedInductionFunctor.{uG, uV} h hU).obj A)))).toLinearMap)) b =
      smoothDualPairing _ ξ by
    obtain ⟨b, hb⟩ := hsuff
    exact ⟨b, Subtype.ext (LinearMap.ext fun x => LinearMap.congr_fun hb x)⟩
  refine exists_eq_of_cellRelations _ _ Good ?_
    (fun K hK => Jacquet.Localization.mk
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).representation O 1
      (cellFunction h hU A K hK.1 t (hWt K hK.2.2.2))) (cellConstant h hU S μ) ?_ ?_ ?_
  · intro W
    obtain ⟨K, hKc, hKW, hI, hI'⟩ := hB ((W ⊓ Wt : OpenSubgroup G) : Set G) (W ⊓ Wt).isOpen
      (one_mem (W ⊓ Wt))
    exact ⟨K, ⟨hKc, hI, hI', fun x hx => (hKW hx).2⟩, fun x hx => (hKW hx).1⟩
  · intro x
    obtain ⟨W, hW⟩ := exists_forall_smoothDualPairing_cellFunction hO hMO g Ψ hΨ S μ C hC A t
      ξ hξ x
    exact ⟨W, fun K hK hKW => hW K hK.1 hK.2.1 hK.2.2.1 hKW (hWt K hK.2.2.2)⟩
  · intro K K₀ hK hK₀ hKK₀
    exact exists_mk_cellFunction_eq_smul hO A hPO hKK₀ hK.1 hK₀.1
      (exists_mul_of_isIwahoriContraction h.levi_le h.unipotent_le hK.2.1)
      (exists_mul_of_isIwahoriContraction h.levi_le h.unipotent_le hK₀.2.1) t _ _
  · intro K hK hc
    have hf0 : cellFunction h hU A K hK.1 t (hWt K hK.2.2.2) = 0 := by
      apply eq_zero_of_forall_fixed_smoothDualPairing hK.1
        (cellFunction_mem_fixedVectors A K hK.1 t _)
      intro ℓ hℓ
      rw [smoothDualPairing_cellFunction S μ C hC A K hK.1 t _ ℓ hℓ, hc, zero_mul]
    have ht0 : t = 0 := by
      rw [← cellFunction_apply_one A K hK.1 t (hWt K hK.2.2.2), hf0]
      rfl
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
      ((normalizedInductionFunctor.{uG, uV} h hU).obj A).contragredient.representation U 1 x
    refine (hξ v).trans ?_
    rw [ht0, map_zero]
    rfl

/-- Renard 2026, VI.9.6 (printed p.202): second adjointness `i ⊣ r̄` for `P = M ⋉ U` and an
opposite closed subgroup `O` normalized by `M` with `P ∩ O = 1`. The inputs are an exact
`r̄`, a natural duality `C : (i τ)~ ≅ i(τ~)` given by an integral of coefficients, and a
natural isomorphism `Ψ : r̄(V~) ≅ (r V)~` with Casselman's stable-lift property for a
contracting element `g` with a basis of opposite Iwahori contractions. -/
theorem nonempty_secondAdjunction_of_stableLift (hδ : IsUnimodularModulus U hU)
    (hproj : Continuous h.projection) (hPO : ∀ x : G, x ∈ P → x ∈ O → x = 1)
    (hO : IsClosed (O : Set G)) (hMO : M ≤ Subgroup.normalizer (O : Set G))
    (hR : SmoothRep.PreservesShortExact (normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO))
    (S : Subgroup G) [MeasurableSpace S] (μ : Measure S)
    (C : (normalizedInductionFunctor.{uG, max uG uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV} ≅
      SmoothRep.contragredientFunctor.{0, uG, max uG uV} ⋙
        normalizedInductionFunctor.{uG, max uG uV} h hU)
    (hC : IsNaturalIntegralDuality.{uG, max uG uV} h hU S μ C) (g : G)
    (hB : Jacquet.HasOppositeIwahoriContractionBasis O M U g)
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, max uG uV} ⋙
        normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO ≅
      (jacquetFunctor.{uG, max uG uV} h hU).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, max uG uV})
    (hΨ : IsStableLiftDuality.{uG, max uG uV} O M U hO hU hMO h.levi_le_normalizer g Ψ) :
    Nonempty (normalizedInductionFunctor.{uG, max uG uV} h hU ⊣
      normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO) := by
  refine SmoothRep.nonempty_adjunction_of_frobeniusChain_unit
    (compactOpenCofinal_of_nonarchimedean G) hR (firstAdjointnessAdjunction h hU hδ) C Ψ
    fun τ => ?_
  obtain ⟨η, hη⟩ := exists_comp_eq_of_injective
    ((normalizedJacquetFunctor.{uG, max uG uV} O M hO hMO).map
        (SmoothRep.bidualHom.{0, uG, max uG uV}
          ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj τ)) ≫
      Ψ.hom.app (Opposite.op ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj τ).contragredient))
    ((hom_injective_of_iso (Ψ.app (Opposite.op
        ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj τ).contragredient))).comp
      (hR.injective_map _ (SmoothRep.bidualHom_injective (compactOpenCofinal_of_nonarchimedean G)
        ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj τ))))
    (SmoothRep.bidualHom.{0, uG, max uG uV} τ ≫
      SmoothRep.contragredientHom
        ((firstAdjointnessAdjunction h hU hδ).counit.app τ.contragredient) ≫
      SmoothRep.contragredientHom
        ((jacquetFunctor.{uG, max uG uV} h hU).map (C.hom.app (Opposite.op τ))))
    (fun t => exists_hom_map_bidualHom_eq hproj hPO hO hMO g hB Ψ hΨ S μ C hC τ t _
      fun v => rfl)
  refine ⟨η, ?_⟩
  exact ((Iso.eq_comp_inv (Ψ.app (Opposite.op
      ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj τ).contragredient))).mpr
    ((Category.assoc _ _ _).trans hη)).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _)))

end Lift

end Langlands.Aubert.General
