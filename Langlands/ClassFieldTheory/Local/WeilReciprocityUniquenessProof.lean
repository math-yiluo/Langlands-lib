import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessStatement
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof

/-! # Uniqueness of geometric local Weil reciprocity -/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace WeilReciprocityUniqueness

open ReciprocitySystemUniqueness

section Galois

variable {K : Type u} [Field K] [PerfectField K]

/-- Every open subgroup of the absolute Galois abelianization is the kernel
of restriction to an actual finite abelian intermediate extension. -/
theorem exists_finiteAbelianExtension_of_isOpen
    (H : Subgroup (Field.absoluteGaloisGroupAbelianization K))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroupAbelianization K))) :
    ∃ L : FiniteAbelianExtension K,
      ∀ a : Field.absoluteGaloisGroupAbelianization K,
        a ∈ H ↔ L.abelianRestriction a = 1 := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let q : Gal(AlgebraicClosure K/K) →ₜ* Field.absoluteGaloisGroupAbelianization K :=
    absoluteAbelianizationProjection K
  let V : Subgroup Gal(AlgebraicClosure K/K) := H.comap q.toMonoidHom
  let : V.Normal := inferInstance
  have hVopen : IsOpen (V : Set Gal(AlgebraicClosure K/K)) :=
    hH.preimage q.continuous
  have hVclosed : IsClosed (V : Set Gal(AlgebraicClosure K/K)) :=
    Subgroup.isClosed_of_isOpen V hVopen
  let L := IntermediateField.fixedField V
  have hfix : L.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVclosed⟩
  let : FiniteDimensional K L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hVopen)
  let : IsGalois K L := IsGalois.of_fixedField_normal_subgroup V
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) L
  have hker : r.ker = V := L.restrictNormalHom_ker.trans hfix
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  have hcomm : IsMulCommutative Gal(L/K) := .of_comm fun a b => by
    obtain ⟨s, rfl⟩ := hr a
    obtain ⟨t, rfl⟩ := hr b
    apply mul_inv_eq_one.mp
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul]
    have hst : s * t * (t * s)⁻¹ ∈ V := by
      change q (s * t * (t * s)⁻¹) ∈ H
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (q t) (q s),
        mul_inv_cancel]
      exact H.one_mem
    exact show s * t * (t * s)⁻¹ ∈ r.ker from hker.symm ▸ hst
  let A : FiniteAbelianExtension K :=
    ⟨{ toIntermediateField := L }, hcomm⟩
  refine ⟨A, ?_⟩
  intro a
  induction a using QuotientGroup.induction_on with
  | H s =>
    change q s ∈ H ↔ r s = 1
    change s ∈ V ↔ s ∈ r.ker
    rw [hker]

/-- Finite norm kernels determine membership in every open subgroup of the
absolute Galois abelianization. -/
theorem mem_openSubgroup_iff
    [TopologicalSpace K]
    {r₁ r₂ : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K}
    (h₁ : ProfiniteNormResidueRelation r₁)
    (h₂ : ProfiniteNormResidueRelation r₂)
    (H : Subgroup (Field.absoluteGaloisGroupAbelianization K))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroupAbelianization K)))
    (a : Kˣ) :
    r₁ a ∈ H ↔ r₂ a ∈ H := by
  obtain ⟨L, hL⟩ := exists_finiteAbelianExtension_of_isOpen H hH
  rw [hL, hL]
  change a ∈ (finiteFamilyOfHom r₁ L).toMonoidHom.ker ↔
    a ∈ (finiteFamilyOfHom r₂ L).toMonoidHom.ker
  rw [(h₁.2.1 L).1, (h₂.2.1 L).1]

end Galois

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Compact inertia gives injectivity on the actual Weil abelianization. -/
theorem toGroupAbelianization_injective :
    Function.Injective
      (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F)) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  apply abelianizationMap_injective_of_compact_commutator
    (Weil.Local.localProjection F) (Weil.Local.localProjection_injective F)
    (Weil.Local.localProjection_denseRange F)
  have hle : (commutator (Weil.Local.localWeilGroup F)).topologicalClosure ≤
      (Weil.Local.localDegree F).toMonoidHom.ker :=
    Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker (Weil.Local.localDegree F).toMonoidHom)
      (isClosed_singleton.preimage (Weil.Local.localDegree F).continuous)
  exact (Weil.Local.localInertia_isCompact F).of_isClosed_subset
    (Subgroup.isClosed_topologicalClosure _) hle

/-- Reduction of geometric degree on the actual Galois abelianization. -/
def degreeMod (N : ℕ) [NeZero N] :
    Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ*
      Multiplicative (ZMod N) :=
  abelianizationLift
    ((profiniteIntegerMod N).comp (Weil.Local.localResidueDegree F))

theorem degreeMod_toGroupAbelianization (N : ℕ) [NeZero N]
    (w : WeilQuotients.Abelianization (Weil.Local.localResidueDegree F)) :
    degreeMod F N
        (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F) w) =
      Multiplicative.ofAdd
        ((Multiplicative.toAdd
          (WeilQuotients.degree (Weil.Local.localResidueDegree F) w) : ℤ) : ZMod N) := by
  induction w using QuotientGroup.induction_on with
  | H w =>
    change profiniteIntegerMod N
      (Weil.Local.localResidueDegree F (Weil.Local.localProjection F w)) = _
    rw [show Weil.Local.localResidueDegree F (Weil.Local.localProjection F w) =
      Weil.frobenius (Weil.Local.localDegree F w) from w.property]
    rfl

variable (T : F.TopologicalData)

theorem candidateGaloisHom_eq_of_order_ne_zero
    {e₁ e₂ : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)}
    (h₁ : GeometricWeilReciprocityRelation F T e₁)
    (h₂ : GeometricWeilReciprocityRelation F T e₂)
    (a : F.Carrierˣ) (ha : T.ord (a : F.Carrier) ≠ 0) :
    candidateGaloisHom T (Weil.Local.localResidueDegree F) e₁ a =
      candidateGaloisHom T (Weil.Local.localResidueDegree F) e₂ a := by
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let := absoluteGaloisNonarchimedean F.Carrier
  let := abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  let := quotientNonarchimedean
    (commutator (Field.absoluteGaloisGroup F.Carrier)).topologicalClosure
  refine eq_of_forall_openSubgroup ?_ (T.ord (a : F.Carrier)) ha ?_
  · intro H hH hmem
    exact (mem_openSubgroup_iff h₁.2.1 h₂.2.1 H hH a).mp hmem
  · intro N hN
    let : NeZero N := ⟨hN⟩
    refine ⟨(degreeMod F N).toMonoidHom, ?_, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod N)))).preimage
        (degreeMod F N).continuous
    · change degreeMod F N
        (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F)
          (e₁.symm a)) = _
      rw [degreeMod_toGroupAbelianization]
      have h := DFunLike.congr_fun h₁.1 (e₁.symm a)
      change T.orderHom (e₁ (e₁.symm a)) =
        WeilQuotients.degree _ (e₁.symm a) at h
      rw [e₁.apply_symm_apply] at h
      have hd : WeilQuotients.degree (Weil.Local.localResidueDegree F) (e₁.symm a) =
          T.orderHom a := h.symm
      rw [hd]
      rfl
    · change degreeMod F N
        (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F)
          (e₂.symm a)) = _
      rw [degreeMod_toGroupAbelianization]
      have h := DFunLike.congr_fun h₂.1 (e₂.symm a)
      change T.orderHom (e₂ (e₂.symm a)) =
        WeilQuotients.degree _ (e₂.symm a) at h
      rw [e₂.apply_symm_apply] at h
      have hd : WeilQuotients.degree (Weil.Local.localResidueDegree F) (e₂.symm a) =
          T.orderHom a := h.symm
      rw [hd]
      rfl

/-- Uniformizer cancellation extends comparison to all field units. -/
theorem candidateGaloisHom_eq
    {e₁ e₂ : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)}
    (h₁ : GeometricWeilReciprocityRelation F T e₁)
    (h₂ : GeometricWeilReciprocityRelation F T e₂)
    (a : F.Carrierˣ) :
    candidateGaloisHom T (Weil.Local.localResidueDegree F) e₁ a =
      candidateGaloisHom T (Weil.Local.localResidueDegree F) e₂ a := by
  let := T.topology
  by_cases ha : T.ord (a : F.Carrier) ≠ 0
  · exact candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ a ha
  · have ha0 : T.ord (a : F.Carrier) = 0 := not_ne_iff.mp ha
    let π := LocalFactor.PadicAbelian.uniformizerUnit T
    have hπ : T.ord (π : F.Carrier) = 1 :=
      LocalFactor.PadicAbelian.uniformizerUnit_ord T
    have hap : T.ord ((a * π : F.Carrierˣ) : F.Carrier) ≠ 0 := by
      change T.ord ((a : F.Carrier) * (π : F.Carrier)) ≠ 0
      rw [T.ord_mul a.ne_zero π.ne_zero, ha0, hπ]
      norm_num
    have heπ := candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ π (by
      rw [hπ]
      norm_num)
    have heap := candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ (a * π) hap
    rw [map_mul, map_mul, heπ] at heap
    exact mul_right_cancel heap

end Local

end WeilReciprocityUniqueness

/-- Uniqueness of geometric local Weil reciprocity in every carrier universe. -/
theorem geometricWeilReciprocityUniqueness :
    GeometricWeilReciprocityUniqueness.{u} := by
  intro p _ F T e₁ e₂ h₁ h₂
  let := T.topology
  have hinv : ∀ a : F.Carrierˣ, e₁.symm a = e₂.symm a := by
    intro a
    apply WeilReciprocityUniqueness.toGroupAbelianization_injective F
    exact WeilReciprocityUniqueness.candidateGaloisHom_eq F T h₁ h₂ a
  apply ContinuousMulEquiv.ext
  intro w
  have hw := hinv (e₁ w)
  rw [ContinuousMulEquiv.symm_apply_apply] at hw
  exact (congrArg e₂ hw).trans (e₂.apply_symm_apply (e₁ w)) |>.symm

end Langlands.LocalClassField
