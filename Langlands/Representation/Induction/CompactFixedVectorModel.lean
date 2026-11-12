import Langlands.Representation.Induction.FixedVectorModel
import Mathlib.LinearAlgebra.DFinsupp

/-! # Finite-support fixed vectors of actual compact induction -/

noncomputable section

open Classical

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- Forget compact support on a fixed compactly induced vector. -/
def compactFixedToSmooth (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) :
    fixedVectors (compactInduced P σ) K.toSubgroup →ₗ[R]
      fixedVectors (smoothInduced P σ) K.toSubgroup where
  toFun f := ⟨f.val.val, fun k => congrArg Subtype.val (f.property k)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of a compactly induced fixed vector, with its coefficient stabilizer. -/
def compactFixedEvaluationAt (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) :
    fixedVectors (compactInduced P σ) K.toSubgroup →ₗ[R]
      fixedVectors σ (conjOpenSubgroup P K x).toSubgroup where
  toFun f := ⟨eval P σ f.val.val x,
    eval_mem_fixedVectors P σ K x (compactFixedToSmooth P σ K f).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Only finitely many double cosets have nonzero values for a fixed compact section. -/
theorem compactFixedEvaluation_finite (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G)
    (f : fixedVectors (compactInduced P σ) K.toSubgroup) :
    ∃ s : Finset (DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G)),
      ∀ q, compactFixedEvaluationAt P σ K q.out f ≠ 0 → q ∈ s := by
  classical
  have hopen : IsOpenMap (quotientMap P) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨t, ht⟩ := f.val.property.elim_finite_subcover
    (fun i : G => quotientMap P '' ((fun k => i * k) '' (K : Set G)))
    (fun i => hopen _ (isOpenMap_mul_left i _ K.isOpen))
    (by
      rintro _ ⟨y, -, rfl⟩
      exact Set.mem_iUnion.mpr ⟨y, y, ⟨1, K.one_mem, mul_one y⟩, rfl⟩)
  refine ⟨t.image (DoubleCoset.mk P K.toSubgroup), ?_⟩
  intro q hq
  have hval : eval P σ f.val.val q.out ≠ 0 := by
    intro hz
    apply hq
    exact Subtype.ext hz
  have hcover := ht ⟨q.out, hval, rfl⟩
  simp only [Set.mem_iUnion] at hcover
  obtain ⟨i, hi, _, ⟨k, hk, rfl⟩, he⟩ := hcover
  have hp : q.out * (i * k)⁻¹ ∈ P :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  apply Finset.mem_image.mpr
  refine ⟨i, hi, ?_⟩
  exact (DoubleCoset.eq.mpr ⟨q.out * (i * k)⁻¹, hp, k, hk,
    by group⟩).trans (DoubleCoset.out_eq' q)

/-- Evaluation on all double-coset representatives lands in the dependent direct sum. -/
def compactFixedEvaluation (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) :
    fixedVectors (compactInduced P σ) K.toSubgroup →ₗ[R]
      Π₀ q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G),
        fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup where
  toFun f := by
    classical
    let h := compactFixedEvaluation_finite P σ K f
    exact ⟨fun q => compactFixedEvaluationAt P σ K q.out f,
      Trunc.mk ⟨h.choose.val, fun q => by
        by_cases hz : compactFixedEvaluationAt P σ K q.out f = 0
        · exact Or.inr hz
        · exact Or.inl (h.choose_spec q hz)⟩⟩
  map_add' f g := by
    apply DFinsupp.ext
    intro q
    exact map_add (compactFixedEvaluationAt P σ K q.out) f g
  map_smul' r f := by
    apply DFinsupp.ext
    intro q
    exact map_smul (compactFixedEvaluationAt P σ K q.out) r f

@[simp] theorem compactFixedEvaluation_apply (P : Subgroup G)
    (σ : Representation R P V) (K : OpenSubgroup G)
    (f : fixedVectors (compactInduced P σ) K.toSubgroup)
    (q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G)) :
    compactFixedEvaluation P σ K f q = compactFixedEvaluationAt P σ K q.out f := rfl

/-- All double-coset values determine a compactly induced fixed vector. -/
theorem compactFixedEvaluation_injective (P : Subgroup G)
    (σ : Representation R P V) (K : OpenSubgroup G) :
    Function.Injective (compactFixedEvaluation P σ K) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let q := DoubleCoset.mk P K.toSubgroup x
  obtain ⟨p, hp, k, hk, hx⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' q)
  have hz : eval P σ f.val.val q.out = 0 :=
    congrArg Subtype.val (DFunLike.congr_fun hf q)
  have hr : eval P σ f.val.val (p * q.out * k) =
      eval P σ f.val.val (p * q.out) :=
    eval_mul_of_mem_fixedVectors P σ K.toSubgroup
      (compactFixedToSmooth P σ K f).property ⟨k, hk⟩ (p * q.out)
  change eval P σ f.val.val x = 0
  rw [hx, hr]
  exact (eval_covariant P σ f.val.val ⟨p, hp⟩ q.out).trans (by rw [hz, map_zero])

/-- The actual compact section attached to one double-coset coefficient. -/
def compactFixedSection (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G))
    (v : fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup) :
    fixedVectors (compactInduced P σ) K.toSubgroup :=
  ⟨compactDoubleCosetSection P σ K hK q.out v.val v.property, by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext y
    exact compactDoubleCosetSection_mul P σ K hK q.out v.val v.property k y⟩

/-- The double-coset section has exactly its prescribed nonzero coordinate. -/
theorem compactFixedEvaluation_section (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G))
    (v : fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup) :
    compactFixedEvaluation P σ K (compactFixedSection P σ K hK q v) =
      DFinsupp.single q v := by
  classical
  apply DFinsupp.ext
  intro r
  by_cases hr : q = r
  · subst r
    rw [DFinsupp.single_eq_same]
    apply Subtype.ext
    exact fixedDoubleCosetSection_eval_self P σ K hK q.out v
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hr)]
    apply Subtype.ext
    exact fixedDoubleCosetSection_eval_of_ne P σ K hK q.out v
      (by simpa only [DoubleCoset.out_eq'] using Ne.symm hr)

/-- The one-coordinate section depends linearly on its fixed coefficient. -/
def compactFixedSectionLinear (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G)) :
    fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup →ₗ[R]
      fixedVectors (compactInduced P σ) K.toSubgroup where
  toFun := compactFixedSection P σ K hK q
  map_add' v w := by
    apply compactFixedEvaluation_injective P σ K
    rw [map_add, compactFixedEvaluation_section, compactFixedEvaluation_section,
      compactFixedEvaluation_section, DFinsupp.single_add]
  map_smul' a v := by
    apply compactFixedEvaluation_injective P σ K
    rw [map_smul, compactFixedEvaluation_section, compactFixedEvaluation_section,
      DFinsupp.single_smul]
    rfl

/-- Finite sums of compact double-coset sections realize every finite-support
family of fixed coefficient vectors. -/
def compactFixedSectionSum (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (Π₀ q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G),
      fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup) →ₗ[R]
        fixedVectors (compactInduced P σ) K.toSubgroup :=
  DFinsupp.lsum R (compactFixedSectionLinear P σ K hK)

/-- Evaluation after forming the finite section sum is the identity. -/
theorem compactFixedEvaluation_sectionSum (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (compactFixedEvaluation P σ K).comp (compactFixedSectionSum P σ K hK) =
      LinearMap.id := by
  apply DFinsupp.lhom_ext
  intro q v
  change compactFixedEvaluation P σ K
    (DFinsupp.lsum R (compactFixedSectionLinear P σ K hK) (DFinsupp.single q v)) = _
  rw [DFinsupp.lsum_single]
  exact compactFixedEvaluation_section P σ K hK q v

/-- Evaluation is a linear equivalence for every compact open subgroup, even
when the double-coset space is infinite. -/
def compactFixedEvaluationEquiv (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    fixedVectors (compactInduced P σ) K.toSubgroup ≃ₗ[R]
      Π₀ q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G),
        fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup where
  __ := compactFixedEvaluation P σ K
  invFun := compactFixedSectionSum P σ K hK
  left_inv f := by
    apply compactFixedEvaluation_injective P σ K
    exact DFunLike.congr_fun (compactFixedEvaluation_sectionSum P σ K hK) _
  right_inv v := DFunLike.congr_fun (compactFixedEvaluation_sectionSum P σ K hK) v

@[simp] theorem compactFixedEvaluationEquiv_apply (P : Subgroup G)
    (σ : Representation R P V) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : fixedVectors (compactInduced P σ) K.toSubgroup) :
    compactFixedEvaluationEquiv P σ K hK f = compactFixedEvaluation P σ K f := rfl

@[simp] theorem compactFixedEvaluationEquiv_symm_apply (P : Subgroup G)
    (σ : Representation R P V) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : Π₀ q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G),
      fixedVectors σ (conjOpenSubgroup P K q.out).toSubgroup) :
    (compactFixedEvaluationEquiv P σ K hK).symm v =
      compactFixedSectionSum P σ K hK v := rfl

end Langlands.Induction
