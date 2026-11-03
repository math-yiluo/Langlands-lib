import Langlands.Representation.Induction.CompactLocalSection
import Mathlib.GroupTheory.DoubleCoset

/-!
# A finite model for fixed vectors of smooth induction

Evaluation at distinct representatives of `P \ G / K` identifies the `K`-fixed
vectors of smooth induction with the product of the corresponding coefficient
fixed spaces. The inverse is the finite sum of actual compact double-coset
sections.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- The compact section at `x`, regarded as a `K`-fixed smooth induced vector. -/
def fixedDoubleCosetSection (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) :
    fixedVectors (smoothInduced P σ) K.toSubgroup :=
  ⟨(compactDoubleCosetSection P σ K hK x v.1 v.2).val, by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    funext y
    exact compactDoubleCosetSection_mul P σ K hK x v.1 v.2 k y⟩

/-- The section has the prescribed value at its representative. -/
theorem fixedDoubleCosetSection_eval_self (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) :
    eval P σ (fixedDoubleCosetSection P σ K hK x v).val x = v.val := by
  change eval P σ (compactDoubleCosetSection P σ K hK x v.1 v.2).val x = v.val
  simpa only [OneMemClass.coe_one, one_mul, mul_one, map_one, Module.End.one_apply] using
    compactDoubleCosetSection_apply P σ K hK x v.1 v.2 1 1

/-- The section vanishes at representatives of other double cosets. -/
theorem fixedDoubleCosetSection_eval_of_ne (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) {y : G}
    (hy : DoubleCoset.mk P K.toSubgroup y ≠ DoubleCoset.mk P K.toSubgroup x) :
    eval P σ (fixedDoubleCosetSection P σ K hK x v).val y = 0 := by
  by_contra hn
  obtain ⟨k, hk, he⟩ :=
    compactDoubleCosetSection_support_subset P σ K hK x v.1 v.2 ⟨y, hn, rfl⟩
  have hp : y * (x * k)⁻¹ ∈ P :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  apply hy
  exact (DoubleCoset.eq.mpr ⟨y * (x * k)⁻¹, hp, k, hk, by group⟩).symm

/-- Sum the compact sections attached to a finite family of coefficient vectors. -/
def fixedSectionSum (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (v : (i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    fixedVectors (smoothInduced P σ) K.toSubgroup :=
  ∑ i : t, fixedDoubleCosetSection P σ K hK i (v i)

/-- Distinct double cosets allow arbitrary prescribed values at the representatives. -/
theorem fixedEvaluation_fixedSectionSum (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (ht : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (v : (i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    fixedEvaluation P σ K t (fixedSectionSum P σ K hK t v) = v := by
  classical
  funext j
  apply Subtype.ext
  let ev : fixedVectors (smoothInduced P σ) K.toSubgroup →ₗ[R] V :=
    { toFun := fun f => eval P σ f.val j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (∑ i : t, fixedDoubleCosetSection P σ K hK i (v i)) = (v j).val
  rw [map_sum, Finset.sum_eq_single j]
  · exact fixedDoubleCosetSection_eval_self P σ K hK j (v j)
  · intro i _ hij
    exact fixedDoubleCosetSection_eval_of_ne P σ K hK i (v i)
      (fun he => hij (ht he.symm))
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Evaluation at finitely many distinct double cosets is surjective. -/
theorem fixedEvaluation_surjective (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (ht : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G))) :
    Function.Surjective (fixedEvaluation P σ K t) :=
  fun v => ⟨fixedSectionSum P σ K hK t v,
    fixedEvaluation_fixedSectionSum P σ K hK t ht v⟩

/-- Evaluation is bijective for a finite double-coset transversal. -/
theorem fixedEvaluation_bijective (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G))) :
    Function.Bijective (fixedEvaluation P σ K t) :=
  ⟨fixedEvaluation_injective P σ K t hcover,
    fixedEvaluation_surjective P σ K hK t hdistinct⟩

/-- The actual linear equivalence given by evaluation on a finite double-coset
transversal. -/
def fixedEvaluationEquiv (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G))) :
    fixedVectors (smoothInduced P σ) K.toSubgroup ≃ₗ[R]
      ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :=
  LinearEquiv.ofBijective (fixedEvaluation P σ K t)
    (fixedEvaluation_bijective P σ K hK t hcover hdistinct)

/-- The forward map of the equivalence is the existing evaluation map. -/
theorem fixedEvaluationEquiv_toLinearMap (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G))) :
    (fixedEvaluationEquiv P σ K hK t hcover hdistinct).toLinearMap =
      fixedEvaluation P σ K t := rfl

/-- The inverse equivalence is the explicit finite sum of compact sections. -/
theorem fixedEvaluationEquiv_symm_apply (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (v : (i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    (fixedEvaluationEquiv P σ K hK t hcover hdistinct).symm v =
      fixedSectionSum P σ K hK t v := by
  apply (fixedEvaluationEquiv P σ K hK t hcover hdistinct).injective
  exact (fixedEvaluationEquiv P σ K hK t hcover hdistinct).apply_symm_apply v |>.trans
    (fixedEvaluation_fixedSectionSum P σ K hK t hdistinct v).symm

omit [CommRing R] [AddCommGroup V] [Module R V] in
/-- Compactness of `P \ G` supplies a finite cover with no repeated double cosets. -/
theorem exists_finset_doubleCoset_representatives (P : Subgroup G)
    [CompactSpace (LeftQuotient P)] (K : OpenSubgroup G) :
    ∃ t : Finset G,
      (∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k) ∧
      Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_doubleCoset_cover P K
  have hfinite : Finite (DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G)) := by
    apply Finite.of_surjective (fun i : s => DoubleCoset.mk P K.toSubgroup (i : G))
    intro q
    obtain ⟨i, hi, p, hp, k, hk, he⟩ := hs q.out
    exact ⟨⟨i, hi⟩, (DoubleCoset.eq.mpr ⟨p, hp, k, hk, he⟩).trans
      (DoubleCoset.out_eq' q)⟩
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G))
  refine ⟨Finset.univ.image
    (fun q : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G) => q.out), ?_, ?_⟩
  · intro x
    let q := DoubleCoset.mk P K.toSubgroup x
    obtain ⟨p, hp, k, hk, he⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' q)
    exact ⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩, p, hp, k, hk, he⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    obtain ⟨qx, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨qy, _, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg Quotient.out
      ((DoubleCoset.out_eq' qx).symm.trans (h.trans (DoubleCoset.out_eq' qy)))

end Langlands.Induction
