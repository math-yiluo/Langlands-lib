import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Analysis.Local.QuotientInvariantComparison
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Left quotients of product groups

For subgroups `A ≤ G₁` and `B ≤ G₂` of topological groups, the left quotient
`(A × B) \ (G₁ × G₂)` is homeomorphic to `A \ G₁ × B \ G₂`, compatibly with right translations;
likewise for a product `∏_i A_i ≤ ∏_i G_i` of an arbitrary family. The carrier of a product
subgroup is isomorphic, as a topological group, to the product of the carriers. A Haar measure on
a second countable locally compact group isomorphic to a group carrying a right-invariant Haar
measure is right invariant. See the paired Markdown.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Topology

universe u₁ u₂ uι uG

section Prod

variable {G₁ : Type u₁} {G₂ : Type u₂} [Group G₁] [Group G₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  (A : Subgroup G₁) (B : Subgroup G₂)

theorem leftQuotient_mk_eq_mk_iff {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    (Quotient.mk _ x : LeftQuotient H) = Quotient.mk _ y ↔ y * x⁻¹ ∈ H :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

theorem leftQuotient_mk_out_eq {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    x * (Quotient.mk _ x : LeftQuotient H).out⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp (Quotient.mk_out x)

/-- `(A × B) \ (G₁ × G₂) ≃ₜ A \ G₁ × B \ G₂`, `[(x, y)] ↦ ([x], [y])`. -/
def leftQuotientProdHomeomorph :
    LeftQuotient (A.prod B) ≃ₜ LeftQuotient A × LeftQuotient B where
  toFun := Quotient.lift (fun x : G₁ × G₂ =>
      ((Quotient.mk _ x.1 : LeftQuotient A), (Quotient.mk _ x.2 : LeftQuotient B))) (by
    intro x y h
    have h' : y * x⁻¹ ∈ A.prod B := QuotientGroup.rightRel_apply.mp h
    rw [Subgroup.mem_prod] at h'
    exact Prod.ext ((leftQuotient_mk_eq_mk_iff A _ _).mpr h'.1)
      ((leftQuotient_mk_eq_mk_iff B _ _).mpr h'.2))
  invFun p := Quotient.mk _ (p.1.out, p.2.out)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      refine (leftQuotient_mk_eq_mk_iff _ _ _).mpr ?_
      rw [Subgroup.mem_prod]
      exact ⟨leftQuotient_mk_out_eq A x.1, leftQuotient_mk_out_eq B x.2⟩
  right_inv p := Prod.ext (Quotient.out_eq p.1) (Quotient.out_eq p.2)
  continuous_toFun :=
    Continuous.quotient_lift ((continuous_quotient_mk'.comp continuous_fst).prodMk
      (continuous_quotient_mk'.comp continuous_snd)) _
  continuous_invFun := by
    have hq := (leftQuotient_isOpenQuotientMap A).prodMap (leftQuotient_isOpenQuotientMap B)
    refine hq.isQuotientMap.continuous_iff.mpr ?_
    have he : (fun p : LeftQuotient A × LeftQuotient B =>
        (Quotient.mk _ (p.1.out, p.2.out) : LeftQuotient (A.prod B))) ∘
          Prod.map (leftQuotientMap A) (leftQuotientMap B) =
        leftQuotientMap (A.prod B) := by
      funext x
      refine (leftQuotient_mk_eq_mk_iff _ _ _).mpr ?_
      rw [Subgroup.mem_prod]
      exact ⟨leftQuotient_mk_out_eq A x.1, leftQuotient_mk_out_eq B x.2⟩
    rw [he]
    exact continuous_quotient_mk'

@[simp]
theorem leftQuotientProdHomeomorph_mk (x : G₁ × G₂) :
    leftQuotientProdHomeomorph A B (Quotient.mk _ x) =
      ((Quotient.mk _ x.1 : LeftQuotient A), (Quotient.mk _ x.2 : LeftQuotient B)) :=
  rfl

theorem leftQuotientProdHomeomorph_rightTranslate (g : G₁ × G₂) (q : LeftQuotient (A.prod B)) :
    leftQuotientProdHomeomorph A B (rightTranslate (A.prod B) g q) =
      Prod.map (rightTranslate A g.1) (rightTranslate B g.2)
        (leftQuotientProdHomeomorph A B q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The carrier of a product subgroup is the product of the carriers. -/
def prodSubgroupHomeomorph : (A.prod B) ≃ₜ* A × B where
  toMulEquiv := Subgroup.prodEquiv A B
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
@[simp]
theorem prodSubgroupHomeomorph_apply (x : A.prod B) :
    prodSubgroupHomeomorph A B x = (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  rfl

end Prod

section Pi

variable {ι : Type uι} {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] (A : ∀ i, Subgroup (G i))

/-- `(∏_i A_i) \ (∏_i G_i) ≃ₜ ∏_i A_i \ G_i`, `[x] ↦ ([x_i])_i`. -/
def leftQuotientPiHomeomorph :
    LeftQuotient (Subgroup.pi Set.univ A) ≃ₜ ∀ i, LeftQuotient (A i) where
  toFun := Quotient.lift (fun x : ∀ i, G i => fun i => (Quotient.mk _ (x i) : LeftQuotient (A i)))
    (by
      intro x y h
      have h' : y * x⁻¹ ∈ Subgroup.pi Set.univ A := QuotientGroup.rightRel_apply.mp h
      rw [Subgroup.mem_pi] at h'
      funext i
      exact (leftQuotient_mk_eq_mk_iff (A i) _ _).mpr (h' i (Set.mem_univ i)))
  invFun p := Quotient.mk _ (fun i => (p i).out)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      refine (leftQuotient_mk_eq_mk_iff _ _ _).mpr ?_
      rw [Subgroup.mem_pi]
      exact fun i _ => leftQuotient_mk_out_eq (A i) (x i)
  right_inv p := funext fun i => Quotient.out_eq (p i)
  continuous_toFun :=
    Continuous.quotient_lift (continuous_pi fun i =>
      continuous_quotient_mk'.comp (continuous_apply i)) _
  continuous_invFun := by
    have hq := IsOpenQuotientMap.piMap fun i => leftQuotient_isOpenQuotientMap (A i)
    refine hq.isQuotientMap.continuous_iff.mpr ?_
    have he : (fun p : ∀ i, LeftQuotient (A i) =>
        (Quotient.mk _ (fun i => (p i).out) : LeftQuotient (Subgroup.pi Set.univ A))) ∘
          Pi.map (fun i => leftQuotientMap (A i)) =
        leftQuotientMap (Subgroup.pi Set.univ A) := by
      funext x
      refine (leftQuotient_mk_eq_mk_iff _ _ _).mpr ?_
      rw [Subgroup.mem_pi]
      intro i _
      exact leftQuotient_mk_out_eq (A i) (x i)
    rw [he]
    exact continuous_quotient_mk'

@[simp]
theorem leftQuotientPiHomeomorph_mk (x : ∀ i, G i) :
    leftQuotientPiHomeomorph A (Quotient.mk _ x) =
      fun i => (Quotient.mk _ (x i) : LeftQuotient (A i)) :=
  rfl

theorem leftQuotientPiHomeomorph_rightTranslate (g : ∀ i, G i)
    (q : LeftQuotient (Subgroup.pi Set.univ A)) :
    leftQuotientPiHomeomorph A (rightTranslate (Subgroup.pi Set.univ A) g q) =
      Pi.map (fun i => rightTranslate (A i) (g i)) (leftQuotientPiHomeomorph A q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The carrier of a product subgroup of a product of groups is the product of the carriers. -/
def piSubgroupHomeomorph : (Subgroup.pi Set.univ A) ≃ₜ* ∀ i, A i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

end Pi

section Measure

/-- A measure transported along a measurable equivalence is preserved by a map that the
equivalence intertwines with a measure-preserving map. -/
theorem measurePreserving_map_symm_of_conj {Q X : Type*} [MeasurableSpace Q] [MeasurableSpace X]
    (Θ : Q ≃ᵐ X) (P : Measure X) {T : Q → Q} {T' : X → X} (hT : Measurable T)
    (hconj : ∀ q, Θ (T q) = T' (Θ q)) (hT' : MeasurePreserving T' P P) :
    MeasurePreserving T (Measure.map Θ.symm P) (Measure.map Θ.symm P) := by
  refine ⟨hT, ?_⟩
  have hc : T ∘ Θ.symm = Θ.symm ∘ T' := by
    funext x
    apply Θ.injective
    simp only [Function.comp_apply, hconj, MeasurableEquiv.apply_symm_apply]
  rw [Measure.map_map hT Θ.symm.measurable, hc,
    ← Measure.map_map Θ.symm.measurable hT'.measurable, hT'.map_eq]

variable {N : Type u₁} {M : Type u₂} [Group N] [Group M] [TopologicalSpace N]
  [TopologicalSpace M] [IsTopologicalGroup N] [IsTopologicalGroup M]
  [LocallyCompactSpace M] [SecondCountableTopology M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace M] [BorelSpace M]

/-- Unimodularity transfers along an isomorphism of topological groups: if `M` carries a
right-invariant Haar measure, every Haar measure on a group isomorphic to `M` is right
invariant. -/
theorem isMulRightInvariant_of_continuousMulEquiv (e : N ≃ₜ* M) (μ : Measure M)
    [IsHaarMeasure μ] [IsMulRightInvariant μ] (ν : Measure N) [IsHaarMeasure ν] :
    IsMulRightInvariant ν := by
  have : IsHaarMeasure (Measure.map e ν) := e.isHaarMeasure_map ν
  have h := isMulLeftInvariant_eq_smul (Measure.map e ν) μ
  have hR : IsMulRightInvariant (Measure.map e ν) := by
    rw [h]
    infer_instance
  have h2 := isMulRightInvariant_map e.symm (Measure.map e ν)
  have hid : Measure.map (e.symm : M → N) (Measure.map (e : N → M) ν) = ν := by
    rw [Measure.map_map (map_continuous e.symm).measurable (map_continuous e).measurable]
    convert Measure.map_id
    funext x
    exact e.symm_apply_apply x
  rwa [hid] at h2

end Measure

end Langlands.QuotientIntegration
