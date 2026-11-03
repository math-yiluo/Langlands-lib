import Langlands.Representation.Aubert.General.InductionTarget
import Langlands.Representation.Aubert.General.InvolutivityTarget

/-!
# Involutivity from induction compatibility, term transitivity and the top term

Aubert's proof of Theorem 1.7(3) (printed p. 2183) derives `D_G ∘ D_G = id`
from Theorem 1.7(2), transitivity of normalized induction and Jacquet
restriction, an alternating sum over subsets, and the identity `i_S ∘ r_S = id`
for the full index set. This module carries out that K0 computation for an
arbitrary family `P I = M I ⋉ U I` indexed by the finite subsets of a finite
type `ι`. It proves none of the three representation-theoretic inputs; the
final theorem takes them as explicit hypotheses.
-/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

section Combinatorics

variable {ι : Type uI} [Fintype ι]

/-- For a fixed `K`, `∑_{K ⊆ J} (-1)^{|J| + |K|}` is `1` when `K` is the whole
index set and `0` otherwise. -/
theorem sum_superset_neg_one_pow_card [DecidableEq ι] (K : Finset ι) :
    ∑ J ∈ Finset.univ.filter (K ⊆ ·), (-1 : ℤ) ^ (J.card + K.card) =
      if K = Finset.univ then 1 else 0 := by
  have hbij : ∑ J ∈ Finset.univ.filter (K ⊆ ·), (-1 : ℤ) ^ (J.card + K.card) =
      ∑ L ∈ (Finset.univ \ K).powerset, (-1 : ℤ) ^ L.card := by
    refine Finset.sum_nbij' (fun J => J \ K) (fun L => L ∪ K) ?_ ?_ ?_ ?_ ?_
    · intro J _
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.subset_univ J) le_rfl
    · intro L _
      simp
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      exact Finset.sdiff_union_of_subset hJ
    · intro L hL
      simp only [Finset.mem_powerset] at hL
      exact Finset.union_sdiff_cancel_right
        (Finset.disjoint_of_subset_left hL Finset.sdiff_disjoint)
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      rw [← Finset.card_sdiff_add_card_eq_card hJ, add_assoc, pow_add, ← two_mul, pow_mul]
      simp
  rw [hbij, Finset.sum_powerset_neg_one_pow_card]
  simp only [Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff]

omit [Fintype ι] in
/-- Summing over the subsets of each `J` read as subsets of `ι` is summing over
`J.powerset`. -/
theorem sum_leviIndex_eq_sum_powerset {A : Type*} [AddCommMonoid A] (J : Finset ι)
    (f : Finset ι → A) :
    ∑ I : Finset J, f (leviIndex J I) = ∑ K ∈ J.powerset, f K := by
  classical
  refine Finset.sum_nbij' (leviIndex J) (fun K => K.subtype (· ∈ J)) ?_ ?_ ?_ ?_ ?_
  · intro I _
    simp only [Finset.mem_powerset]
    intro x hx
    exact Finset.property_of_mem_map_subtype I hx
  · intro K _
    simp
  · intro I _
    ext x
    simp
  · intro K hK
    simp only [Finset.mem_powerset] at hK
    exact Finset.subtype_map_of_mem fun x hx => hK hx
  · intro I _
    rfl

/-- The alternating double sum of Aubert's proof:
`∑_J (-1)^{|J|} ∑_{I ⊆ J} (-1)^{|I|} E_I = E_ι`, for the subsets `I` of `J`
read as subsets of `ι`. -/
theorem sum_neg_one_pow_smul_sum_leviIndex {A : Type*} [AddCommGroup A]
    (E : Finset ι → A) :
    ∑ J : Finset ι, ((-1 : ℤ) ^ J.card) •
        ∑ I : Finset J, ((-1 : ℤ) ^ I.card) • E (leviIndex J I) =
      E Finset.univ := by
  classical
  have h1 : ∀ J : Finset ι, ∑ I : Finset J, ((-1 : ℤ) ^ I.card) • E (leviIndex J I) =
      ∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • E K := by
    intro J
    simp_rw [← card_leviIndex J]
    exact sum_leviIndex_eq_sum_powerset J fun K => ((-1 : ℤ) ^ K.card) • E K
  simp_rw [h1, Finset.smul_sum, smul_smul, ← pow_add]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun K => Finset.univ.filter (K ⊆ ·))]
  · simp_rw [← Finset.sum_smul, sum_superset_neg_one_pow_card]
    simp [ite_smul]
  · intro J K
    simp [Finset.mem_powerset]

end Combinatorics

section Reduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hLevi : ∀ (J : Finset ι) (I : Finset J),
    IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J))
      ((U (leviIndex J I)).subgroupOf (M J)))
  (hLeviFl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hLevi J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))

/-- Two-sided transitivity of the terms on exact K0: for every `J` and every
`I ⊆ J`, `i_J ∘ (i^{M_J}_I ∘ r^{M_J}_I) ∘ r_J = i_I ∘ r_I`, where the middle
term is the `I`-th term of the Levi operator of `leviAlternatingOperator`, built
from the restricted decompositions inside `M J`. It is the K0 consequence of
transitivity of normalized induction and normalized Jacquet restriction used in
Aubert's proof of Theorem 1.7(3). This definition states the identity and
proves no instance of it. -/
def TermTransitivityStatement : Prop :=
  ∀ (J : Finset ι) (I : Finset J),
    letI := (hM J).locallyCompactSpace
    (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
        ((alternatingTerm (fun I : Finset J => (P (leviIndex J I)).subgroupOf (M J))
            (fun I => (M (leviIndex J I)).subgroupOf (M J))
            (fun I => (U (leviIndex J I)).subgroupOf (M J)) (hLevi J)
            (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val) (hLeviFl J) I).comp
          (jacquetK0 (h J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2)) =
      alternatingTerm P M U h hU hfl (leviIndex J I)

/-- Post-composing a signed sum of endomorphisms. -/
theorem comp_sum_zsmul {A : Type*} [AddCommGroup A] {α : Type*} (s : Finset α)
    (f : A →ₗ[ℤ] A) (c : α → ℤ) (g : α → A →ₗ[ℤ] A) :
    f.comp (∑ a ∈ s, c a • g a) = ∑ a ∈ s, c a • f.comp (g a) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]

/-- Each term of `D_G ∘ D_G`: by induction compatibility and term
transitivity, `D_G ∘ i_J ∘ r_J = ∑_{I ⊆ J} (-1)^{|I|} i_I ∘ r_I`. -/
theorem alternatingOperator_comp_alternatingTerm
    (hcompat : InductionCompatibilityStatement P M U h hU hfl hM hLevi hLeviFl)
    (htrans : TermTransitivityStatement P M U h hU hfl hM hLevi hLeviFl) (J : Finset ι) :
    (alternatingOperator P M U h hU hfl).comp (alternatingTerm P M U h hU hfl J) =
      ∑ I : Finset J, ((-1 : ℤ) ^ I.card) • alternatingTerm P M U h hU hfl (leviIndex J I) := by
  rw [alternatingTerm, ← LinearMap.comp_assoc, hcompat J, LinearMap.comp_assoc]
  simp only [leviAlternatingOperator, alternatingOperator]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  exact LinearMap.congr_fun (htrans J I) x

/-- Aubert's Theorem 1.7(3) for the family, from the three inputs of his
proof: induction compatibility (Theorem 1.7(2)), two-sided term transitivity
and the top-term identity `i_ι ∘ r_ι = id`. -/
theorem involutivityStatement_of_inductionCompatibility
    (hcompat : InductionCompatibilityStatement P M U h hU hfl hM hLevi hLeviFl)
    (htrans : TermTransitivityStatement P M U h hU hfl hM hLevi hLeviFl)
    (htop : alternatingTerm P M U h hU hfl Finset.univ = LinearMap.id) :
    InvolutivityStatement P M U h hU hfl := by
  unfold InvolutivityStatement
  conv_lhs => arg 2; rw [alternatingOperator]
  rw [comp_sum_zsmul]
  simp_rw [alternatingOperator_comp_alternatingTerm P M U h hU hfl hM hLevi hLeviFl
    hcompat htrans]
  rw [sum_neg_one_pow_smul_sum_leviIndex, htop]

end Reduction

end Langlands.Aubert.General
