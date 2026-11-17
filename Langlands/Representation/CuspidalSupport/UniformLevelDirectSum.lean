import Langlands.Representation.CuspidalSupport.CenterActionSpan
import Langlands.Representation.Category.FiniteGenerationCoproducts
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.Order.Filter.CountablyGenerated

/-! # Direct-sum tools for uniform compact-open constituent detection -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Langlands.SmoothRep

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} [DecidableEq I]
  (A : I → SmoothRep.{0, uG, max uI uV} ℂ G)

/-- Centre admissibility is preserved by a direct sum whose fixed spaces
have only finitely many active summands at every compact-open level. -/
def LocallyFiniteCenterAdmissibleDirectSumStatement : Prop :=
  (∀ i, (A i).IsCenterAdmissible) →
  (∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    ∃ T : Finset I, ∀ i ∉ T, ∀ v : A i,
      v ∈ fixedVectors (A i).representation K.toSubgroup → v = 0) →
  (directSum A).IsCenterAdmissible

/-- A finite indexing type can be relabelled by `Fin n` in the explicit
centre-generation formula. -/
theorem center_generated_of_finiteIndex
    (X : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G)
    {J : Type*} [Fintype J] (s : J → X)
    (hs : ∀ j, ∀ g ∈ K, X.representation g (s j) = s j)
    (hgen : ∀ x : X, (∀ g ∈ K, X.representation g x = x) →
      ∃ z : J → CatCenter (SmoothRep.{0, uG, uV} ℂ G),
        x = ∑ j, hom ((z j).app X) (s j)) :
    ∃ (n : ℕ) (t : Fin n → X),
      (∀ j, ∀ g ∈ K, X.representation g (t j) = t j) ∧
      ∀ x : X, (∀ g ∈ K, X.representation g x = x) →
        ∃ z : Fin n → CatCenter (SmoothRep.{0, uG, uV} ℂ G),
          x = ∑ j, hom ((z j).app X) (t j) := by
  classical
  let e := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, s ∘ e, fun j => hs (e j), ?_⟩
  intro x hx
  obtain ⟨z, hz⟩ := hgen x hx
  refine ⟨z ∘ e, ?_⟩
  exact hz.trans (e.sum_comp (fun j => hom ((z j).app X) (s j))).symm

/-- A vector with no coordinates outside a finite set is the corresponding
finite sum of its actual component inclusions. -/
theorem directSum_eq_sum_of_zero_off (T : Finset I) (x : directSum A)
    (hx : ∀ i ∉ T, hom (directSumπ A i) x = 0) :
    x = ∑ i : T, hom (directSumι A i.val) (hom (directSumπ A i.val) x) := by
  classical
  have hs : x.support ⊆ T := by
    intro i hi
    by_contra hn
    exact (DFinsupp.mem_support_iff.mp hi) (hx i hn)
  calc
    x = ∑ i ∈ x.support,
        hom (directSumι A i) (hom (directSumπ A i) x) :=
      (DirectSum.sum_support_of x).symm
    _ = ∑ i ∈ T,
        hom (directSumι A i) (hom (directSumπ A i) x) := by
      apply Finset.sum_subset hs
      intro i hi hni
      have hi0 : hom (directSumπ A i) x = 0 :=
        DFinsupp.notMem_support_iff.mp hni
      rw [hi0, map_zero]
    _ = ∑ i : T, hom (directSumι A i.val) (hom (directSumπ A i.val) x) := by
      exact (Finset.sum_coe_sort T
        (fun i => hom (directSumι A i) (hom (directSumπ A i) x))).symm

/-- The locally finite direct-sum centre-admissibility theorem, proved by
assembling finitely many component generator families and using naturality. -/
theorem locallyFiniteCenterAdmissibleDirectSum :
    LocallyFiniteCenterAdmissibleDirectSumStatement A := by
  classical
  intro hA hlocal K hK
  obtain ⟨T, hT⟩ := hlocal K hK
  choose n s hs hgen using fun i : T => hA i.val K hK
  let J := Σ i : T, Fin (n i)
  let t : J → directSum A :=
    fun j => hom (directSumι A j.1.val) (s j.1 j.2)
  apply center_generated_of_finiteIndex (directSum A) K t
  · intro j g hg
    exact ((hom (directSumι A j.1.val)).isIntertwining _ _ g (s j.1 j.2)).symm.trans
      (congrArg (hom (directSumι A j.1.val)) (hs j.1 j.2 g hg))
  · intro x hx
    have hxi (i : I) : ∀ g ∈ K,
        (A i).representation g (hom (directSumπ A i) x) =
          hom (directSumπ A i) x := by
      intro g hg
      exact ((hom (directSumπ A i)).isIntertwining _ _ g x).symm.trans
        (congrArg (hom (directSumπ A i)) (hx g hg))
    choose z hz using fun i : T => hgen i (hom (directSumπ A i.val) x) (hxi i.val)
    refine ⟨fun j => z j.1 j.2, ?_⟩
    calc
      x = ∑ i : T, hom (directSumι A i.val) (hom (directSumπ A i.val) x) :=
        directSum_eq_sum_of_zero_off A T x
          (fun i hi => hT i hi _ (fun g => hxi i g g.property))
      _ = ∑ i : T, ∑ j : Fin (n i),
          hom (directSumι A i.val) (hom ((z i j).app (A i.val)) (s i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hz i, map_sum]
      _ = ∑ j : J, hom ((z j.1 j.2).app (directSum A)) (t j) := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (congrArg
          (fun f : A i.val ⟶ directSum A => hom f (s i j))
          ((z i j).naturality (directSumι A i.val))).symm

/-- An actual direct sum of infinitely many nonzero smooth representations
cannot be finitely generated over the group algebra. -/
theorem not_finite_directSum_of_infinite [Infinite I] (hA : ∀ i, Nontrivial (A i)) :
    ¬ Module.Finite (MonoidAlgebra ℂ G) (directSum A).representation.asModule := by
  intro hfin
  let := hfin
  obtain ⟨T, hT⟩ := finite_support_hom_directSum A (directSum A) (𝟙 _)
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset T
  have hp : directSumπ A i = 0 := by simpa using hT i hi
  have hid : 𝟙 (A i) = 0 := by
    rw [← directSumι_comp_π_self A i, hp, comp_zero]
  let := hA i
  obtain ⟨v, hv⟩ := exists_ne (0 : A i)
  exact hv (congrArg (fun f : A i ⟶ A i => hom f v) hid)

end Langlands.SmoothRep

namespace Langlands

universe uG

open Filter

/-- A first-countable locally compact nonarchimedean group has a decreasing
sequence of compact open subgroups cofinal in the identity neighbourhoods. -/
theorem exists_antitone_compactOpen_basis
    (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] [FirstCountableTopology G] :
    ∃ K : ℕ → OpenSubgroup G, (∀ n, IsCompact (K n : Set G)) ∧
      Antitone K ∧ ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U := by
  have hb : (𝓝 (1 : G)).HasBasis
      (fun K : OpenSubgroup G => IsCompact (K : Set G)) (fun K => (K : Set G)) := by
    constructor
    intro U
    exact ⟨compactOpenSubgroupBasis G U,
      fun ⟨K, _, hKU⟩ => mem_of_superset K.mem_nhds_one hKU⟩
  obtain ⟨K, hK, hbase⟩ := hb.exists_antitone_subbasis
  refine ⟨K, hK, hbase.antitone, ?_⟩
  intro U hU
  obtain ⟨n, _, hn⟩ := hbase.toHasBasis.mem_iff.mp hU
  exact ⟨n, hn⟩

end Langlands
