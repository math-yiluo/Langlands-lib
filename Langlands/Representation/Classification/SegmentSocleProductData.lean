import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.TrivialGroupQuotient
import Mathlib.Data.List.FinRange

/-! # Empty and reindexed actual segment-socle product data -/

noncomputable section

namespace Langlands

universe uG uF uV

namespace Classification

/-- An embedding of an irreducible representation in an irreducible ambient
representation is its strong socle: every irreducible embedding is onto. -/
theorem IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible
    {G : Type uG} [Group G]
    {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    (h : IsIrreducibleSubrepresentation ρ π) (hρ : Representation.IsIrreducible ρ) :
    IsIrreducibleSocle ρ π := by
  let := hρ
  obtain ⟨hπ, j, hj⟩ := h
  have hsurj : ∀ (W' : Type uV) [AddCommGroup W'] [Module ℂ W']
      (π' : Representation ℂ G W'), Representation.IsIrreducible π' →
      ∀ j' : π'.IntertwiningMap ρ, Function.Injective j' → Function.Surjective j' := by
    intro W' _ _ π' hπ' j' hj'
    let := hπ'
    let : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π'.asModule
    apply (Representation.IsIrreducible.surjective_or_eq_zero j').resolve_right
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : W')
    apply hw
    apply hj'
    rw [hz]
    rfl
  refine ⟨hπ, j, hj, ?_⟩
  intro W' _ _ π' hπ' j' hj'
  exact (LinearMap.range_eq_top.mpr (hsurj W' π' hπ' j' hj')).trans
    (LinearMap.range_eq_top.mpr (hsurj W π hπ j hj)).symm

/-- A scalar-line representation of a trivial group has every irreducible
representation as a strong socle. -/
theorem isIrreducibleSocle_of_subsingleton_linearEquiv
    {G : Type uG} [Group G] [Subsingleton G]
    {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (π : Representation ℂ G W)
    (hπ : Representation.IsIrreducible π) (e : V ≃ₗ[ℂ] ℂ) :
    IsIrreducibleSocle ρ π := by
  have hρ := isIrreducible_of_linearEquiv_complex ρ e
  let := hρ
  let := hπ
  let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨_, q, hq⟩ := isIrreducibleQuotient_of_subsingleton_linearEquiv ρ π hπ e
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨v, hv⟩ := hq w
    apply hw
    rw [← hv, hz]
    rfl
  have hqi := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  let f := q.ofBijective ⟨hqi, hq⟩
  exact IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible
    ⟨hπ, f.symm.toIntertwiningMap, f.symm.injective⟩ hρ

end Classification

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

/-- The rank-zero datum has no segment occurrences and no block representations. -/
def empty : SegmentProductDatum.{uV, uF} T 0 where
  length := 0
  segments := Fin.elim0
  degree_sum := by simp
  blocks := fun i => Fin.elim0 i

@[simp] theorem empty_length : (empty : SegmentProductDatum.{uV, uF} T 0).length = 0 := rfl

@[simp] theorem empty_multisegment :
    (empty : SegmentProductDatum.{uV, uF} T 0).multisegment = 0 := by
  simp [multisegment, empty]

theorem empty_isPrecedenceOrdered :
    (empty : SegmentProductDatum.{uV, uF} T 0).IsPrecedenceOrdered :=
  fun i => Fin.elim0 i

theorem empty_hasSegmentSocles :
    (empty : SegmentProductDatum.{uV, uF} T 0).HasSegmentSocles :=
  fun i => Fin.elim0 i

/-- Reindexing carries each supplied segment socle with its segment. -/
theorem HasSegmentSocles.permute {n : ℕ} {d : SegmentProductDatum.{uV, uF} T n}
    (h : d.HasSegmentSocles) (σ : Equiv.Perm (Fin d.length)) :
    (d.permute σ).HasSegmentSocles := fun i => h (σ i)

/-- Reindexing preserves the multiset of segment occurrences. -/
@[simp] theorem permute_multisegment {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (σ : Equiv.Perm (Fin d.length)) : (d.permute σ).multisegment = d.multisegment := by
  exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm d.segments)

end SegmentProductDatum

end PadicField.TopologicalData

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible representation of `GL₀` is the strong socle of the actual
empty normalized product. -/
theorem emptySegmentProduct_isZelevinskySocle
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hπ : letI := T.topology
      Representation.IsIrreducible π.representation) :
    (PadicField.TopologicalData.SegmentProductDatum.empty :
      T.SegmentProductDatum.{max uF uV, uF} 0).IsZelevinskySocle π := by
  let := T.topology
  let d : T.SegmentProductDatum.{max uF uV, uF} 0 := .empty
  refine ⟨PadicField.TopologicalData.SegmentProductDatum.empty_isPrecedenceOrdered,
    PadicField.TopologicalData.SegmentProductDatum.empty_hasSegmentSocles, ?_⟩
  exact isIrreducibleSocle_of_subsingleton_linearEquiv d.induced.representation
    π.representation hπ (rankZeroNormalizedProductLinearEquiv F T d.shape
      (fun i => (d.blocks i).representation))

/-- The zero-rank case of socle exhaustion uses exactly the empty multisegment. -/
theorem multisegmentSocleExhaustion_rankZero
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hπ : letI := T.topology
      Representation.IsIrreducible π.representation) :
    ∃ a : T.Multisegment.{max uF uV, uF}, a.degree = 0 ∧ a.IsZelevinskySocle π := by
  refine ⟨0, by simp [PadicField.TopologicalData.Multisegment.degree], ?_⟩
  exact ⟨.empty, PadicField.TopologicalData.SegmentProductDatum.empty_multisegment,
    emptySegmentProduct_isZelevinskySocle F T π hπ⟩

end Classification

end Langlands
