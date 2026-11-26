import Langlands.Global.ArthurSiegelPartitionPoints
import Langlands.LinearAlgebra.ArthurCombinatoricsPartition

/-! # Arthur's partition lemma from the reduction-theoretic lemma

Arthur 1978, Lemma 6.4 and its proof (pp.941–942); Arthur 2005, Lemma 8.2 and (8.1). -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}

section SiegelSets

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
include hG hν in
/-- `H_0(n m a k) = H_0(a)` for `n ∈ N_0(𝔸)`, `m ∈ M_0(𝔸)^1`, `a ∈ A_0` and `k ∈ K`. -/
theorem height_siegel_product (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
    (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
    (a : PositiveRealTorus.intrinsicSubgroup F T) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    height hi hK hρ (map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m * positiveTorusMap F i a * k) =
      height hi hK hρ (positiveTorusMap F i a) := by
  unfold height
  congr 1
  have hU := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
    (Set.empty_subset _)
  rw [hK.height_mul_right _ hk, mul_assoc, ← Standard.unipotentToParabolic_comp,
    map_comp_apply_of_hom, hK.height_map_mul, characterLog_map,
    characterLog_eq_zero_of_isUnipotent hU, map_zero, zero_add,
    ← Standard.leviToParabolic_comp, map_comp_apply_of_hom, hK.height_map_mul,
    characterLog_map, (characterLog_eq_zero_iff F _ _).mpr m.2, map_zero, zero_add]

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- `S^P(T_1, ω) ⊆ S^{P_1}(T_1, ω)` for `Δ_0^{P_1} ⊆ Δ_0^P`. -/
theorem siegelSet_mono
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    {S SP : Finset (characterLattice T)} (h : S ⊆ SP) (T₁ : V T) :
    siegelSet hi hK hρ C SP T₁ ⊆ siegelSet hi hK hρ C S T₁ := by
  intro x hx
  rw [mem_siegelSet_iff] at hx ⊢
  obtain ⟨n, hn, m, hm, a, ha, k, hk, hx⟩ := hx
  exact ⟨n, hn, m, hm, a, fun β hβ => ha β (h hβ), k, hk, hx⟩

include hG hν in
/-- The height of a point of a Siegel set is the height of its torus factor. -/
theorem exists_height_eq_of_mem_siegelSet
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (hC : C.compactSubgroup = K) {S : Finset (characterLattice T)} {T₁ : V T}
    {x : AdelicGroupPoints F G} (hx : x ∈ siegelSet hi hK hρ C S T₁) :
    ∃ n ∈ C.omegaN, ∃ m ∈ C.omegaM, ∃ a : PositiveRealTorus.intrinsicSubgroup F T,
      (∀ β ∈ S, 0 < eval T β (height hi hK hρ (positiveTorusMap F i a) - T₁)) ∧
      ∃ k ∈ C.compactSubgroup,
        map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
            positiveTorusMap F i a * k = x ∧
        height hi hK hρ x = height hi hK hρ (positiveTorusMap F i a) := by
  rw [mem_siegelSet_iff] at hx
  obtain ⟨n, hn, m, hm, a, ha, k, hk, rfl⟩ := hx
  exact ⟨n, hn, m, hm, a, ha, k, hk, rfl,
    height_siegel_product hG hi hν hK hρ n m a (hC ▸ hk)⟩

include hG hν in
/-- A point of `S^{P_1}(T_1, ω)` with `α(H_0(x) − T_1) > 0` for every `α ∈ Δ_0^P ∖ Δ_0^{P_1}`
lies in `S^P(T_1, ω)`. -/
theorem mem_siegelSet_of_mem_of_pos
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (hC : C.compactSubgroup = K) {S SP : Finset (characterLattice T)} {T₁ : V T}
    {x : AdelicGroupPoints F G} (hx : x ∈ siegelSet hi hK hρ C S T₁)
    (hpos : ∀ α ∈ SP, α ∉ S → 0 < eval T α (height hi hK hρ x - T₁)) :
    x ∈ siegelSet hi hK hρ C SP T₁ := by
  obtain ⟨n, hn, m, hm, a, ha, k, hk, hx, hheight⟩ :=
    exists_height_eq_of_mem_siegelSet hG hi hν hK hρ C hC hx
  rw [mem_siegelSet_iff]
  refine ⟨n, hn, m, hm, a, fun β hβ => ?_, k, hk, hx⟩
  by_cases hβS : β ∈ S
  · exact ha β hβS
  · have := hpos β hβ hβS
    rwa [hheight] at this

end SiegelSets

section Translation

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Arthur's weight `ϖ^P_β` as the abstract weight coordinate of `standardIndex`. -/
theorem weight_eq_weightCoordinate (S : Set (characterLattice T)) {β : characterLattice T}
    (hβ : β ∈ simpleRelativeRoots i ν) (H : V T) :
    ArthurRelative.weight hG hi ν D S β H =
      ArthurCombinatorics.weightCoordinate (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν S)
        ⟨β, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν hβ⟩
        (ArthurRelative.toCorootSpan hG hi D H) := by
  rw [ArthurRelative.weight_of_mem hG hi ν D S
    (ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν hβ)]
  rfl

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- A simple root on `𝔞_0` is the abstract root on the `𝔞_0^G`-component. -/
theorem eval_eq_root' {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) (H : V T) :
    eval T α H = (ArthurRelative.rootPairing hG hi D).root'
      ⟨α, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν hα⟩
      (ArthurRelative.toCorootSpan hG hi D H) := by
  have h := ArthurRelative.eval_sub_toCorootSpan hG hi D
    (simpleRelativeRoots_subset_relativeRoots i ν hα) H
  rw [map_sub, sub_eq_zero] at h
  rw [h, eval_eq_pair]
  rfl

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- `𝔞_0^P ⊆ 𝔞_0` maps into the abstract coroot span of `standardIndex`. -/
theorem toCorootSpan_mem_corootSpan {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) {v : V T}
    (hv : v ∈ Submodule.span ℝ (D.realCorootsOf S)) :
    ArthurRelative.toCorootSpan hG hi D v ∈
      ArthurCombinatorics.corootSpan (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν S) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    let β : RelativeRoot.indivisibleRoots i :=
      ⟨α.1, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hS hα)⟩
    have hβ : D.realCoroot α = ((ArthurRelative.rootPairing hG hi D).coroot β : V T) := by
      rw [ArthurRelative.rootPairing_coroot]
    rw [hβ, ArthurRelative.toCorootSpan_apply_coe]
    exact Submodule.subset_span ⟨β, (ArthurRelative.mem_standardIndex hG hi ν).mpr
      ⟨hS hα, hα⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
theorem coe_simpleFinset : ((simpleFinset ν hG hi : Finset (characterLattice T)) :
    Set (characterLattice T)) = simpleRelativeRoots i ν := by
  ext α
  simp

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
theorem subset_simple_of_subset {SP : Finset (characterLattice T)}
    (hSP : SP ⊆ simpleFinset ν hG hi) :
    (SP : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := by
  intro α hα
  exact (mem_simpleFinset hG hi).mp (hSP hα)

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The nonpositivity of Arthur's weights of `S` as nonpositivity of abstract weights. -/
theorem weightCoordinate_nonpos_of_weight_nonpos {S : Finset (characterLattice T)}
    (_hS : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν) {H : V T}
    (hw : ∀ β ∈ S, ArthurRelative.weight hG hi ν D (S : Set (characterLattice T)) β H ≤ 0) :
    ∀ j ∈ ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)),
      ArthurCombinatorics.weightCoordinate (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T))) j
        (ArthurRelative.toCorootSpan hG hi D H) ≤ 0 := by
  intro j hj
  have hjS := (ArthurRelative.mem_standardIndex hG hi ν).mp hj
  have h := hw j.1 (Finset.mem_coe.mp hjS.2)
  rw [weight_eq_weightCoordinate hG hi D _ hjS.1] at h
  exact h

end Translation

section Core

variable (hcomp : ParabolicSpacesComparisonStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
  (hC : C.compactSubgroup = K) (T₁ Tp : V T)

include hν in
/-- **Existence** (Arthur 1978, proof of Lemma 6.4, "at least one"): a point of `S^P(T_1, ω)`
has `F^{P_1}(y, T) τ_{P_1}^P(H_0(y) − T) = 1` for some `P_0 ⊆ P_1 ⊆ P`. -/
theorem exists_partition_term {SP : Finset (characterLattice T)}
    (hSP : SP ⊆ simpleFinset ν hG hi) {y : AdelicGroupPoints F G}
    (hy : y ∈ siegelSet hi hK hρ C SP T₁) :
    ∃ S ∈ SP.powerset, siegelIndicator hG hi D hK hρ C S T₁ Tp y = 1 ∧
      ArthurRelative.tau hG hi ν D (S : Set (characterLattice T)) (SP : Set (characterLattice T))
        (height hi hK hρ y - Tp) = 1 := by
  have := ArthurRelative.finite_indivisibleRoots hG hi
  set b := ArthurRelative.base hG hi hν D
  have hSPs := subset_simple_of_subset hG hi hSP
  have hΘP : ArthurRelative.standardIndex hG hi ν (SP : Set (characterLattice T)) ⊆ b.support :=
    ArthurRelative.standardIndex_subset_support hG hi D hν _
  obtain ⟨Θ, ⟨⟨-, hΘ⟩, hw, ht⟩, -⟩ := ArthurCombinatorics.existsUnique_weight_nonpos_tau b
    (Finset.empty_subset _) hΘP (ArthurRelative.toCorootSpan hG hi D (height hi hK hρ y - Tp))
  have hΘs : ∀ α ∈ Θ, (α : characterLattice T) ∈ simpleRelativeRoots i ν := fun α hα =>
    ((ArthurRelative.mem_standardIndex hG hi ν).mp (hΘ hα)).1
  set S : Finset (characterLattice T) := Θ.image Subtype.val with hSdef
  have hScoe : (S : Set (characterLattice T)) =
      (↑) '' (Θ : Set (RelativeRoot.indivisibleRoots i)) := by
    rw [hSdef, Finset.coe_image]
  have hSΘ : ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)) = Θ := by
    rw [hScoe]
    exact ArthurRelative.standardIndex_image hG hi ν Θ hΘs
  have hSSP : S ⊆ SP := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβ
    exact ((ArthurRelative.mem_standardIndex hG hi ν).mp (hΘ hα)).2
  refine ⟨S, Finset.mem_powerset.mpr hSSP, ?_, ?_⟩
  · unfold siegelIndicator
    split_ifs with hcond
    · rfl
    exfalso
    apply hcond
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul]
    refine ⟨siegelSet_mono hi hK hρ C hSSP T₁ hy, fun β hβ => ?_⟩
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβ
    rw [weight_eq_weightCoordinate hG hi D _ (hΘs α hα), hSΘ]
    exact hw α (Finset.mem_sdiff.mpr ⟨hα, Finset.notMem_empty _⟩)
  · change ArthurCombinatorics.tau (ArthurRelative.rootPairing hG hi D)
      (ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)))
      (ArthurRelative.standardIndex hG hi ν (SP : Set (characterLattice T)))
      (ArthurRelative.toCorootSpan hG hi D (height hi hK hρ y - Tp)) = 1
    rw [hSΘ]
    exact ht

include hcomp hν hC in
/-- **Normal form of a contributing term.** If `F^{P_1}(y, T) τ_{P_1}^P(H_0(y) − T) = 1`, a left
`P_1(F)`-translate `ry` lies in the truncated Siegel set, in `S^P(T_1, ω)`, has the same value of
`τ_{P_1}^P` and satisfies `α(H_0(ry) − T) > 0` for every `α ∈ Δ_0^P ∖ Δ_0^{P_1}`. -/
theorem exists_translate_of_partition_term {S SP : Finset (characterLattice T)} (hS : S ⊆ SP)
    (hSP : SP ⊆ simpleFinset ν hG hi)
    (hTT : ∀ β ∈ simpleRelativeRoots i ν, eval T β T₁ < eval T β Tp)
    {y : AdelicGroupPoints F G}
    (hind : siegelIndicator hG hi D hK hρ C S T₁ Tp y = 1)
    (ht : ArthurRelative.tau hG hi ν D (S : Set (characterLattice T))
      (SP : Set (characterLattice T)) (height hi hK hρ y - Tp) = 1) :
    ∃ r ∈ parabolicRationalImage (Standard.parabolicHom i ν (S : Set (characterLattice T))),
      r * y ∈ siegelSet hi hK hρ C SP T₁ ∧
      (∀ β ∈ S, ArthurRelative.weight hG hi ν D (S : Set (characterLattice T)) β
        (height hi hK hρ (r * y) - Tp) ≤ 0) ∧
      ArthurRelative.tau hG hi ν D (S : Set (characterLattice T))
        (SP : Set (characterLattice T)) (height hi hK hρ (r * y) - Tp) = 1 ∧
      ∀ α ∈ SP, α ∉ S → 0 < eval T α (height hi hK hρ (r * y) - Tp) := by
  have := ArthurRelative.finite_indivisibleRoots hG hi
  set b := ArthurRelative.base hG hi hν D
  have hSPs := subset_simple_of_subset hG hi hSP
  have hSs : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun α hα => hSPs (hS hα)
  have hΘP := ArthurRelative.standardIndex_subset_support hG hi D hν
    (SP : Set (characterLattice T))
  have hΘS := ArthurRelative.standardIndex_subset_support hG hi D hν
    (S : Set (characterLattice T))
  have hΘSP : ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)) ⊆
      ArthurRelative.standardIndex hG hi ν (SP : Set (characterLattice T)) :=
    ArthurRelative.standardIndex_mono hG hi ν (Finset.coe_subset.mpr hS)
  unfold siegelIndicator at hind
  split_ifs at hind with hex
  · obtain ⟨r, hr, hsieg, hw⟩ := hex
    have hdiff := height_sub_mem_span hcomp hG hi hν D hK hρ hSs hr y
    have htau' : ArthurRelative.tau hG hi ν D (S : Set (characterLattice T))
        (SP : Set (characterLattice T)) (height hi hK hρ (r * y) - Tp) = 1 := by
      have heq : height hi hK hρ (r * y) - Tp =
          (height hi hK hρ y - Tp) + (height hi hK hρ (r * y) - height hi hK hρ y) := by abel
      change ArthurCombinatorics.tau (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)))
        (ArthurRelative.standardIndex hG hi ν (SP : Set (characterLattice T)))
        (ArthurRelative.toCorootSpan hG hi D (height hi hK hρ (r * y) - Tp)) = 1
      rw [heq, map_add, ArthurCombinatorics.tau_add_of_mem_corootSpan b hΘS _ _
        (toCorootSpan_mem_corootSpan hG hi D hSs hdiff)]
      exact ht
    have hw' := weightCoordinate_nonpos_of_weight_nonpos hG hi D hSs hw
    have hpos : ∀ α ∈ SP, α ∉ S → 0 < eval T α (height hi hK hρ (r * y) - Tp) := by
      intro α hα hαS
      have hαs := hSPs hα
      rw [eval_eq_root' hG hi D hαs]
      exact ArthurCombinatorics.root'_pos_of_weight_nonpos_of_tau b hΘSP hΘP hw' htau'
        ((ArthurRelative.mem_standardIndex hG hi ν).mpr ⟨hαs, hα⟩)
        (fun h => hαS ((ArthurRelative.mem_standardIndex hG hi ν).mp h).2)
    refine ⟨r, hr, mem_siegelSet_of_mem_of_pos hG hi hν hK hρ C hC hsieg
      (fun α hα hαS => ?_), hw, htau', hpos⟩
    have h1 := hpos α hα hαS
    have h2 := hTT α (hSPs hα)
    rw [map_sub] at h1 ⊢
    linarith
  · exact absurd hind (by norm_num)

include hcomp hν hC in
/-- **Uniqueness** (Arthur 1978, proof of Lemma 6.4, "at most one"). If
`F^{P_a}(δ_a x, T) τ_{P_a}^P(H_0(δ_a x) − T) = 1` for `δ_a ∈ P(F)`, `a = 1, 2`, then `P_1 = P_2`
and `δ_2 δ_1⁻¹ ∈ P_1(F)`. -/
theorem partition_term_unique {SP S₁ S₂ : Finset (characterLattice T)}
    (hSP : SP ⊆ simpleFinset ν hG hi) (h1 : S₁ ⊆ SP) (h2 : S₂ ⊆ SP)
    (hTT : ∀ β ∈ simpleRelativeRoots i ν, eval T β T₁ < eval T β Tp)
    (hred : ∀ S ∈ SP.powerset, ∀ x δ : AdelicGroupPoints F G,
      δ ∈ parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))) →
      x ∈ siegelSet hi hK hρ C SP T₁ → δ * x ∈ siegelSet hi hK hρ C SP T₁ →
      (∀ α ∈ SP, α ∉ S → 0 < eval T α (height hi hK hρ x - Tp)) →
      δ ∈ parabolicRationalImage (Standard.parabolicHom i ν (S : Set (characterLattice T))))
    {x δ₁ δ₂ : AdelicGroupPoints F G}
    (hδ₁ : δ₁ ∈ parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))))
    (hδ₂ : δ₂ ∈ parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))))
    (hind₁ : siegelIndicator hG hi D hK hρ C S₁ T₁ Tp (δ₁ * x) = 1)
    (ht₁ : ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
      (SP : Set (characterLattice T)) (height hi hK hρ (δ₁ * x) - Tp) = 1)
    (hind₂ : siegelIndicator hG hi D hK hρ C S₂ T₁ Tp (δ₂ * x) = 1)
    (ht₂ : ArthurRelative.tau hG hi ν D (S₂ : Set (characterLattice T))
      (SP : Set (characterLattice T)) (height hi hK hρ (δ₂ * x) - Tp) = 1) :
    S₁ = S₂ ∧
      δ₂ * δ₁⁻¹ ∈ parabolicRationalImage (Standard.parabolicHom i ν (S₁ : Set (characterLattice T))) := by
  have := ArthurRelative.finite_indivisibleRoots hG hi
  obtain ⟨r₁, hr₁, hy₁, hw₁, ht₁', hpos₁⟩ := exists_translate_of_partition_term hcomp hG hi hν D
    hK hρ C hC T₁ Tp h1 hSP hTT hind₁ ht₁
  obtain ⟨r₂, hr₂, hy₂, hw₂, ht₂', hpos₂⟩ := exists_translate_of_partition_term hcomp hG hi hν D
    hK hρ C hC T₁ Tp h2 hSP hTT hind₂ ht₂
  have hSPs := subset_simple_of_subset hG hi hSP
  have hS1s : (S₁ : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun α hα => hSPs (h1 hα)
  have hS2s : (S₂ : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun α hα => hSPs (h2 hα)
  have hP1 := parabolicRationalImage_mono hG hi hν (Finset.coe_subset.mpr h1) hSPs
  have hP2 := parabolicRationalImage_mono hG hi hν (Finset.coe_subset.mpr h2) hSPs
  set y₁ := r₁ * (δ₁ * x) with hy₁def
  set y₂ := r₂ * (δ₂ * x) with hy₂def
  set δ := (r₂ * δ₂) * (r₁ * δ₁)⁻¹ with hδdef
  have hδ : δ ∈ parabolicRationalImage
      (Standard.parabolicHom i ν (SP : Set (characterLattice T))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hP2 hr₂) hδ₂)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hP1 hr₁) hδ₁))
  have hδy : δ * y₁ = y₂ := by
    rw [hδdef, hy₁def, hy₂def]
    group
  have hδy' : δ⁻¹ * y₂ = y₁ := by
    rw [← hδy]
    group
  have hδ1 := hred S₁ (Finset.mem_powerset.mpr h1) y₁ δ hδ hy₁ (hδy ▸ hy₂) hpos₁
  have hδ2' := hred S₂ (Finset.mem_powerset.mpr h2) y₂ δ⁻¹ (Subgroup.inv_mem _ hδ) hy₂
    (hδy' ▸ hy₁) hpos₂
  have hδ2 : δ ∈ parabolicRationalImage
      (Standard.parabolicHom i ν (S₂ : Set (characterLattice T))) := by
    simpa using Subgroup.inv_mem _ hδ2'
  have hd1 := height_sub_mem_span hcomp hG hi hν D hK hρ hS1s hδ1 y₁
  have hd2 := height_sub_mem_span hcomp hG hi hν D hK hρ hS2s hδ2 y₁
  rw [hδy] at hd1 hd2
  set b := ArthurRelative.base hG hi hν D
  have hΘP := ArthurRelative.standardIndex_subset_support hG hi D hν
    (SP : Set (characterLattice T))
  have hΘ1 := ArthurRelative.standardIndex_subset_support hG hi D hν
    (S₁ : Set (characterLattice T))
  have hΘ2 := ArthurRelative.standardIndex_subset_support hG hi D hν
    (S₂ : Set (characterLattice T))
  have hZ : ArthurRelative.toCorootSpan hG hi D (height hi hK hρ y₂ - Tp) -
      ArthurRelative.toCorootSpan hG hi D (height hi hK hρ y₁ - Tp) ∈
      ArthurCombinatorics.corootSpan (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν (S₁ : Set (characterLattice T)) ∩
          ArthurRelative.standardIndex hG hi ν (S₂ : Set (characterLattice T))) := by
    rw [← map_sub, show (height hi hK hρ y₂ - Tp) - (height hi hK hρ y₁ - Tp) =
      height hi hK hρ y₂ - height hi hK hρ y₁ by abel]
    exact ArthurCombinatorics.mem_corootSpan_inter b hΘ1 hΘ2
      (toCorootSpan_mem_corootSpan hG hi D hS1s hd1)
      (toCorootSpan_mem_corootSpan hG hi D hS2s hd2)
  have hΘ := ArthurCombinatorics.eq_of_weight_nonpos_of_tau b
    (ArthurRelative.standardIndex_mono hG hi ν (Finset.coe_subset.mpr h1))
    (ArthurRelative.standardIndex_mono hG hi ν (Finset.coe_subset.mpr h2)) hΘP hZ
    (weightCoordinate_nonpos_of_weight_nonpos hG hi D hS1s hw₁) ht₁'
    (weightCoordinate_nonpos_of_weight_nonpos hG hi D hS2s hw₂) ht₂'
  have hS : S₁ = S₂ :=
    Finset.coe_injective (ArthurRelative.standardIndex_injOn hG hi ν hS1s hS2s hΘ)
  subst hS
  refine ⟨rfl, ?_⟩
  have heq : δ₂ * δ₁⁻¹ = r₂⁻¹ * δ * r₁ := by
    rw [hδdef]
    group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hr₂) hδ1) hr₁

end Core

section Terms

variable (hcomp : ParabolicSpacesComparisonStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
  (T₁ Tp : V T)

theorem siegelIndicator_eq_zero_or_one (S : Finset (characterLattice T))
    (y : AdelicGroupPoints F G) :
    siegelIndicator hG hi D hK hρ C S T₁ Tp y = 0 ∨
      siegelIndicator hG hi D hK hρ C S T₁ Tp y = 1 := by
  unfold siegelIndicator
  split_ifs <;> simp

theorem tau_eq_zero_or_one (S SP : Set (characterLattice T)) (H : V T) :
    ArthurRelative.tau hG hi ν D S SP H = 0 ∨ ArthurRelative.tau hG hi ν D S SP H = 1 := by
  unfold ArthurRelative.tau ArthurCombinatorics.tau
  split_ifs <;> simp

/-- A nonzero term `F^P(y, T) τ(H)` has both factors equal to `1`. -/
theorem eq_one_of_mul_ne_zero {S : Finset (characterLattice T)} {SP : Set (characterLattice T)}
    {y : AdelicGroupPoints F G} {H : V T}
    (h : siegelIndicator hG hi D hK hρ C S T₁ Tp y * ArthurRelative.tau hG hi ν D
      (S : Set (characterLattice T)) SP H ≠ 0) :
    siegelIndicator hG hi D hK hρ C S T₁ Tp y = 1 ∧
      ArthurRelative.tau hG hi ν D (S : Set (characterLattice T)) SP H = 1 := by
  rcases siegelIndicator_eq_zero_or_one hG hi D hK hρ C T₁ Tp S y with h1 | h1 <;>
    rcases tau_eq_zero_or_one (ν := ν) hG hi D (S : Set (characterLattice T)) SP H with h2 | h2 <;>
    simp_all

/-- `F^P(·, T)` is left `P(F)`-invariant. -/
theorem siegelIndicator_mul_left (S : Finset (characterLattice T)) {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν (S : Set (characterLattice T))))
    (y : AdelicGroupPoints F G) :
    siegelIndicator hG hi D hK hρ C S T₁ Tp (r * y) =
      siegelIndicator hG hi D hK hρ C S T₁ Tp y := by
  unfold siegelIndicator
  congr 1
  apply propext
  constructor
  · rintro ⟨δ, hδ, hmem⟩
    exact ⟨δ * r, Subgroup.mul_mem _ hδ hr, by rwa [mul_assoc]⟩
  · rintro ⟨δ, hδ, hmem⟩
    exact ⟨δ * r⁻¹, Subgroup.mul_mem _ hδ (Subgroup.inv_mem _ hr), by
      rwa [mul_assoc, inv_mul_cancel_left]⟩

include hcomp hν in
/-- `τ_{P_1}^P(H_0(·) − T)` is left `P_1(F)`-invariant. -/
theorem tau_height_mul_left {S : Finset (characterLattice T)} (SP : Set (characterLattice T))
    (hS : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν) {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν (S : Set (characterLattice T))))
    (y : AdelicGroupPoints F G) :
    ArthurRelative.tau hG hi ν D (S : Set (characterLattice T)) SP
        (height hi hK hρ (r * y) - Tp) =
      ArthurRelative.tau hG hi ν D (S : Set (characterLattice T)) SP
        (height hi hK hρ y - Tp) := by
  have := ArthurRelative.finite_indivisibleRoots hG hi
  have hdiff := height_sub_mem_span hcomp hG hi hν D hK hρ hS hr y
  have heq : height hi hK hρ (r * y) - Tp =
      (height hi hK hρ y - Tp) + (height hi hK hρ (r * y) - height hi hK hρ y) := by abel
  change ArthurCombinatorics.tau (ArthurRelative.rootPairing hG hi D)
      (ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)))
      (ArthurRelative.standardIndex hG hi ν SP)
      (ArthurRelative.toCorootSpan hG hi D (height hi hK hρ (r * y) - Tp)) =
    ArthurCombinatorics.tau (ArthurRelative.rootPairing hG hi D)
      (ArthurRelative.standardIndex hG hi ν (S : Set (characterLattice T)))
      (ArthurRelative.standardIndex hG hi ν SP)
      (ArthurRelative.toCorootSpan hG hi D (height hi hK hρ y - Tp))
  rw [heq, map_add, ArthurCombinatorics.tau_add_of_mem_corootSpan
    (ArthurRelative.base hG hi hν D)
    (ArthurRelative.standardIndex_subset_support hG hi D hν _) _ _
    (toCorootSpan_mem_corootSpan hG hi D hS hdiff)]

theorem coe_mem_parabolicRationalImage {J : Set (characterLattice T)}
    (z : parabolicRationalSubgroup F (Standard.parabolicHom i ν J)) :
    ((z : rationalSubgroup F G) : AdelicGroupPoints F G) ∈
      parabolicRationalImage (Standard.parabolicHom i ν J) :=
  ⟨z, z.2, rfl⟩

theorem mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage {J : Set (characterLattice T)}
    (z : rationalSubgroup F G) :
    z ∈ parabolicRationalSubgroup F (Standard.parabolicHom i ν J) ↔
      (z : AdelicGroupPoints F G) ∈ parabolicRationalImage (Standard.parabolicHom i ν J) := by
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    rwa [Subtype.ext hwz] at hw

end Terms

section Predicates

variable (hcomp : ParabolicSpacesComparisonStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

/-- A regularity bound for `T` above `c` and above every `β(T_1)`. -/
theorem regular_of_lt (T₁ : V T) (c : ℝ) {Tp : V T}
    (hTp : ∀ β ∈ simpleRelativeRoots i ν,
      |c| + ∑ β' ∈ simpleFinset ν hG hi, |eval T β' T₁| < eval T β Tp) :
    (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) ∧
      ∀ β ∈ simpleRelativeRoots i ν, eval T β T₁ < eval T β Tp := by
  have hsum : 0 ≤ ∑ β' ∈ simpleFinset ν hG hi, |eval T β' T₁| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · have := hTp β hβ
    linarith [le_abs_self c]
  · have h1 : |eval T β T₁| ≤ ∑ β' ∈ simpleFinset ν hG hi, |eval T β' T₁| :=
      Finset.single_le_sum (f := fun β' => |eval T β' T₁|) (fun _ _ => abs_nonneg _)
        ((mem_simpleFinset hG hi).mpr hβ)
    have := hTp β hβ
    linarith [le_abs_self (eval T β T₁), abs_nonneg c]

include hcomp hν in
/-- **Arthur 1978, Lemma 6.4; Arthur 2005, (8.1)**, for one compact subgroup, from the
reduction-theoretic lemma. -/
theorem isRelativeSiegelPartition_of_reduction (hred : IsSiegelReductionLemma hG hi hK hρ) :
    IsRelativeSiegelPartition hG hi D hK hρ := by
  intro C T₁ hC hcov
  obtain ⟨c₀, hc₀⟩ := hred C T₁ hC
  refine ⟨|c₀| + ∑ β ∈ simpleFinset ν hG hi, |eval T β T₁|, fun Tp hTp SP hSP x => ?_⟩
  obtain ⟨hreg, hTT⟩ := regular_of_lt hG hi T₁ c₀ hTp
  have hSPsub : SP ⊆ simpleFinset ν hG hi := Finset.mem_powerset.mp hSP
  have hSPs := subset_simple_of_subset hG hi hSPsub
  have hredSP := hc₀ Tp hreg SP hSP
  -- the representatives lie in `P(F)`
  have hrep : ∀ {S₁ : Finset (characterLattice T)}
      (δ : RelativeCosets (F := F) (i := i) (ν := ν) (S₁ : Set (characterLattice T))
        (SP : Set (characterLattice T))),
      (((Quotient.out δ : parabolicRationalSubgroup F
        (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) : rationalSubgroup F G) :
          AdelicGroupPoints F G) ∈
        parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))) :=
    fun δ => coe_mem_parabolicRationalImage (Quotient.out δ)
  -- the terms
  let term : (S₁ : Finset (characterLattice T)) →
      RelativeCosets (F := F) (i := i) (ν := ν) (S₁ : Set (characterLattice T))
        (SP : Set (characterLattice T)) → ℤ := fun S₁ δ =>
    siegelIndicator hG hi D hK hρ C S₁ T₁ Tp
        ((((Quotient.out δ : parabolicRationalSubgroup F
          (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
            rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
      ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
        (SP : Set (characterLattice T))
        (height hi hK hρ ((((Quotient.out δ : parabolicRationalSubgroup F
          (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
            rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp)
  show (∀ S₁ ∈ SP.powerset, (Function.support (term S₁)).Finite) ∧
    ∑ S₁ ∈ SP.powerset, ∑' δ, term S₁ δ = 1
  -- two cosets with nonzero terms for the same `P_1` agree
  have hF1 : ∀ S₁ ∈ SP.powerset, ∀ δ δ', term S₁ δ ≠ 0 → term S₁ δ' ≠ 0 → δ = δ' := by
    intro S₁ hS₁ δ δ' h h'
    obtain ⟨hi₁, ht₁⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h
    obtain ⟨hi₂, ht₂⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h'
    obtain ⟨-, hmem⟩ := partition_term_unique hcomp hG hi hν D hK hρ C hC T₁ Tp hSPsub
      (Finset.mem_powerset.mp hS₁) (Finset.mem_powerset.mp hS₁) hTT
      (fun S hS x δ => hredSP S hS x δ) (hrep δ) (hrep δ') hi₁ ht₁ hi₂ ht₂
    rw [← Quotient.out_eq δ, ← Quotient.out_eq δ']
    apply Quotient.sound
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage]
    simpa using hmem
  -- a contributing pair from the covering
  have hx : x ∈ (parabolicRationalImage
      (Standard.parabolicHom i ν (SP : Set (characterLattice T))) : Set (AdelicGroupPoints F G)) *
        siegelSet hi hK hρ C SP T₁ := by
    rw [hcov SP hSP]
    exact Set.mem_univ x
  obtain ⟨r, hr, s', hs', hrs⟩ := hx
  obtain ⟨S₀, hS₀, hind₀, ht₀⟩ := exists_partition_term hG hi hν D hK hρ C T₁ Tp hSPsub hs'
  have hδ₀ : r⁻¹ ∈ parabolicRationalImage
      (Standard.parabolicHom i ν (SP : Set (characterLattice T))) := Subgroup.inv_mem _ hr
  have hδ₀x : r⁻¹ * x = s' := by rw [← hrs, inv_mul_cancel_left]
  have hind₀' : siegelIndicator hG hi D hK hρ C S₀ T₁ Tp (r⁻¹ * x) = 1 := by rwa [hδ₀x]
  have ht₀' : ArthurRelative.tau hG hi ν D (S₀ : Set (characterLattice T))
      (SP : Set (characterLattice T)) (height hi hK hρ (r⁻¹ * x) - Tp) = 1 := by rwa [hδ₀x]
  -- every contributing pair has the parabolic `P_{S₀}`
  have hF3 : ∀ S₁ ∈ SP.powerset, ∀ δ, term S₁ δ ≠ 0 → S₁ = S₀ := by
    intro S₁ hS₁ δ h
    obtain ⟨hi₁, ht₁⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h
    exact (partition_term_unique hcomp hG hi hν D hK hρ C hC T₁ Tp hSPsub
      (Finset.mem_powerset.mp hS₀) (Finset.mem_powerset.mp hS₁) hTT
      (fun S hS x δ => hredSP S hS x δ) hδ₀ (hrep δ) hind₀' ht₀' hi₁ ht₁).1.symm
  -- the coset of `r⁻¹`
  obtain ⟨z, hz, hzr⟩ := hδ₀
  set c₀ : RelativeCosets (F := F) (i := i) (ν := ν) (S₀ : Set (characterLattice T))
      (SP : Set (characterLattice T)) := Quotient.mk _ ⟨z, hz⟩ with hc₀
  have hrel := Quotient.mk_out (s := QuotientGroup.rightRel
    ((parabolicRationalSubgroup F (Standard.parabolicHom i ν (S₀ : Set (characterLattice T)))).subgroupOf
      (parabolicRationalSubgroup F (Standard.parabolicHom i ν (SP : Set (characterLattice T))))))
    (⟨z, hz⟩ : parabolicRationalSubgroup F
      (Standard.parabolicHom i ν (SP : Set (characterLattice T))))
  change QuotientGroup.rightRel _ _ _ at hrel
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf,
    mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage] at hrel
  set q := (((Quotient.out c₀ : parabolicRationalSubgroup F
    (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) : rationalSubgroup F G) :
      AdelicGroupPoints F G) with hq
  have hγ : r⁻¹ * q⁻¹ ∈ parabolicRationalImage
      (Standard.parabolicHom i ν (S₀ : Set (characterLattice T))) := by
    have : ((((⟨z, hz⟩ : parabolicRationalSubgroup F
        (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) * (Quotient.out c₀)⁻¹ :
          parabolicRationalSubgroup F
            (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
              rationalSubgroup F G) : AdelicGroupPoints F G) = r⁻¹ * q⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hq]
      rw [← hzr]
      rfl
    rw [← this]
    exact hrel
  have hqx : q * x = (r⁻¹ * q⁻¹)⁻¹ * s' := by
    rw [← hδ₀x]
    group
  have hS₀s : (S₀ : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun α hα => hSPs (Finset.mem_powerset.mp hS₀ hα)
  have hterm₀ : term S₀ c₀ = 1 := by
    change siegelIndicator hG hi D hK hρ C S₀ T₁ Tp (q * x) *
      ArthurRelative.tau hG hi ν D (S₀ : Set (characterLattice T))
        (SP : Set (characterLattice T)) (height hi hK hρ (q * x) - Tp) = 1
    rw [hqx, siegelIndicator_mul_left hG hi D hK hρ C T₁ Tp S₀ (Subgroup.inv_mem _ hγ),
      tau_height_mul_left hcomp hG hi hν D hK hρ Tp _ hS₀s (Subgroup.inv_mem _ hγ), hind₀, ht₀,
      mul_one]
  refine ⟨fun S₁ hS₁ => ?_, ?_⟩
  · refine Set.Subsingleton.finite fun δ hδ δ' hδ' => hF1 S₁ hS₁ δ δ' hδ hδ'
  · rw [Finset.sum_eq_single S₀]
    · rw [tsum_eq_single c₀]
      · exact hterm₀
      · intro δ hδ
        by_contra h
        exact hδ (hF1 S₀ hS₀ δ c₀ h (by rw [hterm₀]; norm_num))
    · intro S₁ hS₁ hne
      have h0 : ∀ δ, term S₁ δ = 0 := fun δ => by
        by_contra h
        exact hne (hF3 S₁ hS₁ δ h)
      exact (tsum_congr h0).trans tsum_zero
    · intro h
      exact absurd hS₀ h

include hcomp hν in
/-- **Arthur 2005, Lemma 8.2; Arthur 1978, Lemma 6.4 for `P = G`**, for one compact subgroup, from
the reduction-theoretic lemma. -/
theorem isSiegelPartition_of_reduction (hred : IsSiegelReductionLemma hG hi hK hρ) :
    IsSiegelPartition hG hi D hK hρ := by
  intro C T₁ hC hcov
  obtain ⟨c₀, hc₀⟩ := hred C T₁ hC
  refine ⟨|c₀| + ∑ β ∈ simpleFinset ν hG hi, |eval T β T₁|, fun Tp hTp x => ?_⟩
  obtain ⟨hreg, hTT⟩ := regular_of_lt hG hi T₁ c₀ hTp
  have hSPcoe : ((simpleFinset ν hG hi : Finset (characterLattice T)) :
      Set (characterLattice T)) = simpleRelativeRoots i ν := coe_simpleFinset hG hi
  have hSPs := subset_simple_of_subset hG hi (subset_refl (simpleFinset ν hG hi))
  have hredSP := hc₀ Tp hreg (simpleFinset ν hG hi) (Finset.mem_powerset_self _)
  have hGP : ∀ g : rationalSubgroup F G, (g : AdelicGroupPoints F G) ∈ parabolicRationalImage
      (Standard.parabolicHom i ν ((simpleFinset ν hG hi : Finset (characterLattice T)) :
        Set (characterLattice T))) := by
    intro g
    rw [hSPcoe]
    exact rationalSubgroup_le_parabolicRationalImage hG hi hν g.2
  have htau : ∀ (S₁ : Finset (characterLattice T)) (H : V T),
      ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T)) (simpleRelativeRoots i ν) H =
        ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
          ((simpleFinset ν hG hi : Finset (characterLattice T)) : Set (characterLattice T)) H := by
    intro S₁ H
    rw [hSPcoe]
  let term : (S₁ : Finset (characterLattice T)) →
      ParabolicRationalCosets F (Standard.parabolicHom i ν (S₁ : Set (characterLattice T))) → ℤ :=
    fun S₁ δ =>
      siegelIndicator hG hi D hK hρ C S₁ T₁ Tp
          (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
        ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T)) (simpleRelativeRoots i ν)
          (height hi hK hρ (((Quotient.out δ : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
            Tp)
  show (∀ S ∈ (simpleFinset ν hG hi).powerset, (Function.support (term S)).Finite) ∧
    ∑ S ∈ (simpleFinset ν hG hi).powerset, ∑' δ, term S δ = 1
  have hF1 : ∀ S₁ ∈ (simpleFinset ν hG hi).powerset, ∀ δ δ', term S₁ δ ≠ 0 → term S₁ δ' ≠ 0 →
      δ = δ' := by
    intro S₁ hS₁ δ δ' h h'
    obtain ⟨hi₁, ht₁⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h
    obtain ⟨hi₂, ht₂⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h'
    rw [htau] at ht₁ ht₂
    obtain ⟨-, hmem⟩ := partition_term_unique hcomp hG hi hν D hK hρ C hC T₁ Tp
      (subset_refl _) (Finset.mem_powerset.mp hS₁) (Finset.mem_powerset.mp hS₁) hTT
      (fun S hS x δ => hredSP S hS x δ) (hGP _) (hGP _) hi₁ ht₁ hi₂ ht₂
    rw [← Quotient.out_eq δ, ← Quotient.out_eq δ']
    apply Quotient.sound
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage]
    simpa using hmem
  have hx : x ∈ (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
      siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ := by
    rw [hcov]
    exact Set.mem_univ x
  obtain ⟨r, hr, s', hs', hrs⟩ := hx
  obtain ⟨S₀, hS₀, hind₀, ht₀⟩ := exists_partition_term hG hi hν D hK hρ C T₁ Tp
    (subset_refl _) hs'
  have hrr : r⁻¹ ∈ rationalSubgroup F G := Subgroup.inv_mem _ hr
  have hδ₀x : r⁻¹ * x = s' := by rw [← hrs, inv_mul_cancel_left]
  have hind₀' : siegelIndicator hG hi D hK hρ C S₀ T₁ Tp (r⁻¹ * x) = 1 := by rwa [hδ₀x]
  have ht₀' : ArthurRelative.tau hG hi ν D (S₀ : Set (characterLattice T))
      ((simpleFinset ν hG hi : Finset (characterLattice T)) : Set (characterLattice T))
      (height hi hK hρ (r⁻¹ * x) - Tp) = 1 := by rwa [hδ₀x]
  have hF3 : ∀ S₁ ∈ (simpleFinset ν hG hi).powerset, ∀ δ, term S₁ δ ≠ 0 → S₁ = S₀ := by
    intro S₁ hS₁ δ h
    obtain ⟨hi₁, ht₁⟩ := eq_one_of_mul_ne_zero hG hi D hK hρ C T₁ Tp h
    rw [htau] at ht₁
    exact (partition_term_unique hcomp hG hi hν D hK hρ C hC T₁ Tp (subset_refl _)
      (Finset.mem_powerset.mp hS₀) (Finset.mem_powerset.mp hS₁) hTT
      (fun S hS x δ => hredSP S hS x δ) (hGP ⟨r⁻¹, hrr⟩) (hGP _) hind₀' ht₀' hi₁ ht₁).1.symm
  set c₀ : ParabolicRationalCosets F (Standard.parabolicHom i ν (S₀ : Set (characterLattice T))) :=
    Quotient.mk _ ⟨r⁻¹, hrr⟩ with hc₀
  have hrel := Quotient.mk_out (s := QuotientGroup.rightRel
    (parabolicRationalSubgroup F (Standard.parabolicHom i ν (S₀ : Set (characterLattice T)))))
    (⟨r⁻¹, hrr⟩ : rationalSubgroup F G)
  change QuotientGroup.rightRel _ _ _ at hrel
  rw [QuotientGroup.rightRel_apply, mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage] at hrel
  set q := ((Quotient.out c₀ : rationalSubgroup F G) : AdelicGroupPoints F G) with hq
  have hγ : r⁻¹ * q⁻¹ ∈ parabolicRationalImage
      (Standard.parabolicHom i ν (S₀ : Set (characterLattice T))) := by
    simpa [hq] using hrel
  have hqx : q * x = (r⁻¹ * q⁻¹)⁻¹ * s' := by
    rw [← hδ₀x]
    group
  have hS₀s : (S₀ : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun α hα => hSPs (Finset.mem_powerset.mp hS₀ hα)
  have hterm₀ : term S₀ c₀ = 1 := by
    change siegelIndicator hG hi D hK hρ C S₀ T₁ Tp (q * x) *
      ArthurRelative.tau hG hi ν D (S₀ : Set (characterLattice T)) (simpleRelativeRoots i ν)
        (height hi hK hρ (q * x) - Tp) = 1
    rw [htau, hqx, siegelIndicator_mul_left hG hi D hK hρ C T₁ Tp S₀ (Subgroup.inv_mem _ hγ),
      tau_height_mul_left hcomp hG hi hν D hK hρ Tp _ hS₀s (Subgroup.inv_mem _ hγ), hind₀, ht₀,
      mul_one]
  refine ⟨fun S₁ hS₁ => ?_, ?_⟩
  · exact Set.Subsingleton.finite fun δ hδ δ' hδ' => hF1 S₁ hS₁ δ δ' hδ hδ'
  · rw [Finset.sum_eq_single S₀]
    · rw [tsum_eq_single c₀]
      · exact hterm₀
      · intro δ hδ
        by_contra h
        exact hδ (hF1 S₀ hS₀ δ c₀ h (by rw [hterm₀]; norm_num))
    · intro S₁ hS₁ hne
      have h0 : ∀ δ, term S₁ δ = 0 := fun δ => by
        by_contra h
        exact hne (hF3 S₁ hS₁ δ h)
      exact (tsum_congr h0).trans tsum_zero
    · intro h
      exact absurd hS₀ h

include hcomp in
/-- **Arthur 2005, Lemma 8.2 and (8.1) for every compact Iwasawa subgroup**, from the
reduction-theoretic lemma of Arthur 1978, p.941, and the comparison of `𝔞_P` with the
relative root data. -/
theorem iwasawaSiegelPartitionStatement_of_reduction
    (hred : IwasawaSiegelReductionStatement.{u}) : IwasawaSiegelPartitionStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ
  exact ⟨isSiegelPartition_of_reduction hcomp hG hi hν D hK hρ (hred F G T i ν hG hi hν K hK hρ),
    isRelativeSiegelPartition_of_reduction hcomp hG hi hν D hK hρ
      (hred F G T i ν hG hi hν K hK hρ)⟩

end Predicates

end Langlands.Global.ArthurTruncation
