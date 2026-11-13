import Langlands.Representation.Jacquet.FixedVectorCategoryReduction
import Langlands.Shimura.LevelHeckeBasis
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Category.RenardNoetherian

/-! # The fixed-vector splitting from subquotient closure and Noetherianity -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Langlands.Shimura Langlands.Shimura.LevelHecke Langlands.Induction

universe uG uV uW

namespace Langlands.Jacquet.FixedVectorSplitting

section Transpose

variable {G : Type uG} [Group G]

/-- Inversion `K g L ↦ L g⁻¹ K` of double cosets. -/
def transposeDoubleCoset (K L : Subgroup G) :
    DoubleCoset.Quotient (K : Set G) L ≃ DoubleCoset.Quotient (L : Set G) K where
  toFun := Quotient.lift (fun g : G => DoubleCoset.mk L K g⁻¹) (by
    intro a b hab
    obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.rel_iff.mp hab
    exact DoubleCoset.eq.mpr ⟨l⁻¹, L.inv_mem hl, k⁻¹, K.inv_mem hk, by group⟩)
  invFun := Quotient.lift (fun g : G => DoubleCoset.mk K L g⁻¹) (by
    intro a b hab
    obtain ⟨l, hl, k, hk, rfl⟩ := DoubleCoset.rel_iff.mp hab
    exact DoubleCoset.eq.mpr ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, by group⟩)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g => change DoubleCoset.mk K L g⁻¹⁻¹ = DoubleCoset.mk K L g; rw [inv_inv]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g => change DoubleCoset.mk L K g⁻¹⁻¹ = DoubleCoset.mk L K g; rw [inv_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The transpose `y ↦ (g K ↦ y (g⁻¹ L))` from `ℂ[G/L]^K` to `ℂ[G/K]^L`. -/
def heckeTranspose (K L : CompactOpenLevel G) :
    HeckeSpace ℂ K.subgroup L.subgroup ≃ₗ[ℂ] HeckeSpace ℂ L.subgroup K.subgroup :=
  (heckeBasis ℂ K L).repr.trans
    ((Finsupp.domLCongr (transposeDoubleCoset K.subgroup L.subgroup)).trans
      (heckeBasis ℂ L K).repr.symm)

theorem heckeTranspose_apply (K L : CompactOpenLevel G)
    (a : HeckeSpace ℂ K.subgroup L.subgroup) (g : G) :
    (heckeTranspose K L a : G ⧸ K.subgroup →₀ ℂ) (g : G ⧸ K.subgroup) =
      (a : G ⧸ L.subgroup →₀ ℂ) ((g⁻¹ : G) : G ⧸ L.subgroup) := by
  rw [← heckeBasis_repr_mk ℂ L K, ← heckeBasis_repr_mk ℂ K L]
  change ((heckeBasis ℂ L K).repr ((heckeBasis ℂ L K).repr.symm
      (Finsupp.domLCongr (transposeDoubleCoset K.subgroup L.subgroup)
        ((heckeBasis ℂ K L).repr a)))) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Transpose

section Pairing

variable {X : Type*}

/-- The symmetric pairing `⟨u, w⟩ = ∑ₓ u x * w x` of finitely supported functions. -/
def pair (u w : X →₀ ℂ) : ℂ := u.sum fun x c => c * w x

theorem pair_zero_left (w : X →₀ ℂ) : pair 0 w = 0 := Finsupp.sum_zero_index

theorem pair_single_left (x : X) (c : ℂ) (w : X →₀ ℂ) :
    pair (Finsupp.single x c) w = c * w x :=
  Finsupp.sum_single_index (zero_mul _)

theorem pair_add_left (u₁ u₂ w : X →₀ ℂ) :
    pair (u₁ + u₂) w = pair u₁ w + pair u₂ w :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pair_add_right (u w₁ w₂ : X →₀ ℂ) :
    pair u (w₁ + w₂) = pair u w₁ + pair u w₂ := by
  simp only [pair, Finsupp.coe_add, Pi.add_apply, mul_add, Finsupp.sum_add]

theorem pair_smul_right (u w : X →₀ ℂ) (c : ℂ) :
    pair u (c • w) = c * pair u w := by
  simp only [pair, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => mul_left_comm _ _ _

/-- Pairing against a fixed `u`, as a linear functional. -/
def pairRight (u : X →₀ ℂ) : (X →₀ ℂ) →ₗ[ℂ] ℂ where
  toFun := pair u
  map_add' := pair_add_right u
  map_smul' c w := pair_smul_right u w c

/-- Complex conjugation of the values. -/
def conjFun (z : X →₀ ℂ) : X →₀ ℂ := z.mapRange (starRingEnd ℂ) (map_zero _)

theorem eq_zero_of_pair_conj (z : X →₀ ℂ) (h : pair z (conjFun z) = 0) : z = 0 := by
  classical
  have hs : pair z (conjFun z) = ((∑ x ∈ z.support, Complex.normSq (z x) : ℝ) : ℂ) := by
    rw [pair, Finsupp.sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [conjFun, Finsupp.mapRange_apply, Complex.mul_conj]
  rw [hs, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)] at h
  ext x
  by_contra hx
  exact hx (Complex.normSq_eq_zero.mp (h x (Finsupp.mem_support_iff.mpr hx)))

variable {G : Type uG} [Group G] [MulAction G X]

theorem pair_permutation (g : G) (u w : X →₀ ℂ) :
    pair (permutation ℂ G X ℂ g u) w = pair u (permutation ℂ G X ℂ g⁻¹ w) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, pair_zero_left, pair_zero_left]
  | add a b ha hb => rw [map_add, pair_add_left, pair_add_left, ha, hb]
  | single x c =>
      rw [permutation_single, pair_single_left, pair_single_left, permutation_apply, inv_inv]

theorem conjFun_permutation (g : G) (z : X →₀ ℂ) :
    conjFun (permutation ℂ G X ℂ g z) = permutation ℂ G X ℂ g (conjFun z) := by
  ext x
  rw [permutation_apply, conjFun, conjFun, Finsupp.mapRange_apply, Finsupp.mapRange_apply,
    permutation_apply]

theorem conjFun_mem_fixedVectors (H : Subgroup G) {z : X →₀ ℂ}
    (hz : z ∈ fixedVectors (permutation ℂ G X ℂ) H) :
    conjFun z ∈ fixedVectors (permutation ℂ G X ℂ) H := by
  intro h
  change permutation ℂ G X ℂ h (conjFun z) = conjFun z
  rw [← conjFun_permutation]
  exact congrArg conjFun (hz h)

end Pairing

section PairingMap

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The intertwiner `ℂ[G/L] → ℂ[G/K]` sending `δ_L` to the transpose of `y ∈ ℂ[G/L]^K`. -/
def pairingMap (K L : CompactOpenLevel G) (y : HeckeSpace ℂ K.subgroup L.subgroup) :
    (permRep ℂ L.subgroup).IntertwiningMap (permRep ℂ K.subgroup) :=
  frobenius (permRep ℂ K.subgroup) (heckeTranspose K L y)

/-- The value of `pairingMap y u` at the identity coset is the pairing of `u` with `y`. -/
theorem pairingMap_apply_one (K L : CompactOpenLevel G)
    (y : HeckeSpace ℂ K.subgroup L.subgroup) (u : G ⧸ L.subgroup →₀ ℂ) :
    pairingMap K L y u ((1 : G) : G ⧸ K.subgroup) = pair u y := by
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, pair_zero_left, Finsupp.zero_apply]
  | add a b ha hb => rw [map_add, Finsupp.add_apply, ha, hb, pair_add_left]
  | single q c =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [pairingMap, frobenius_apply, Finsupp.linearCombination_single, cosetVector_mk,
        Finsupp.smul_apply, permutation_apply, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul,
        mul_one, heckeTranspose_apply, inv_inv, pair_single_left]

end PairingMap

section Spans

variable {G : Type uG} [Group G]
variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

/-- The subrepresentation spanned by the translates of a set of vectors. -/
def translateSpan (ρ : Representation ℂ G V) (s : Set V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ {v | ∃ g : G, ∃ w ∈ s, v = ρ g w}
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨h, w, hw, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * h, w, hw, by rw [map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem translate_mem_translateSpan (ρ : Representation ℂ G V) {s : Set V} {v : V}
    (hv : v ∈ s) (g : G) : ρ g v ∈ translateSpan ρ s :=
  Submodule.subset_span ⟨g, v, hv, rfl⟩

theorem mem_translateSpan_of_mem (ρ : Representation ℂ G V) {s : Set V} {v : V}
    (hv : v ∈ s) : v ∈ translateSpan ρ s := by
  have h := translate_mem_translateSpan ρ hv 1
  rwa [map_one, Module.End.one_apply] at h

theorem translateSpan_le {ρ : Representation ℂ G V} {s : Set V} {S : Subrepresentation ρ}
    (h : s ⊆ S) : translateSpan ρ s ≤ S := by
  intro v hv
  refine (Submodule.span_le.mpr ?_) hv
  rintro _ ⟨g, w, hw, rfl⟩
  exact S.apply_mem_toSubmodule g (h hw)

theorem translateSpan_mono (ρ : Representation ℂ G V) {s t : Set V} (h : s ⊆ t) :
    translateSpan ρ s ≤ translateSpan ρ t :=
  translateSpan_le fun _ hv => mem_translateSpan_of_mem ρ (h hv)

/-- The subrepresentation generated by the `H`-fixed vectors. -/
abbrev fixedSpan (ρ : Representation ℂ G V) (H : Subgroup G) : Subrepresentation ρ :=
  translateSpan ρ (fixedVectors ρ H)

variable [TopologicalSpace G]

/-- The subrepresentation generated by the fixed vectors is generated by its fixed vectors. -/
theorem fixedSpan_generated (A : SmoothRep.{0,uG,uV} ℂ G) (H : Subgroup G) :
    fixedVectorGenerated H
      (SmoothRep.subrepresentation A (fixedSpan A.representation H)) := by
  intro S hS
  apply top_unique
  rintro ⟨v, hv⟩ -
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, w, hw, rfl⟩ := hx
      have hw' : (⟨w, mem_translateSpan_of_mem _ hw⟩ :
          SmoothRep.subrepresentation A (fixedSpan A.representation H)) ∈
          fixedVectors (SmoothRep.subrepresentation A
            (fixedSpan A.representation H)).representation H := by
        intro h
        apply Subtype.ext
        exact hw h
      exact S.apply_mem_toSubmodule g (hS hw')
  | zero => exact S.toSubmodule.zero_mem
  | add x y _ _ hx hy => exact S.toSubmodule.add_mem hx hy
  | smul c x _ hx => exact S.toSubmodule.smul_mem c hx

variable [IsTopologicalGroup G]

/-- The vectors all of whose translates have zero `K`-average. -/
def noFixedPart (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : Subrepresentation ρ where
  toSubmodule := ⨅ g : G, LinearMap.ker ((Compact.averageMap ρ hρ K hK).comp (ρ g))
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_iInf] at hv ⊢
    intro h
    have := hv (h * g)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, map_mul, Module.End.mul_apply] at this
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact this

theorem mem_noFixedPart (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (v : V) :
    v ∈ noFixedPart ρ hρ K hK ↔ ∀ g : G, Compact.averageMap ρ hρ K hK (ρ g v) = 0 := by
  change v ∈ ⨅ g : G, LinearMap.ker ((Compact.averageMap ρ hρ K hK).comp (ρ g)) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]

/-- The subrepresentation `noFixedPart` has no nonzero `K`-fixed vectors. -/
theorem fixedVectors_noFixedPart (A : SmoothRep.{0,uG,uV} ℂ G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    fixedVectors (SmoothRep.subrepresentation A
      (noFixedPart A.representation A.isSmooth K hK)).representation K.toSubgroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have hfix : x.val ∈ fixedVectors A.representation K.toSubgroup :=
    fun k => congrArg Subtype.val (hx k)
  have h1 := (mem_noFixedPart A.representation A.isSmooth K hK x.val).mp x.property 1
  rw [map_one, Module.End.one_apply, Compact.averageMap_id _ _ _ _ _ hfix] at h1
  exact h1

end Spans

section Core

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of a subrepresentation under an intertwiner. -/
def imageSub {V : Type uW} {W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (N : Subrepresentation ρ) : Subrepresentation σ where
  toSubmodule := N.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g w hw := by
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨ρ g v, N.apply_mem_toSubmodule g hv, f.isIntertwining _ _ g v⟩

/-- Compact averaging preserves every subrepresentation. -/
theorem averageMap_mem {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (N : Subrepresentation ρ) {v : V} (hv : v ∈ N) :
    Compact.averageMap ρ hρ K hK v ∈ N := by
  let A : SmoothRep.{0,uG,uW} ℂ G := SmoothRep.of ρ hρ
  let N' : Subrepresentation A.representation := N
  let ι := SmoothRep.hom (SmoothRep.subtype A N')
  have h := LinearMap.congr_fun (Compact.averageMap_commute _ ρ
    (SmoothRep.subrepresentation A N').isSmooth hρ K hK ι) ⟨v, hv⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  change ι _ = Compact.averageMap ρ hρ K hK v at h
  rw [← h]
  exact (Compact.averageMap _ (SmoothRep.subrepresentation A N').isSmooth K hK ⟨v, hv⟩).property

/-- If an intertwiner lands in a fixed-vector-generated representation, then on every
subrepresentation it agrees with its restriction to the part generated by fixed vectors. -/
theorem exists_fixedSpan_eq_of_generated (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects]
    {V : Type uW} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (B : SmoothRep.{0,uG,uV} ℂ G) (hB : fixedVectorGenerated K.toSubgroup B)
    (Φ : ρ.IntertwiningMap B.representation) (N : Subrepresentation ρ) {n : V} (hn : n ∈ N) :
    ∃ s ∈ fixedSpan ρ K.toSubgroup, s ∈ N ∧ Φ s = Φ n := by
  let S := imageSub Φ N
  have : Mono (SmoothRep.subtype B S) :=
    (SmoothRep.mono_iff_injective _).mpr (SmoothRep.subtype_injective B S)
  have hBS : fixedVectorGenerated K.toSubgroup (SmoothRep.subrepresentation B S) :=
    (fixedVectorGenerated K.toSubgroup).prop_of_mono (SmoothRep.subtype B S) hB
  let T := fixedVectorComap (SmoothRep.hom (SmoothRep.subtype B S))
    (imageSub Φ (fixedSpan ρ K.toSubgroup ⊓ N))
  have hT : T = ⊤ := by
    apply hBS
    rintro ⟨x, hxS⟩ hx
    obtain ⟨m, hm, rfl⟩ := hxS
    have hfix : Φ m ∈ fixedVectors B.representation K.toSubgroup :=
      fun k => congrArg Subtype.val (hx k)
    refine ⟨Compact.averageMap ρ hρ K hK m,
      ⟨mem_translateSpan_of_mem _ (Compact.averageMap_mem_fixedVectors ρ hρ K hK m),
        averageMap_mem ρ hρ K hK N hm⟩, ?_⟩
    have hc := LinearMap.congr_fun
      (Compact.averageMap_commute ρ B.representation hρ B.isSmooth K hK Φ) m
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    change Φ (Compact.averageMap ρ hρ K hK m) =
      Compact.averageMap B.representation B.isSmooth K hK (Φ m) at hc
    rw [Compact.averageMap_id _ _ _ _ _ hfix] at hc
    exact hc
  have hx : (⟨Φ n, ⟨n, hn, rfl⟩⟩ : SmoothRep.subrepresentation B S) ∈ T := by
    rw [hT]; trivial
  obtain ⟨s, ⟨hs1, hs2⟩, hse⟩ := hx
  exact ⟨s, hs1, hs2, hse⟩

/-- The vectors killed by `pairingMap y` for all `y ∈ t`. -/
def pairingKernel (K L : CompactOpenLevel G) (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)) :
    Subrepresentation (permRep ℂ L.subgroup) where
  toSubmodule := ⨅ y ∈ t, LinearMap.ker (pairingMap K L y).toLinearMap
  apply_mem_toSubmodule g v hv := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
    intro y hy
    have h := hv y hy
    rw [Representation.IntertwiningMap.toLinearMap_apply] at h ⊢
    rw [Representation.IntertwiningMap.isIntertwining, h, map_zero]

theorem mem_pairingKernel (K L : CompactOpenLevel G)
    (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)) (v : G ⧸ L.subgroup →₀ ℂ) :
    v ∈ pairingKernel K L t ↔ ∀ y ∈ t, pairingMap K L y v = 0 := by
  change v ∈ ⨅ y ∈ t, LinearMap.ker (pairingMap K L y).toLinearMap ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

/-- Modulo the part generated by `K`-fixed vectors, every vector is killed by finitely many
pairing maps. -/
theorem exists_fixedSpan_sub_mem_pairingKernel (K L : CompactOpenLevel G)
    [Small.{uV} (G ⧸ K.subgroup)]
    [(fixedVectorGenerated.{uG,uV} K.subgroup).IsClosedUnderSubobjects]
    (t : Finset (HeckeSpace ℂ K.subgroup L.subgroup)) (u : G ⧸ L.subgroup →₀ ℂ) :
    ∃ s ∈ fixedSpan (permRep ℂ L.subgroup) K.subgroup,
      u - s ∈ pairingKernel K L (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨0, (fixedSpan _ _).toSubmodule.zero_mem, ?_⟩
      rw [mem_pairingKernel]
      intro y hy
      simp at hy
  | insert y t _ ih =>
      obtain ⟨s, hs, hus⟩ := ih
      let e := smallFixedVectorGeneratorEquiv.{uG,uV} K.openSubgroup
      obtain ⟨s', hs'1, hs'2, he⟩ := exists_fixedSpan_eq_of_generated.{uG,uV} K.openSubgroup
        K.isCompact (permRep ℂ L.subgroup) (isSmooth_permutation L.subgroup L.openSubgroup.isOpen)
        (smallFixedVectorGenerator.{uG,uV} K.openSubgroup)
        (smallFixedVectorGenerator_generated K.openSubgroup)
        (e.toIntertwiningMap.comp (pairingMap K L y)) (pairingKernel K L t) hus
      have he' : pairingMap K L y s' = pairingMap K L y (u - s) :=
        e.toLinearEquiv.injective he
      refine ⟨s + s', (fixedSpan _ _).toSubmodule.add_mem hs hs'1, ?_⟩
      have hsub : u - (s + s') = (u - s) - s' := by abel
      rw [hsub, mem_pairingKernel]
      intro z hz
      rw [Finset.coe_insert, Set.mem_insert_iff] at hz
      rcases hz with rfl | hz
      · rw [map_sub, he', sub_self]
      · rw [map_sub, (mem_pairingKernel K L _ _).mp hus z hz,
          (mem_pairingKernel K L _ _).mp hs'2 z hz, sub_zero]

/-- If finitely many `K`-fixed vectors of `ℂ[G/L]` generate all `K`-fixed vectors, then every
vector of `ℂ[G/L]` is the sum of a vector generated by `K`-fixed vectors and a vector without
`K`-fixed components. -/
theorem exists_fixedSpan_sub_mem_noFixedPart (K L : CompactOpenLevel G)
    [Small.{uV} (G ⧸ K.subgroup)]
    [(fixedVectorGenerated.{uG,uV} K.subgroup).IsClosedUnderSubobjects]
    (t : Finset (HeckeSpace ℂ K.subgroup L.subgroup))
    (ht : ∀ z ∈ fixedVectors (permRep ℂ L.subgroup) K.subgroup,
      z ∈ translateSpan (permRep ℂ L.subgroup)
        ((↑) '' (t : Set (HeckeSpace ℂ K.subgroup L.subgroup))))
    (u : G ⧸ L.subgroup →₀ ℂ) :
    ∃ s ∈ fixedSpan (permRep ℂ L.subgroup) K.subgroup,
      u - s ∈ noFixedPart (permRep ℂ L.subgroup)
        (isSmooth_permutation L.subgroup L.openSubgroup.isOpen) K.openSubgroup K.isCompact := by
  obtain ⟨s, hs, hn⟩ := exists_fixedSpan_sub_mem_pairingKernel.{uG,uV} K L t u
  refine ⟨s, hs, ?_⟩
  rw [mem_noFixedPart]
  intro g
  set z := Compact.averageMap (permRep ℂ L.subgroup)
    (isSmooth_permutation L.subgroup L.openSubgroup.isOpen) K.openSubgroup K.isCompact
    (permRep ℂ L.subgroup g (u - s)) with hz
  have hzker : z ∈ pairingKernel K L (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)) :=
    averageMap_mem _ _ _ _ _ ((pairingKernel K L _).apply_mem_toSubmodule g hn)
  have hzfix : z ∈ fixedVectors (permRep ℂ L.subgroup) K.subgroup :=
    Compact.averageMap_mem_fixedVectors _ _ _ _ _
  have hle : (translateSpan (permRep ℂ L.subgroup)
      ((↑) '' (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)))).toSubmodule ≤
      LinearMap.ker (pairRight z) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, _, ⟨y, hy, rfl⟩, rfl⟩
    change pair z (permutation ℂ G (G ⧸ L.subgroup) ℂ h (y : G ⧸ L.subgroup →₀ ℂ)) = 0
    have hp := pair_permutation h⁻¹ z (y : G ⧸ L.subgroup →₀ ℂ)
    rw [inv_inv] at hp
    rw [← hp, ← pairingMap_apply_one K L y,
      (mem_pairingKernel K L _ _).mp ((pairingKernel K L _).apply_mem_toSubmodule h⁻¹ hzker) y hy,
      Finsupp.zero_apply]
  exact eq_zero_of_pair_conj z (hle (ht _ (conjFun_mem_fixedVectors _ hzfix)))

end Core

section Finiteness

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Intertwiners carry translate spans into translate spans of the image set. -/
theorem map_mem_translateSpan {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) {s : Set V} {v : V} (hv : v ∈ translateSpan ρ s) :
    f v ∈ translateSpan σ (f '' s) := by
  have h : translateSpan ρ s ≤ fixedVectorComap f (translateSpan σ (f '' s)) :=
    translateSpan_le fun w hw => mem_translateSpan_of_mem σ ⟨w, hw, rfl⟩
  exact h hv

/-- Noetherianity of the smooth category gives finitely many `K`-fixed vectors of `ℂ[G/L]`
whose translates span all `K`-fixed vectors. -/
theorem exists_finset_translateSpan (K L : CompactOpenLevel G) [Small.{uV} (G ⧸ L.subgroup)]
    (hcat : Langlands.Renard.IsNoetherianCategory (SmoothRep.{0,uG,uV} ℂ G)) :
    ∃ t : Finset (HeckeSpace ℂ K.subgroup L.subgroup),
      ∀ z ∈ fixedVectors (permRep ℂ L.subgroup) K.subgroup,
        z ∈ translateSpan (permRep ℂ L.subgroup)
          ((↑) '' (t : Set (HeckeSpace ℂ K.subgroup L.subgroup))) := by
  classical
  let Ps := smallFixedVectorGenerator.{uG,uV} L.openSubgroup
  have hN : IsNoetherian (MonoidAlgebra ℂ G) Ps.representation.asModule :=
    (SmoothRep.renardNoetherian_iff Ps).mp (hcat.2 Ps ((SmoothRep.renardFiniteType_iff Ps).mpr
      (smallFixedVectorGenerator_finite L.openSubgroup)))
  let e := smallFixedVectorGeneratorEquiv.{uG,uV} L.openSubgroup
  let φ : Finset (HeckeSpace ℂ K.subgroup L.subgroup) →
      Submodule (MonoidAlgebra ℂ G) Ps.representation.asModule := fun t =>
    Subrepresentation.asSubmodule (fixedVectorComap e.symm.toIntertwiningMap
      (translateSpan (permRep ℂ L.subgroup)
        ((↑) '' (t : Set (HeckeSpace ℂ K.subgroup L.subgroup)))))
  have hmono : Monotone φ := fun t₁ t₂ h v hv =>
    translateSpan_mono _ (Set.image_mono (Finset.coe_subset.mpr h)) hv
  obtain ⟨_, ⟨t₀, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr hN (Set.range φ) (Set.range_nonempty φ)
  refine ⟨t₀, fun z hz => ?_⟩
  let t₁ := insert (⟨z, hz⟩ : HeckeSpace ℂ K.subgroup L.subgroup) t₀
  have hle : φ t₀ ≤ φ t₁ := hmono (Finset.subset_insert _ _)
  have heq : φ t₀ = φ t₁ := by
    by_contra hne
    exact hmax (φ t₁) ⟨t₁, rfl⟩ (lt_of_le_of_ne hle hne)
  have key : e.symm.toIntertwiningMap (e.toIntertwiningMap z) = z :=
    e.toLinearEquiv.symm_apply_apply z
  have hz1 : (e.toIntertwiningMap z : Ps.representation.asModule) ∈ φ t₁ := by
    change e.symm.toIntertwiningMap (e.toIntertwiningMap z) ∈ translateSpan _ _
    rw [key]
    exact mem_translateSpan_of_mem _
      ⟨⟨z, hz⟩, Finset.mem_coe.mpr (Finset.mem_insert_self _ _), rfl⟩
  rw [← heq] at hz1
  have hz0 : e.symm.toIntertwiningMap (e.toIntertwiningMap z) ∈
      translateSpan (permRep ℂ L.subgroup)
        ((↑) '' (t₀ : Set (HeckeSpace ℂ K.subgroup L.subgroup))) := hz1
  rwa [key] at hz0

end Finiteness

section Splitting

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The splitting of every smooth representation into the part generated by `K`-fixed
vectors and a part without `K`-fixed vectors, from subobject closure of fixed-vector
generation and Noetherianity of the smooth category. -/
theorem fixedVectorSplitting_of_noetherian (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects]
    (hcat : Langlands.Renard.IsNoetherianCategory (SmoothRep.{0,uG,uV} ℂ G))
    (hsmall : ∀ L : OpenSubgroup G, Small.{uV} (G ⧸ L.toSubgroup)) :
    fixedVectorSplitting.{uG,uV} K := by
  intro A
  refine ⟨fixedSpan A.representation K.toSubgroup,
    noFixedPart A.representation A.isSmooth K hK,
    fixedSpan_generated A K.toSubgroup, fixedVectors_noFixedPart A K hK, ?_⟩
  apply top_unique
  intro a _
  obtain ⟨U, hU⟩ := A.isSmooth a
  let Kc : CompactOpenLevel G := ⟨K, hK⟩
  let L : CompactOpenLevel G := ⟨K ⊓ U, hK.inter_right U.isClosed⟩
  have ha : a ∈ fixedVectors A.representation L.subgroup := fun l => hU ⟨l.val, l.property.2⟩
  have : Small.{uV} (G ⧸ Kc.subgroup) := hsmall K
  have : Small.{uV} (G ⧸ L.subgroup) := hsmall L.openSubgroup
  have : (fixedVectorGenerated.{uG,uV} Kc.subgroup).IsClosedUnderSubobjects := inferInstanceAs
    ((fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects)
  obtain ⟨t, ht⟩ := exists_finset_translateSpan.{uG,uV} Kc L hcat
  obtain ⟨s, hs, hn⟩ := exists_fixedSpan_sub_mem_noFixedPart.{uG,uV} Kc L t ht
    (unitElement (R := ℂ) L.subgroup : G ⧸ L.subgroup →₀ ℂ)
  let f := frobenius A.representation ⟨a, ha⟩
  have hfa : f (unitElement (R := ℂ) L.subgroup : G ⧸ L.subgroup →₀ ℂ) = a := frobenius_unitElement _ _
  have hfs : f s ∈ fixedSpan A.representation K.toSubgroup :=
    translateSpan_mono _ (by rintro _ ⟨w, hw, rfl⟩; exact map_mem_fixedVectors f hw)
      (map_mem_translateSpan f hs)
  have hfn : f ((unitElement (R := ℂ) L.subgroup : G ⧸ L.subgroup →₀ ℂ) - s) ∈
      noFixedPart A.representation A.isSmooth K hK := by
    rw [mem_noFixedPart]
    intro g
    have h0 := (mem_noFixedPart _ _ _ _ _).mp hn g
    have hc := LinearMap.congr_fun (Compact.averageMap_commute (permRep ℂ L.subgroup)
      A.representation (isSmooth_permutation L.subgroup L.openSubgroup.isOpen) A.isSmooth K hK f)
      (permRep ℂ L.subgroup g ((unitElement (R := ℂ) L.subgroup : G ⧸ L.subgroup →₀ ℂ) - s))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    change f (Compact.averageMap _ _ K hK _) = Compact.averageMap A.representation
      A.isSmooth K hK (f _) at hc
    rw [← f.isIntertwining _ _ g, ← hc]
    change f (Compact.averageMap _ _ Kc.openSubgroup Kc.isCompact _) = 0
    rw [h0, map_zero]
  have hsum : a = f s + f ((unitElement (R := ℂ) L.subgroup : G ⧸ L.subgroup →₀ ℂ) - s) := by
    rw [map_sub, add_sub_cancel, hfa]
  rw [hsum]
  exact (Submodule.mem_sup.mpr ⟨_, hfs, _, hfn, rfl⟩ : _ ∈ (_ ⊔ _ : Submodule ℂ A))

end Splitting

end Langlands.Jacquet.FixedVectorSplitting
