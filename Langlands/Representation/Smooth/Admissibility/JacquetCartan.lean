import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Compact.OrbitMeanTranslation
import Langlands.Representation.Jacquet.SmoothTwist
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Category.Basic

/-!
# Jacquet's admissibility theorem from a Jacquet–Cartan datum

A `JacquetCartanDatum G` on a topological group `G` records the structural input
of Jacquet's proof that irreducible smooth representations are admissible
(Renard VI.2.2): a family of Levi–unipotent pairs with an Iwasawa decomposition,
walls whose unipotent subgroups descend to smaller indices, a Cartan
decomposition of each Levi with a countable middle set, and contraction of the
walls by the Cartan elements away from a compact-times-central region.

`Langlands.isAdmissible_of_jacquetCartanDatum` proves, for a topological group
with a compact open subgroup and such a datum, that every irreducible smooth
complex representation is admissible. The proof takes a minimal index with a
nonzero Jacquet module, an irreducible quotient `σ` of that Jacquet module, kills
the wall Jacquet modules of `σ` by minimality, bounds the fixed vectors of `σ` by
Cartan decomposition, contraction and Schur's lemma in countable dimension, and
embeds the fixed vectors of the original representation in finitely many fixed
vector spaces of `σ`.
-/

noncomputable section

open Filter Topology

namespace Langlands

universe uG uι uV uX

open CuspidalSupport

/-- The structural input of Jacquet's admissibility argument on a topological
group `G`.

* `levi i` and `unipotent i` are the Levi and unipotent subgroups of a parabolic
  indexed by `i`; `levi i` normalizes `unipotent i` and is closed, and
  `G = levi i * unipotent i * C` for a compact set `C` (Iwasawa).
* The index `top` has trivial unipotent subgroup.
* For each wall `a : wall i` there is a subgroup `wallUnipotent i a ≤ levi i`
  (modelled on the unipotent radical of a maximal parabolic of `levi i`);
  `descent` gives an index `j` of smaller rank with
  `unipotent j ⊆ wallUnipotent i a * unipotent i`.
* Every element of `levi i` is `k₁ * t * k₂` with `k₁, k₂` in a compact subset
  `cartanCompact i` of `levi i` and `t` in a countable subset `cartanSet i`.
* `contraction`: for every neighbourhood `O` of `1` and every finite family of
  wall elements there is a compact set `D` such that each Cartan element `t` is
  either `d * z` with `d ∈ D` and `z` central in `levi i`, or conjugates the given
  elements of some wall into `O`. -/
structure JacquetCartanDatum (G : Type uG) [Group G] [TopologicalSpace G] where
  /-- The index type of the parabolic pairs. -/
  ι : Type uι
  /-- A natural-number rank on the indices, decreasing along `descent`. -/
  rank : ι → ℕ
  /-- The Levi subgroup of the pair indexed by `i`. -/
  levi : ι → Subgroup G
  /-- The unipotent subgroup of the pair indexed by `i`. -/
  unipotent : ι → Subgroup G
  /-- The index of the whole group. -/
  top : ι
  unipotent_top : unipotent top = ⊥
  levi_le_normalizer : ∀ i, levi i ≤ Subgroup.normalizer (unipotent i : Set G)
  isClosed_levi : ∀ i, IsClosed (levi i : Set G)
  iwasawa : ∀ i, ∃ C : Set G, IsCompact C ∧
    ∀ g : G, ∃ m ∈ levi i, ∃ n ∈ unipotent i, ∃ c ∈ C, g = m * n * c
  /-- The walls of the Levi subgroup indexed by `i`. -/
  wall : ι → Type uι
  /-- The unipotent subgroup of a wall. -/
  wallUnipotent : ∀ i, wall i → Subgroup G
  wallUnipotent_le : ∀ i a, wallUnipotent i a ≤ levi i
  descent : ∀ i a, ∃ j, rank j < rank i ∧
    ∀ n ∈ unipotent j, ∃ u ∈ wallUnipotent i a, ∃ n' ∈ unipotent i, n = u * n'
  /-- The compact part of the Cartan decomposition of `levi i`. -/
  cartanCompact : ι → Set G
  /-- The countable middle set of the Cartan decomposition of `levi i`. -/
  cartanSet : ι → Set G
  isCompact_cartanCompact : ∀ i, IsCompact (cartanCompact i)
  cartanCompact_subset : ∀ i, cartanCompact i ⊆ levi i
  countable_cartanSet : ∀ i, (cartanSet i).Countable
  cartanSet_subset : ∀ i, cartanSet i ⊆ levi i
  cartan : ∀ i, ∀ m ∈ levi i,
    ∃ k₁ ∈ cartanCompact i, ∃ t ∈ cartanSet i, ∃ k₂ ∈ cartanCompact i, m = k₁ * t * k₂
  contraction : ∀ i, ∀ O ∈ 𝓝 (1 : G), ∀ S : wall i → Finset G,
    (∀ a, (S a : Set G) ⊆ wallUnipotent i a) →
    ∃ D : Set G, IsCompact D ∧ ∀ t ∈ cartanSet i,
      (∃ d ∈ D, ∃ z ∈ levi i, (∀ m ∈ levi i, m * z = z * m) ∧ t = d * z) ∨
        ∃ a, ∀ u ∈ S a, t * u * t⁻¹ ∈ O

namespace JacquetCartanDatum

/-! ### Generic lemmas -/

section Generic

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The coinvariant relations of the trivial subgroup vanish. -/
theorem relations_bot (ρ : Representation ℂ G V) : Jacquet.relations ρ ⊥ = ⊥ := by
  rw [eq_bot_iff, Jacquet.relations_eq_span, Submodule.span_le]
  rintro _ ⟨⟨n, v⟩, rfl⟩
  have hn : (n : G) = 1 := Subgroup.mem_bot.mp n.2
  simp [hn]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Finitely many left cosets of an open subgroup cover a compact set. -/
theorem exists_finset_inv_mul_mem {S : Set G} (hS : IsCompact S) (H : OpenSubgroup G) :
    ∃ E : Finset G, ∀ k ∈ S, ∃ f ∈ E, f⁻¹ * k ∈ H := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun c : G => (c⁻¹ * ·) ⁻¹' (H : Set G))
    (fun c => H.isOpen.preimage (continuous_const.mul continuous_id))
    (fun k _ => Set.mem_iUnion.mpr ⟨k, by
      change k⁻¹ * k ∈ H
      rw [inv_mul_cancel]
      exact H.one_mem⟩)
  refine ⟨t, fun k hk => ?_⟩
  obtain ⟨c, hc, hkc⟩ := Set.mem_iUnion₂.mp (ht hk)
  exact ⟨c, hc, hkc⟩

/-- A compact set moves a smooth vector to finitely many vectors. -/
theorem finite_image_of_isCompact (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {S : Set G} (hS : IsCompact S) (v : V) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨E, hE⟩ := exists_finset_inv_mul_mem hS U
  refine (E.finite_toSet.image fun f => ρ f v).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨f, hf, hfg⟩ := hE g hg
  refine ⟨f, hf, ?_⟩
  have hfix : ρ (f⁻¹ * g) v = v := hU ⟨f⁻¹ * g, hfg⟩
  calc ρ f v = ρ f (ρ (f⁻¹ * g) v) := by rw [hfix]
    _ = ρ g v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- An irreducible smooth representation has countable dimension when every group
element is `a * t * b` with `a, b` in compact sets and `t` in a countable set. -/
theorem rank_le_aleph0_of_compact_cover (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hirr : ρ.IsIrreducible) {A B T : Set G} (hA : IsCompact A) (hB : IsCompact B)
    (hT : T.Countable) (hcover : ∀ g : G, ∃ a ∈ A, ∃ t ∈ T, ∃ b ∈ B, g = a * t * b) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  obtain ⟨v₀, hv₀⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible ρ hirr
  let Y : Set V := (fun b => ρ b v₀) '' B
  have hY : Y.Finite := finite_image_of_isCompact ρ hρ hB v₀
  let Z : Set V := ⋃ t ∈ T, ⋃ y ∈ Y, (fun a => ρ a (ρ t y)) '' A
  have hZ : Z.Countable := hT.biUnion fun t _ => hY.countable.biUnion fun y _ =>
    (finite_image_of_isCompact ρ hρ hA (ρ t y)).countable
  have hsub : Set.range (fun g => ρ g v₀) ⊆ Z := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, ha, t, ht, b, hb, rfl⟩ := hcover g
    simp only [Z, Set.mem_iUnion]
    refine ⟨t, ht, ρ b v₀, ⟨b, hb, rfl⟩, a, ha, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => ρ g v₀)) := by
      rw [LeviAdmissibility.span_orbit_eq_top ρ hirr hv₀]
    _ ≤ Cardinal.mk (Set.range fun g => ρ g v₀) := rank_span_le _
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr (hZ.mono hsub).to_subtype

/-- The open subgroup `{m ∈ M | f⁻¹ * m * f ∈ K}` of a subgroup `M`. -/
def conjOpenSubgroup (M : Subgroup G) (K : OpenSubgroup G) (f : G) : OpenSubgroup M :=
  K.comap ((MulAut.conj f⁻¹).toMonoidHom.comp M.subtype)
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem mem_conjOpenSubgroup (M : Subgroup G) (K : OpenSubgroup G) (f : G) (m : M) :
    m ∈ conjOpenSubgroup M K f ↔ f⁻¹ * (m : G) * f ∈ K := by
  simp [conjOpenSubgroup]

end Generic

/-! ### The irreducible quotient of a minimal Jacquet module -/

variable {G : Type uG} [Group G] [TopologicalSpace G] (𝒟 : JacquetCartanDatum.{uG, uι} G)

theorem isCompact_preimage_levi (i : 𝒟.ι) {S : Set G} (hS : IsCompact S) :
    IsCompact (Subtype.val ⁻¹' S : Set (𝒟.levi i)) :=
  (𝒟.isClosed_levi i).isClosedEmbedding_subtypeVal.isCompact_preimage hS

section Minimal

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An index of minimal rank with a nonzero Jacquet module; every index of smaller
rank has a zero Jacquet module. -/
theorem exists_minimal (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible) :
    ∃ i, Jacquet.relations ρ (𝒟.unipotent i) ≠ ⊤ ∧
      ∀ j, 𝒟.rank j < 𝒟.rank i → Jacquet.relations ρ (𝒟.unipotent j) = ⊤ := by
  obtain ⟨v₀, hv₀⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible ρ hirr
  have hex : {i | Jacquet.relations ρ (𝒟.unipotent i) ≠ ⊤}.Nonempty := ⟨𝒟.top, by
    show Jacquet.relations ρ (𝒟.unipotent 𝒟.top) ≠ ⊤
    rw [𝒟.unipotent_top, relations_bot]
    intro h
    apply hv₀
    have : v₀ ∈ (⊥ : Submodule ℂ V) := h ▸ Submodule.mem_top
    exact (Submodule.mem_bot ℂ).mp this⟩
  obtain ⟨i, hi, hmin⟩ := (InvImage.wf 𝒟.rank wellFounded_lt).has_min _ hex
  exact ⟨i, hi, fun j hj => by_contra fun h => hmin j h hj⟩

end Minimal

section Levi

variable [IsTopologicalGroup G] {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- Irreducible smooth representations of a Levi subgroup have countable
dimension, by its Cartan decomposition. -/
theorem rank_le_aleph0_levi (i : 𝒟.ι) (σ : Representation ℂ (𝒟.levi i) X)
    (hσ : IsSmooth σ) (hirr : σ.IsIrreducible) : Module.rank ℂ X ≤ Cardinal.aleph0 := by
  refine rank_le_aleph0_of_compact_cover σ hσ hirr
    (𝒟.isCompact_preimage_levi i (𝒟.isCompact_cartanCompact i))
    (𝒟.isCompact_preimage_levi i (𝒟.isCompact_cartanCompact i))
    ((𝒟.countable_cartanSet i).preimage Subtype.val_injective) fun m => ?_
  obtain ⟨k₁, hk₁, t, ht, k₂, hk₂, hm⟩ := 𝒟.cartan i m m.2
  exact ⟨⟨k₁, 𝒟.cartanCompact_subset i hk₁⟩, hk₁, ⟨t, 𝒟.cartanSet_subset i ht⟩, ht,
    ⟨k₂, 𝒟.cartanCompact_subset i hk₂⟩, hk₂, Subtype.ext hm⟩

/-- An irreducible smooth representation of a Levi subgroup whose wall Jacquet
modules all vanish has finite-dimensional fixed vectors under every open
subgroup. -/
theorem finite_fixedVectors_levi (i : 𝒟.ι) (K₀ : OpenSubgroup G)
    (hK₀ : IsCompact (K₀ : Set G)) (σ : Representation ℂ (𝒟.levi i) X)
    (hσ : IsSmooth σ) (hirr : σ.IsIrreducible)
    (hwall : ∀ a, Jacquet.relations σ ((𝒟.wallUnipotent i a).subgroupOf (𝒟.levi i)) = ⊤)
    (H : OpenSubgroup (𝒟.levi i)) : Module.Finite ℂ (fixedVectors σ H.toSubgroup) := by
  classical
  let M := 𝒟.levi i
  -- a compact open subgroup of `M` inside `H`
  let Hc : OpenSubgroup M := H ⊓ K₀.comap M.subtype continuous_subtype_val
  have hHc : IsCompact (Hc : Set M) :=
    (𝒟.isCompact_preimage_levi i hK₀).of_isClosed_subset Hc.isClosed
      fun x hx => (OpenSubgroup.mem_inf.mp hx).2
  have hrank := 𝒟.rank_le_aleph0_levi i σ hσ hirr
  obtain ⟨w₀, hw₀⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible σ hirr
  let A : Set M := Subtype.val ⁻¹' 𝒟.cartanCompact i
  have hA : IsCompact A := 𝒟.isCompact_preimage_levi i (𝒟.isCompact_cartanCompact i)
  obtain ⟨E, hE⟩ := LeviAdmissibility.exists_finset_mul_inv_mem hA Hc
  let Y : Set X := (fun k => σ k w₀) '' A
  have hY : Y.Finite := finite_image_of_isCompact σ hσ hA w₀
  -- witnesses expressing every vector through the relations of each wall
  have hrel : ∀ (a : 𝒟.wall i) (y : X),
      ∃ c : ((𝒟.wallUnipotent i a).subgroupOf M × X) →₀ ℂ,
        (c.sum fun p r => r • (σ (p.1 : M) p.2 - p.2)) = y := by
    intro a y
    have hy : y ∈ Jacquet.relations σ ((𝒟.wallUnipotent i a).subgroupOf M) := by
      rw [hwall a]
      exact Submodule.mem_top
    rw [Jacquet.relations_eq_span, Finsupp.mem_span_range_iff_exists_finsupp] at hy
    exact hy
  choose c hc using hrel
  let S : 𝒟.wall i → Finset G := fun a =>
    hY.toFinset.biUnion fun y => (c a y).support.image fun p => ((p.1 : M) : G)
  have hS : ∀ a, (S a : Set G) ⊆ 𝒟.wallUnipotent i a := by
    intro a u hu
    simp only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨y, -, p, -, rfl⟩ := hu
    exact Subgroup.mem_subgroupOf.mp p.1.2
  -- a neighbourhood of `1` whose conjugates by `E` lie in `Hc`
  have h1 : (Hc : Set M) ∈ 𝓝 (1 : M) := Hc.isOpen.mem_nhds Hc.one_mem
  obtain ⟨U, hU, hUHc⟩ := (mem_nhds_subtype (M : Set G) 1 (Hc : Set M)).mp h1
  let O : Set G := ⋂ e ∈ E, (fun g => ((e : M) : G) * g * ((e : M) : G)⁻¹) ⁻¹' U
  have hO : O ∈ 𝓝 (1 : G) := by
    refine (Filter.biInter_finset_mem E).mpr fun e _ => ?_
    have hcont : Continuous fun g : G => ((e : M) : G) * g * ((e : M) : G)⁻¹ := by
      fun_prop
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨D, hD, hDt⟩ := 𝒟.contraction i O hO S hS
  let D' : Set M := Subtype.val ⁻¹' D
  have hD' : IsCompact D' := 𝒟.isCompact_preimage_levi i hD
  let avg := Compact.averageMap σ hσ Hc hHc
  have havg : ∀ h ∈ Hc, ∀ x, avg (σ h x) = avg x := fun h hh x =>
    Compact.orbitMean_apply (σ.comp Hc.toSubgroup.subtype) ⟨h, hh⟩ x
  let Φ : Set X :=
    ⋃ e ∈ (E : Set M), ⋃ y ∈ Y, (fun x => avg (σ e x)) '' ((fun d => σ d y) '' D')
  have hΦ : Φ.Finite := E.finite_toSet.biUnion fun e _ => hY.biUnion fun y _ =>
    (finite_image_of_isCompact σ hσ hD' y).image _
  have hgen : ∀ m : M, avg (σ m w₀) ∈ Submodule.span ℂ Φ := by
    intro m
    obtain ⟨k₁, hk₁, t, ht, k₂, hk₂, hm⟩ := 𝒟.cartan i m m.2
    have hk₁M := 𝒟.cartanCompact_subset i hk₁
    have hk₂M := 𝒟.cartanCompact_subset i hk₂
    have htM := 𝒟.cartanSet_subset i ht
    obtain ⟨e, he, hke⟩ := hE ⟨k₁, hk₁M⟩ hk₁
    have hy : σ ⟨k₂, hk₂M⟩ w₀ ∈ Y := ⟨⟨k₂, hk₂M⟩, hk₂, rfl⟩
    have hm' : m = (⟨k₁, hk₁M⟩ * e⁻¹) * (e * ⟨t, htM⟩) * ⟨k₂, hk₂M⟩ := by
      apply Subtype.ext
      rw [hm]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hstep : avg (σ m w₀) = avg (σ (e * ⟨t, htM⟩) (σ ⟨k₂, hk₂M⟩ w₀)) := by
      rw [hm', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact havg _ hke _
    rw [hstep]
    generalize σ ⟨k₂, hk₂M⟩ w₀ = y at hy
    rcases hDt t ht with ⟨d, hd, z, hz, hzc, rfl⟩ | ⟨a, ha⟩
    · -- `t = d * z` with `z` central: `σ z` is a scalar
      have hdM : d ∈ M := by
        have := M.mul_mem htM (M.inv_mem hz)
        simpa using this
      obtain ⟨s, hs⟩ := LeviAdmissibility.exists_scalar_of_central σ hrank hirr ⟨z, hz⟩
        fun g => Subtype.ext (hzc g g.2)
      have ht' : (⟨d * z, htM⟩ : M) = ⟨d, hdM⟩ * ⟨z, hz⟩ := rfl
      rw [ht', ← mul_assoc, map_mul, Module.End.mul_apply, hs, map_smul, map_smul]
      refine Submodule.smul_mem _ s (Submodule.subset_span ?_)
      simp only [Φ, Set.mem_iUnion]
      refine ⟨e, he, y, hy, σ ⟨d, hdM⟩ y, ⟨⟨d, hdM⟩, hd, rfl⟩, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    · -- `t` contracts the relation elements of the wall `a` into `O`
      rw [← hc a y, map_finsuppSum, map_finsuppSum, Finsupp.sum]
      refine Submodule.sum_mem _ fun p hp => ?_
      have hu : ((p.1 : M) : G) ∈ S a := Finset.mem_biUnion.mpr
        ⟨y, hY.mem_toFinset.mpr hy, Finset.mem_image_of_mem _ hp⟩
      have hconj : (e * ⟨t, htM⟩) * (p.1 : M) * (e * ⟨t, htM⟩)⁻¹ ∈ Hc := by
        apply hUHc
        have := Set.mem_iInter₂.mp (ha _ hu) e he
        simpa [mul_assoc] using this
      have hkill : avg (σ (e * ⟨t, htM⟩) (σ (p.1 : M) p.2)) =
          avg (σ (e * ⟨t, htM⟩) p.2) := by
        rw [← havg _ hconj (σ (e * ⟨t, htM⟩) p.2)]
        congr 1
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right]
      rw [map_smul, map_smul, map_sub, map_sub, hkill, sub_self, smul_zero]
      exact Submodule.zero_mem _
  have hspan : Submodule.span ℂ (Set.range fun m => σ m w₀) ≤
      (Submodule.span ℂ Φ).comap avg := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hgen m
  have hle : fixedVectors σ H.toSubgroup ≤ Submodule.span ℂ Φ := by
    intro x hx
    have hxHc : x ∈ fixedVectors σ Hc.toSubgroup := by
      rw [fixedVectors, Representation.mem_invariants] at hx ⊢
      intro k
      exact hx ⟨k.1, (OpenSubgroup.mem_inf.mp k.2).1⟩
    have hx' : x ∈ (Submodule.span ℂ Φ).comap avg := by
      apply hspan
      rw [LeviAdmissibility.span_orbit_eq_top σ hirr hw₀]
      exact Submodule.mem_top
    rw [Submodule.mem_comap, Compact.averageMap_id σ hσ Hc hHc x hxHc] at hx'
    exact hx'
  have : FiniteDimensional ℂ (Submodule.span ℂ Φ) := FiniteDimensional.span_of_finite ℂ hΦ
  exact Submodule.finiteDimensional_of_le hle

end Levi

end JacquetCartanDatum

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

open JacquetCartanDatum in
/-- **Jacquet's theorem from a Jacquet–Cartan datum.** On a topological group with
a compact open subgroup and a `JacquetCartanDatum`, every irreducible smooth
complex representation is admissible. -/
theorem isAdmissible_of_jacquetCartanDatum (𝒟 : JacquetCartanDatum.{uG, uι} G)
    (hK₀ : ∃ K : OpenSubgroup G, IsCompact (K : Set G)) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible) : IsAdmissible ρ := by
  classical
  obtain ⟨K₀, hK₀⟩ := hK₀
  obtain ⟨v₀, hv₀⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible ρ hirr
  obtain ⟨i, hi, hmin⟩ := 𝒟.exists_minimal ρ hirr
  let N := 𝒟.unipotent i
  let M := 𝒟.levi i
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := 𝒟.levi_le_normalizer i
  let J := Jacquet.action ρ N M hMN
  obtain ⟨C, hC, hiw⟩ := 𝒟.iwasawa i
  -- the Jacquet module is nonzero and generated by the images of `ρ c v₀`, `c ∈ C`
  have : Nontrivial (Jacquet.Coinvariants ρ N) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hi (eq_top_iff.mpr fun v _ => (Jacquet.mk_eq_zero ρ N v).mp (Subsingleton.elim _ _))
  have hCfin := finite_image_of_isCompact ρ hρ hC v₀
  let s : Finset (Jacquet.Coinvariants ρ N) := hCfin.toFinset.image (Jacquet.mk ρ N)
  have hs : ∀ S : Subrepresentation J, (∀ x ∈ s, x ∈ S) → S = ⊤ := by
    intro S hS
    have hspan : Submodule.span ℂ (Set.range fun g => ρ g v₀) ≤
        S.toSubmodule.comap (Jacquet.mk ρ N) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨m, hm, n, hn, c, hc, rfl⟩ := hiw g
      have hmem : Jacquet.mk ρ N (ρ c v₀) ∈ S :=
        hS _ (Finset.mem_image_of_mem _ (hCfin.mem_toFinset.mpr ⟨c, hc, rfl⟩))
      have hJ := S.apply_mem_toSubmodule ⟨m, hm⟩ hmem
      show Jacquet.mk ρ N (ρ (m * n * c) v₀) ∈ S.toSubmodule
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have h2 : Jacquet.mk ρ N (ρ n (ρ c v₀)) = Jacquet.mk ρ N (ρ c v₀) :=
        Jacquet.mk_apply_subgroup ρ N ⟨n, hn⟩ _
      have h3 : Jacquet.mk ρ N (ρ m (ρ n (ρ c v₀))) =
          J ⟨m, hm⟩ (Jacquet.mk ρ N (ρ n (ρ c v₀))) := rfl
      rw [h3, h2]
      exact hJ
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
    exact hspan (QuasicuspidalEmbedding.mem_span_orbit ρ hirr hv₀ v)
  obtain ⟨S, hS⟩ := QuasicuspidalEmbedding.exists_isCoatom_subrepresentation J s hs
  -- the irreducible quotient `σ` of the Jacquet module
  let X := Jacquet.Coinvariants ρ N ⧸ S.toSubmodule
  let σ : Representation ℂ M X :=
    Representation.quotient J S.toSubmodule fun m _ hv => S.apply_mem_toSubmodule m hv
  let π : J.IntertwiningMap σ := ⟨S.toSubmodule.mkQ, fun m => by ext; rfl⟩
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hσirr : σ.IsIrreducible :=
    QuasicuspidalEmbedding.isIrreducible_of_isCoatom π hπ S hS
      fun x => Submodule.Quotient.mk_eq_zero _
  have hσ : IsSmooth σ := isSmooth_of_surjective π hπ (Jacquet.isSmooth_action ρ N M hMN hρ)
  let q : V →ₗ[ℂ] X := S.toSubmodule.mkQ ∘ₗ Jacquet.mk ρ N
  have hq_levi : ∀ m (hm : m ∈ M) (v : V), q (ρ m v) = σ ⟨m, hm⟩ (q v) :=
    fun _ _ _ => rfl
  have hq_unip : ∀ n ∈ N, ∀ v, q (ρ n v) = q v := fun n hn v => by
    show S.toSubmodule.mkQ (Jacquet.mk ρ N (ρ n v)) = S.toSubmodule.mkQ (Jacquet.mk ρ N v)
    rw [show ρ n v = ρ ((⟨n, hn⟩ : N) : G) v from rfl, Jacquet.mk_apply_subgroup]
  have hq_surj : Function.Surjective q :=
    (Submodule.mkQ_surjective _).comp (Jacquet.mk_surjective ρ N)
  -- minimality kills the wall Jacquet modules of `σ`
  have hwall : ∀ a, Jacquet.relations σ ((𝒟.wallUnipotent i a).subgroupOf M) = ⊤ := by
    intro a
    obtain ⟨j, hj, hdesc⟩ := 𝒟.descent i a
    have hrel : Jacquet.relations ρ (𝒟.unipotent j) ≤
        (Jacquet.relations σ ((𝒟.wallUnipotent i a).subgroupOf M)).comap q := by
      rw [Jacquet.relations_eq_span, Submodule.span_le]
      rintro _ ⟨⟨n, x⟩, rfl⟩
      obtain ⟨u, hu, n', hn', hn⟩ := hdesc n n.2
      have huM : u ∈ M := 𝒟.wallUnipotent_le i a hu
      have hu' : (⟨u, huM⟩ : M) ∈ (𝒟.wallUnipotent i a).subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr hu
      show q (ρ n x - x) ∈ Jacquet.relations σ ((𝒟.wallUnipotent i a).subgroupOf M)
      have e1 : q (ρ u (ρ n' x)) = σ ⟨u, huM⟩ (q x) := by
        rw [← hq_unip n' hn' x]
        exact hq_levi u huM (ρ n' x)
      rw [map_sub, hn, map_mul, Module.End.mul_apply, e1]
      exact Jacquet.sub_mem_relations σ _ ⟨_, hu'⟩ (q x)
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hq_surj w
    exact hrel (by rw [hmin j hj]; exact Submodule.mem_top)
  have hfin : ∀ H : OpenSubgroup M, Module.Finite ℂ (fixedVectors σ H.toSubgroup) :=
    𝒟.finite_fixedVectors_levi i K₀ hK₀ σ hσ hσirr hwall
  -- the vectors killed by `q` after every translation form a proper subrepresentation
  let W : Subrepresentation ρ :=
    { toSubmodule := ⨅ g : G, (LinearMap.ker q).comap (ρ g)
      apply_mem_toSubmodule := fun h v hv => by
        simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
        intro g
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (g * h) }
  have hW : W = ⊥ := by
    rcases hirr.eq_bot_or_eq_top W with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible σ hσirr
      obtain ⟨v, rfl⟩ := hq_surj w
      have hv : v ∈ W.toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      have h1 := (Submodule.mem_iInf _).mp hv 1
      rw [Submodule.mem_comap, LinearMap.mem_ker, map_one, Module.End.one_apply] at h1
      exact hw h1
  -- fixed vectors of a compact open subgroup embed in finitely many `σ`-fixed spaces
  refine ⟨hρ, fun K => ?_⟩
  let K' : OpenSubgroup G := K ⊓ K₀
  have hK' : IsCompact (K' : Set G) :=
    hK₀.of_isClosed_subset K'.isClosed fun x hx => (OpenSubgroup.mem_inf.mp hx).2
  obtain ⟨E, hE⟩ := exists_finset_inv_mul_mem hC K'
  let T : fixedVectors ρ K'.toSubgroup →ₗ[ℂ]
      ((f : E) → fixedVectors σ (conjOpenSubgroup M K' (f : G)).toSubgroup) :=
    LinearMap.pi fun f => LinearMap.codRestrict _
      (q ∘ₗ ρ (f : G) ∘ₗ (fixedVectors ρ K'.toSubgroup).subtype) (by
        intro v h
        change σ (h : M) (q (ρ f (v : V))) = q (ρ f (v : V))
        have hk : (f : G)⁻¹ * ((h : M) : G) * f ∈ K' :=
          (mem_conjOpenSubgroup M K' f h).mp h.2
        have hv : ρ ((f : G)⁻¹ * ((h : M) : G) * f) (v : V) = v := v.2 ⟨_, hk⟩
        rw [← hq_levi, ← Module.End.mul_apply, ← map_mul,
          show ((h : M) : G) * f = f * ((f : G)⁻¹ * ((h : M) : G) * f) by group,
          map_mul, Module.End.mul_apply, hv])
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun v hv => ?_
    have hzero : ∀ f : E, q (ρ f v) = 0 := fun f =>
      congrArg Subtype.val (congrFun hv f)
    have hvW : (v : V) ∈ W.toSubmodule := by
      show (v : V) ∈ ⨅ g : G, (LinearMap.ker q).comap (ρ g)
      rw [Submodule.mem_iInf]
      intro g
      rw [Submodule.mem_comap, LinearMap.mem_ker]
      obtain ⟨m, hm, n, hn, c, hc, rfl⟩ := hiw g
      obtain ⟨f, hf, hfc⟩ := hE c hc
      have hvc : ρ c v = ρ f v := by
        have hfix : ρ (f⁻¹ * c) (v : V) = v := v.2 ⟨_, hfc⟩
        calc ρ c v = ρ f (ρ (f⁻¹ * c) v) := by
              rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
          _ = ρ f v := by rw [hfix]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hq_levi m hm,
        hq_unip n hn, hvc, hzero ⟨f, hf⟩, map_zero]
    rw [hW] at hvW
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp hvW)
  have : ∀ f : E, Module.Finite ℂ (fixedVectors σ (conjOpenSubgroup M K' (f : G)).toSubgroup) :=
    fun f => hfin _
  have : Module.Finite ℂ (fixedVectors ρ K'.toSubgroup) := Module.Finite.of_injective T hT
  exact finite_fixedVectors_of_le (ρ := ρ) (H := K'.toSubgroup) (K := K.toSubgroup)
    fun x hx => (OpenSubgroup.mem_inf.mp hx).1

/-- **Jacquet's theorem from a Jacquet–Cartan datum**, for smooth representations
as objects of the smooth category. -/
theorem SmoothRep.isAdmissible_of_jacquetCartanDatum (𝒟 : JacquetCartanDatum.{uG, uι} G)
    (hK₀ : ∃ K : OpenSubgroup G, IsCompact (K : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsIrreducible) : A.IsAdmissible :=
  Langlands.isAdmissible_of_jacquetCartanDatum 𝒟 hK₀ A.representation A.isSmooth hA

end Main

end Langlands
