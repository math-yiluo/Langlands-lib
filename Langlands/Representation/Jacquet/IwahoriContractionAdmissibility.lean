import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.Representation.Jacquet.CompressionStabilizationProof
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Representation.Jacquet.SmoothTwist

/-!
# Jacquet's lemma from abstract Iwahori factorization and contraction

For a compact open subgroup `K` with an Iwahori factorization relative to
`(Nbar, M, N)` and an element `g` of `M` contracting `K ∩ N` and expanding
`K ∩ Nbar`, the actual quotient map from `K`-fixed vectors to the `K ∩ M`-fixed
vectors of the `N`-coinvariants is bijective on the stable image of the
compressed action of `g` whenever the `K`-fixed vectors are finite dimensional.
Consequently Jacquet restriction preserves admissibility whenever such pairs
`(K, g)` exist with `K ∩ M` arbitrarily small. No reductive structure is used.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

section Abstract

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem apply_eq_of_mem_fixedVectors {ρ : Representation ℂ G V} {H : Subgroup G}
    {v : V} (hv : v ∈ fixedVectors ρ H) {k : G} (hk : k ∈ H) : ρ k v = v :=
  hv ⟨k, hk⟩

private theorem averageMap_apply_mem (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k v) = Compact.averageMap ρ hρ K hK v := by
  let τ := ρ.comp K.toSubgroup.subtype
  let k' : K.toSubgroup := ⟨k, hk⟩
  have ho : Compact.orbit τ (τ k' v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * k', by simp [τ]⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * k'⁻¹, ?_⟩
      simp [τ, map_mul, Module.End.mul_apply]
  change Compact.orbitMean τ (τ k' v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Conjugation of `ρ k` past `ρ b`: if `b⁻¹ k b` fixes `v`, then `k` fixes `ρ b v`. -/
private theorem apply_apply_eq {ρ : Representation ℂ G V} {H : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H) (b k : G) (hk : b⁻¹ * k * b ∈ H) :
    ρ k (ρ b v) = ρ b v := by
  calc
    ρ k (ρ b v) = ρ b (ρ (b⁻¹ * k * b) v) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = ρ b v := congrArg (ρ b) (apply_eq_of_mem_fixedVectors hv hk)

section Compression

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N M Nbar : Subgroup G)

omit [IsTopologicalGroup G] in
/-- If `b` conjugates `K ∩ Nbar` and `K ∩ M` into `K` from the right, then every
`K`-translate of `ρ b v`, for `v` fixed by `K`, is a `K ∩ N`-translate. -/
theorem exists_upper_translate
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (b : G) (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, b⁻¹ * l * b ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, b⁻¹ * m * b ∈ K)
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) (k : G) (hk : k ∈ K) :
    ∃ u ∈ K.toSubgroup ⊓ N, ρ k (ρ b v) = ρ u (ρ b v) := by
  obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := hfactor k⁻¹ (K.inv_mem hk)
  have heq : k = u⁻¹ * m⁻¹ * l⁻¹ := by
    rw [← inv_inv k, hprod]
    group
  refine ⟨u⁻¹, (K.toSubgroup ⊓ N).inv_mem hu, ?_⟩
  rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    apply_apply_eq hv b l⁻¹ (hlow _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)),
    apply_apply_eq hv b m⁻¹ (hmid _ ((K.toSubgroup ⊓ M).inv_mem hm))]

/-- Multiplicativity of compression for a pair `(a, b)` adapted to the
factorization. -/
theorem compressedAction_mul_of_factor
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (a b : G) (hup : ∀ u ∈ K.toSubgroup ⊓ N, a * u * a⁻¹ ∈ K)
    (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, b⁻¹ * l * b ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, b⁻¹ * m * b ∈ K) :
    compressedAction ρ hρ K hK (a * b) =
      compressedAction ρ hρ K hK a * compressedAction ρ hρ K hK b := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change Compact.averageMap ρ hρ K hK (ρ (a * b) v.val) =
    Compact.averageMap ρ hρ K hK (ρ a
      (Compact.averageMap ρ hρ K hK (ρ b v.val)))
  rw [map_mul, Module.End.mul_apply]
  symm
  apply map_averageMap_of_forall_eq ρ hρ K hK
    ((Compact.averageMap ρ hρ K hK).comp (ρ a)) (ρ b v.val)
  intro k
  change Compact.averageMap ρ hρ K hK (ρ a (ρ k.val (ρ b v.val))) = _
  obtain ⟨u, hu, hk⟩ := exists_upper_translate ρ K N M Nbar hfactor b hlow hmid
    v.val v.property k.val k.property
  rw [hk]
  calc
    _ = Compact.averageMap ρ hρ K hK (ρ (a * u * a⁻¹) (ρ a (ρ b v.val))) := by
      congr 1
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = _ := averageMap_apply_mem ρ hρ K hK (hup u hu) _

/-- Compression by an element `b` of `M` adapted to the factorization intertwines
the actual quotient map with the unnormalized descended action of `b`. -/
theorem mk_compressedAction_of_factor (hMN : M ≤ Subgroup.normalizer N)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (b : M) (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, (b : G)⁻¹ * l * b ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, (b : G)⁻¹ * m * b ∈ K)
    (v : fixedVectors ρ K.toSubgroup) :
    mk ρ N (compressedAction ρ hρ K hK b v : V) = action ρ N M hMN b (mk ρ N (v : V)) := by
  rw [action_mk]
  change mk ρ N (Compact.averageMap ρ hρ K hK (ρ b v.val)) = mk ρ N (ρ b v.val)
  apply map_averageMap_of_forall_eq
  intro k
  obtain ⟨u, hu, hk⟩ := exists_upper_translate ρ K N M Nbar hfactor b hlow hmid
    v.val v.property k.val k.property
  rw [hk]
  exact mk_apply_subgroup ρ N ⟨u, hu.2⟩ _

end Compression

section Contraction

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}

/-- Compression by powers of `g` is the power of compression by `g`. -/
theorem IsIwahoriContraction.compressedAction_pow (h : IsIwahoriContraction K N M Nbar g)
    (r : ℕ) : compressedAction ρ hρ K hK (g ^ r) = compressedAction ρ hρ K hK g ^ r := by
  induction r with
  | zero => simp only [pow_zero, compressedAction_one]; rfl
  | succ r ih =>
    rw [pow_succ, compressedAction_mul_of_factor ρ hρ K hK N M Nbar h.factor (g ^ r) g
      (fun u hu => (h.upper_pow r u hu).1) (fun l hl => (h.lower l hl).1)
      (fun m hm => (h.levi m hm).1), ih, pow_succ]

/-- The unnormalized descended action of `g` on the coinvariants. -/
theorem mk_compressedAction_of_iwahoriContraction (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (v : fixedVectors ρ K.toSubgroup) :
    mk ρ N (compressedAction ρ hρ K hK g v : V) =
      action ρ N M hMN ⟨g, h.mem_levi⟩ (mk ρ N (v : V)) :=
  mk_compressedAction_of_factor ρ hρ K hK N M Nbar hMN h.factor ⟨g, h.mem_levi⟩
    (fun l hl => (h.lower l hl).1) (fun m hm => (h.levi m hm).1) v

/-- Span induction combines the eventual thresholds for genuine Jacquet relations. -/
private theorem relations_eventually_average_zero (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (v : V) (hv : v ∈ relations ρ N) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → Compact.averageMap ρ hρ K hK (ρ (g ^ s) v) = 0 := by
  rw [relations_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, w⟩, rfl⟩ := hw
    obtain ⟨r, hr⟩ := h.eventually_mem hMN x
    refine ⟨r, fun s hs => ?_⟩
    rw [map_sub, map_sub, sub_eq_zero]
    calc
      _ = Compact.averageMap ρ hρ K hK
          (ρ (g ^ s * x.val * (g ^ s)⁻¹) (ρ (g ^ s) w)) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := averageMap_apply_mem ρ hρ K hK (hr s hs) _
  | zero => exact ⟨0, fun s _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨rx, hx⟩ := hx
    obtain ⟨ry, hy⟩ := hy
    refine ⟨max rx ry, fun s hs => ?_⟩
    rw [map_add, map_add, hx s (le_trans (le_max_left _ _) hs),
      hy s (le_trans (le_max_right _ _) hs), add_zero]
  | smul c x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨r, fun s hs => ?_⟩
    rw [map_smul, map_smul, hr s hs, smul_zero]

/-- The generalized kernel of compression by `g` is the kernel of the actual
quotient map on `K`-fixed vectors. -/
theorem powerKernelSup_eq_ker_of_iwahoriContraction (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) :
    powerKernelSup ρ hρ K hK g =
      LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
  have hfixed (v : fixedVectors ρ K.toSubgroup) :
      v ∈ LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) ↔ mk ρ N v.val = 0 := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext_iff
  have hmk (r : ℕ) (v : fixedVectors ρ K.toSubgroup) :
      mk ρ N ((compressedAction ρ hρ K hK g ^ r) v : V) =
        action ρ N M hMN (⟨g, h.mem_levi⟩ ^ r) (mk ρ N (v : V)) := by
    induction r generalizing v with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN, ih, pow_succ',
        map_mul, Module.End.mul_apply]
  apply le_antisymm
  · apply iSup_le
    intro r v hv
    apply (hfixed v).mpr
    have hz : (compressedAction ρ hρ K hK g ^ r) v = 0 := hv
    have hq := hmk r v
    rw [hz] at hq
    have hi := (Representation.apply_bijective (action ρ N M hMN)
      (⟨g, h.mem_levi⟩ ^ r)).injective
    apply hi
    simpa only [ZeroMemClass.coe_zero, map_zero] using hq.symm
  · intro v hv
    have hvrel := (mk_eq_zero ρ N v.val).mp ((hfixed v).mp hv)
    obtain ⟨r, hr⟩ := relations_eventually_average_zero ρ hρ hK h hMN v.val hvrel
    apply (le_iSup (fun s : ℕ => LinearMap.ker (compressedAction ρ hρ K hK g ^ s)) r)
    rw [LinearMap.mem_ker, ← h.compressedAction_pow ρ hρ hK r]
    apply Subtype.ext
    exact hr r le_rfl

omit [IsTopologicalGroup G] in
include hρ in
/-- Some power of `g` carries any vector to a vector fixed by `K ∩ Nbar`. -/
theorem IsIwahoriContraction.exists_pow_lower_fixed (h : IsIwahoriContraction K N M Nbar g)
    (v : V) : ∃ s : ℕ, ∀ l ∈ K.toSubgroup ⊓ Nbar, ρ l (ρ (g ^ s) v) = ρ (g ^ s) v := by
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨s, hs⟩ := h.contract U
  exact ⟨s, fun l hl => apply_apply_eq hU (g ^ s) l (hs l hl)⟩

/-- Jacquet's lemma: with finite-dimensional `K`-fixed vectors, the actual quotient
map restricted to the stable image of compression by `g` is bijective onto the
`K ∩ M`-fixed coinvariants. -/
theorem stableImageJacquetMap_bijective_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN) := by
  have hcompl := powerKernelSup_isCompl_stableImage ρ hρ K hK g hfin
  have hker := powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN
  let gM : M := ⟨g, h.mem_levi⟩
  -- Every fixed vector has the quotient of a stable-image vector.
  have hsplit : ∀ x : fixedVectors ρ K.toSubgroup,
      ∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = mk ρ N (x : V) := by
    intro x
    have hx : x ∈ powerKernelSup ρ hρ K hK g ⊔ stableImage ρ hρ K hK g := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hker, LinearMap.mem_ker] at hk
    have hk0 : mk ρ N (k : V) = 0 := congrArg Subtype.val hk
    rw [Submodule.coe_add, map_add, hk0, zero_add]
  -- The action of `g` can be cancelled on the image of the stable image.
  have hstep : ∀ z : Coinvariants ρ N,
      (∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = action ρ N M hMN gM z) →
      ∃ t : stableImage ρ hρ K hK g, mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    rintro z ⟨t, htz⟩
    obtain ⟨t', rfl⟩ := (stableImageAction_bijective ρ hρ K hK g hfin).2 t
    refine ⟨t', ?_⟩
    apply (Representation.apply_bijective (action ρ N M hMN) gM).injective
    rw [← htz]
    exact (mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN (t' : fixedVectors ρ K.toSubgroup)).symm
  have hpow : ∀ (s : ℕ) (z : Coinvariants ρ N),
      (∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = action ρ N M hMN (gM ^ s) z) →
      ∃ t : stableImage ρ hρ K hK g, mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    intro s
    induction s with
    | zero =>
      intro z hz
      simpa using hz
    | succ s ih =>
      intro z hz
      apply ih
      apply hstep
      simpa only [pow_succ', map_mul, Module.End.mul_apply] using hz
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have h1 : (t : fixedVectors ρ K.toSubgroup) ∈
        LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := ht
    rw [← hker] at h1
    have h0 := hcompl.disjoint.le_bot ⟨h1, t.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro y
    suffices hy : ∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = (y : Coinvariants ρ N) by
      obtain ⟨t, ht⟩ := hy
      exact ⟨t, Subtype.ext ht⟩
    obtain ⟨v, hv⟩ := mk_surjective ρ N (y : Coinvariants ρ N)
    obtain ⟨s, hs⟩ := h.exists_pow_lower_fixed ρ hρ v
    have hgs : ((gM ^ s : M) : G) = g ^ s := by simp [gM]
    -- The Levi factor of `K` acts through the fixed vector `y`.
    have hlevi : ∀ m ∈ K.toSubgroup ⊓ M,
        mk ρ N (ρ m (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
      intro m hm
      have hm' := h.levi_pow s m hm
      have hyfix := y.property ⟨⟨_, hm'.2⟩, hm'.1⟩
      calc
        mk ρ N (ρ m (ρ (g ^ s) v)) =
            mk ρ N (ρ (gM ^ s : M) (ρ ((g ^ s)⁻¹ * m * g ^ s) v)) := by
          rw [hgs]
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 2
          group
        _ = action ρ N M hMN (gM ^ s)
              (action ρ N M hMN ⟨_, hm'.2⟩ (mk ρ N v)) := by
          rw [action_mk, action_mk]
        _ = _ := by
          rw [hv]
          exact congrArg _ hyfix
    -- Every `K`-translate of `ρ(g^s) v` has quotient `g^s y`.
    have hconst : ∀ k : K,
        mk ρ N (ρ k.val (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
      intro k
      obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
      have heq : k.val = u⁻¹ * (m⁻¹ * l⁻¹) := by
        rw [← inv_inv k.val, hprod]
        group
      rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        hs _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
      rw [mk_apply_subgroup ρ N ⟨u⁻¹, N.inv_mem hu.2⟩]
      exact hlevi _ ((K.toSubgroup ⊓ M).inv_mem hm)
    apply hpow s
    obtain ⟨t, ht⟩ := hsplit ⟨Compact.averageMap ρ hρ K hK (ρ (g ^ s) v),
      Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩
    exact ⟨t, ht.trans (map_averageMap_of_forall_eq ρ hρ K hK (mk ρ N) _ _ hconst)⟩

include hρ hK in
/-- Finite dimensionality of `K`-fixed vectors gives finite dimensionality of the
`K ∩ M`-fixed coinvariants. -/
theorem finiteDimensional_fixedVectors_action_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    FiniteDimensional ℂ (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :=
  Module.Finite.of_surjective (stableImageJacquetMap ρ hρ K hK g N M hMN)
    (stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin).2

include hρ hK in
/-- Weak Jacquet lemma: with finite-dimensional `K`-fixed vectors, the actual
quotient map sends `K`-fixed vectors onto the `K ∩ M`-fixed coinvariants. -/
theorem fixedJacquetMap_surjective_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
  intro y
  obtain ⟨t, ht⟩ := (stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin).2 y
  exact ⟨t, ht⟩

end Contraction

/-- Jacquet restriction preserves admissibility when compact open subgroups with
abstract Iwahori factorization and contraction have arbitrarily small Levi parts. -/
theorem isAdmissible_action_of_iwahoriContraction (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hbasis : HasIwahoriContractionBasis N M Nbar) :
    IsAdmissible (action ρ N M hMN) := by
  refine ⟨isSmooth_action ρ N M hMN hρ.1, fun L => ?_⟩
  obtain ⟨K, hK, hKL, g, h⟩ := hbasis L
  have hfin := finiteDimensional_fixedVectors_action_of_iwahoriContraction ρ hρ.1 hK h hMN
    (hρ.2 K)
  have hle : fixedVectors (action ρ N M hMN) L.toSubgroup ≤
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) := by
    intro x hx k
    exact hx ⟨k.val, hKL k.property⟩
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end Abstract

end Langlands.Jacquet
