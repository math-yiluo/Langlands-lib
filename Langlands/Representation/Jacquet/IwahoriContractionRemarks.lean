import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Representation.Hecke.UniformFixedLevelBounds
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Compact.OrbitMeanTranslation
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Renard VI.9.1, Remarks 1 and 2, for abstract Iwahori contractions -/

noncomputable section

namespace Langlands.Compact

universe uH uH' uV

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Orbit means depend only on the orbit set. -/
theorem orbitMean_eq_of_orbit_eq {H : Type uH} {H' : Type uH'} [Group H] [Group H']
    (ρ : Representation ℂ H V) (σ : Representation ℂ H' V) {v w : V}
    (h : orbit ρ v = orbit σ w) : orbitMean ρ v = orbitMean σ w := by
  unfold orbitMean
  rw [h]

/-- If an orbit is the image of a finite orbit under an injective linear map, its
orbit mean is the image of the orbit mean. -/
theorem orbitMean_eq_apply_of_orbit_eq_image {H : Type uH} {H' : Type uH'} [Group H]
    [Group H'] (ρ : Representation ℂ H V) (σ : Representation ℂ H' V) (f : V →ₗ[ℂ] V)
    (hf : Function.Injective f) {v w : V} [Finite (orbit ρ v)]
    (h : orbit σ w = f '' orbit ρ v) : orbitMean σ w = f (orbitMean ρ v) := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  unfold orbitMean
  rw [h, Nat.card_image_of_injective hf, map_smul]
  congr 1
  let e : orbit ρ v ≃ (f '' orbit ρ v) := Equiv.Set.image f _ hf
  let := Fintype.ofEquiv _ e
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  exact (Fintype.sum_equiv e (fun x => f x.val) (fun y => y.val) (fun _ => rfl)).symm

end Langlands.Compact

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

section Averages

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- If translation by `a` carries every `K`-translate of `y` to a `K`-translate of
`ρ a y`, then averaging over `K` after `a` does not see a prior average of `y`. -/
theorem averageMap_apply_averageMap (a : G) (y : V)
    (hsub : ∀ k ∈ K, ∃ k' ∈ K, ρ a (ρ k y) = ρ k' (ρ a y)) :
    Compact.averageMap ρ hρ K hK (ρ a (Compact.averageMap ρ hρ K hK y)) =
      Compact.averageMap ρ hρ K hK (ρ a y) := by
  classical
  let τ := ρ.comp K.toSubgroup.subtype
  let := Compact.finite_orbit_of_smooth ρ hρ K hK y
  let := Fintype.ofFinite (Compact.orbit τ y)
  have hav : Compact.averageMap ρ hρ K hK y = Compact.orbitMean τ y := rfl
  have hterm : ∀ x : Compact.orbit τ y,
      Compact.averageMap ρ hρ K hK (ρ a x.val) = Compact.averageMap ρ hρ K hK (ρ a y) := by
    rintro ⟨x, ⟨k, rfl⟩⟩
    obtain ⟨k', hk', hkk⟩ := hsub k.val k.property
    change Compact.averageMap ρ hρ K hK (ρ a (ρ k.val y)) = _
    rw [hkk, averageMap_apply_of_mem ρ hρ K hK hk']
  rw [hav, Compact.orbitMean_eq_finiteMean]
  unfold Compact.finiteMean
  rw [map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

end Averages

/-- The open subgroup `a⁻¹ K a ∩ H` of a subgroup `H`, as the preimage of `K` under
conjugation by `a`. -/
def conjugateOpenSubgroup (K : OpenSubgroup G) (H : Subgroup G) (a : G) : OpenSubgroup H :=
  K.comap ((MulAut.conj a).toMonoidHom.comp H.subtype)
    (show Continuous fun x : H => a * (x : G) * a⁻¹ from
      (continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem mem_conjugateOpenSubgroup {K : OpenSubgroup G} {H : Subgroup G} {a : G} {x : H} :
    x ∈ conjugateOpenSubgroup K H a ↔ a * (x : G) * a⁻¹ ∈ K :=
  Iff.rfl

/-- For a closed subgroup `H` and a compact `K`, the subgroup `a⁻¹ K a ∩ H` is compact. -/
theorem isCompact_conjugateOpenSubgroup {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (a : G) :
    IsCompact ((conjugateOpenSubgroup K H a : OpenSubgroup H) : Set H) := by
  have h1 : IsCompact ((fun x : G => a * x * a⁻¹) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isCompact_preimage.mpr hK
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1

namespace IsIwahoriContraction

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g g' : G}

omit [IsTopologicalGroup G] in
/-- An Iwahori contraction commutes with every element central in the Levi. -/
theorem commute_of_central (h : IsIwahoriContraction K N M Nbar g)
    (hcent' : ∀ m ∈ M, m * g' = g' * m) : Commute g g' :=
  hcent' g h.mem_levi

omit [IsTopologicalGroup G] in
/-- The product of two Iwahori contractions, the second central in the Levi, is an
Iwahori contraction. -/
theorem mul (h : IsIwahoriContraction K N M Nbar g) (h' : IsIwahoriContraction K N M Nbar g')
    (hcent' : ∀ m ∈ M, m * g' = g' * m) (hMN : M ≤ Subgroup.normalizer N) :
    IsIwahoriContraction K N M Nbar (g * g') where
  mem_levi := M.mul_mem h.mem_levi h'.mem_levi
  factor := h.factor
  upper u hu := by
    have e : g * g' * u * (g * g')⁻¹ = g * (g' * u * g'⁻¹) * g⁻¹ := by group
    rw [e]
    exact h.upper _ (h'.upper u hu)
  levi m hm := by
    have e : (g * g')⁻¹ * m * (g * g') = g'⁻¹ * (g⁻¹ * m * g) * g' := by group
    rw [e]
    exact h'.levi _ (h.levi m hm)
  lower l hl := by
    have e : (g * g')⁻¹ * l * (g * g') = g'⁻¹ * (g⁻¹ * l * g) * g' := by group
    rw [e]
    exact h'.lower _ (h.lower l hl)
  exhaust x hx := by
    obtain ⟨r, hr⟩ := h'.exhaust x hx
    have hgN : g' ^ r ∈ Subgroup.normalizer N := pow_mem (hMN h'.mem_levi) r
    have hN : g' ^ r * x * (g' ^ r)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    refine ⟨r, ?_⟩
    rw [(h.commute_of_central hcent').mul_pow]
    have e : g ^ r * g' ^ r * x * (g ^ r * g' ^ r)⁻¹ =
        g ^ r * (g' ^ r * x * (g' ^ r)⁻¹) * (g ^ r)⁻¹ := by group
    rw [e]
    exact (h.upper_pow r _ ⟨hr, hN⟩).1
  contract L := by
    obtain ⟨s, hs⟩ := h'.contract L
    refine ⟨s, fun l hl => ?_⟩
    rw [(h.commute_of_central hcent').mul_pow]
    have e : (g ^ s * g' ^ s)⁻¹ * l * (g ^ s * g' ^ s) =
        (g' ^ s)⁻¹ * ((g ^ s)⁻¹ * l * g ^ s) * g' ^ s := by group
    rw [e]
    exact hs _ (h.lower_pow s l hl)

end IsIwahoriContraction

section RemarkOne

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g g' : G}

/-- Compression by `g ^ r * g' ^ r` is the composite of the two compressions. -/
theorem compressedAction_pow_mul_pow (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction K N M Nbar g') (r : ℕ) :
    compressedAction ρ hρ K hK (g ^ r * g' ^ r) =
      compressedAction ρ hρ K hK g ^ r * compressedAction ρ hρ K hK g' ^ r := by
  rw [compressedAction_mul_of_factor ρ hρ K hK N M Nbar h.factor (g ^ r) (g' ^ r)
    (fun u hu => (h.upper_pow r u hu).1) (fun l hl => (h'.lower_pow r l hl).1)
    (fun m hm => (h'.levi_pow r m hm).1), h.compressedAction_pow ρ hρ hK r,
    h'.compressedAction_pow ρ hρ hK r]

/-- The stable image of the product is contained in that of the first factor. -/
theorem stableImage_mul_le (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction K N M Nbar g') (hcent' : ∀ m ∈ M, m * g' = g' * m)
    (hMN : M ≤ Subgroup.normalizer N) :
    stableImage ρ hρ K hK (g * g') ≤ stableImage ρ hρ K hK g := by
  intro v hv
  rw [mem_stableImage] at hv ⊢
  intro r
  obtain ⟨w, hw⟩ := hv r
  refine ⟨(compressedAction ρ hρ K hK g' ^ r) w, ?_⟩
  rw [← (h.mul h' hcent' hMN).compressedAction_pow ρ hρ hK r,
    (h.commute_of_central hcent').mul_pow, compressedAction_pow_mul_pow ρ hρ hK h h' r] at hw
  rw [← hw, Module.End.mul_apply]

/-- If two subspaces are complements of the same subspace and one contains the other,
they are equal. -/
theorem eq_of_isCompl_of_le {α : Type*} [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {k s t : α} (hs : IsCompl k s) (ht : IsCompl k t) (hle : t ≤ s) : t = s :=
  eq_of_le_of_inf_le_of_sup_le hle
    (by rw [inf_comm, hs.inf_eq_bot]; exact bot_le)
    (by rw [sup_comm t, ht.sup_eq_top]; exact le_top)

/-- Renard VI.9.1, Remark 1, for abstract Iwahori contractions: the kernel supremum
does not depend on the contracting element. -/
theorem powerKernelSup_eq_of_iwahoriContraction (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction K N M Nbar g') (hMN : M ≤ Subgroup.normalizer N) :
    powerKernelSup ρ hρ K hK g' = powerKernelSup ρ hρ K hK g := by
  rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN,
    powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h' hMN]

/-- Renard VI.9.1, Remark 1, for abstract Iwahori contractions: when the compressions of
`g`, `g'` and `g * g'` split, the stable images of `g` and `g'` agree. -/
theorem stableImage_eq_of_iwahoriContraction (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction K N M Nbar g') (hcent : ∀ m ∈ M, m * g = g * m)
    (hcent' : ∀ m ∈ M, m * g' = g' * m) (hMN : M ≤ Subgroup.normalizer N)
    (hs : CompactCompressionSplits ρ hρ K hK g) (hs' : CompactCompressionSplits ρ hρ K hK g')
    (hss : CompactCompressionSplits ρ hρ K hK (g * g')) :
    stableImage ρ hρ K hK g' = stableImage ρ hρ K hK g := by
  have hgg := h.mul h' hcent' hMN
  have hgg' := h'.mul h hcent hMN
  have hk : powerKernelSup ρ hρ K hK (g * g') = powerKernelSup ρ hρ K hK g :=
    powerKernelSup_eq_of_iwahoriContraction ρ hρ hK h hgg hMN
  have hk' : powerKernelSup ρ hρ K hK (g * g') = powerKernelSup ρ hρ K hK g' :=
    powerKernelSup_eq_of_iwahoriContraction ρ hρ hK h' hgg hMN
  unfold CompactCompressionSplits at hs hs' hss
  have e1 : stableImage ρ hρ K hK (g * g') = stableImage ρ hρ K hK g :=
    eq_of_isCompl_of_le hs (hk ▸ hss) (stableImage_mul_le ρ hρ hK h h' hcent' hMN)
  have hcomm : g * g' = g' * g := (h.commute_of_central hcent').eq
  have e2 : stableImage ρ hρ K hK (g * g') = stableImage ρ hρ K hK g' := by
    rw [hcomm]
    exact eq_of_isCompl_of_le hs' (hk' ▸ hcomm ▸ hss)
      (stableImage_mul_le ρ hρ hK h' h hcent hMN)
  rw [← e1, e2]

end RemarkOne

section RemarkTwo

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If `b⁻¹ k b` fixes `v`, then `k` fixes `ρ b v`. -/
theorem apply_apply_eq_of_conj_mem {H : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H) (b k : G) (hk : b⁻¹ * k * b ∈ H) :
    ρ k (ρ b v) = ρ b v := by
  calc
    ρ k (ρ b v) = ρ b (ρ (b⁻¹ * k * b) v) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = ρ b v := congrArg (ρ b) (hv ⟨_, hk⟩)

include hρ hK in
omit [IsTopologicalGroup G] in
/-- Orbits under `K ∩ H` are finite, being contained in orbits under `K`. -/
theorem finite_orbit_inf [IsTopologicalGroup G] (H : Subgroup G) (v : V) :
    Finite (Compact.orbit (ρ.comp (K.toSubgroup ⊓ H).subtype) v) := by
  have := Compact.finite_orbit_of_smooth ρ hρ K hK v
  refine (Set.Finite.subset (Set.toFinite (Compact.orbit (ρ.comp K.toSubgroup.subtype) v))
    ?_).to_subtype
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k.val, k.property.1⟩, rfl⟩

/-- Renard (VI.9.1.5): on `K`-fixed vectors, averaging over `K` after `g ^ s` is
translation by `g ^ s` after averaging over `C_s = {x ∈ N | g ^ s x g ^ (-s) ∈ K}`. -/
theorem averageMap_apply_pow_eq (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hN : IsClosed (N : Set G)) (s : ℕ) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    Compact.averageMap ρ hρ K hK (ρ (g ^ s) v) =
      ρ (g ^ s) (Compact.averageMap (ρ.comp N.subtype)
        (isSmooth_comp N.subtype continuous_subtype_val hρ)
        (conjugateOpenSubgroup K N (g ^ s)) (isCompact_conjugateOpenSubgroup hK hN (g ^ s)) v) := by
  have hgN : g ^ s ∈ Subgroup.normalizer N := pow_mem (hMN h.mem_levi) s
  have hgN' : (g ^ s)⁻¹ ∈ Subgroup.normalizer N := inv_mem hgN
  let C := conjugateOpenSubgroup K N (g ^ s)
  have := Compact.finite_orbit_of_smooth (ρ.comp N.subtype)
    (isSmooth_comp N.subtype continuous_subtype_val hρ) C
    (isCompact_conjugateOpenSubgroup hK hN (g ^ s)) v
  change Compact.orbitMean (ρ.comp K.toSubgroup.subtype) (ρ (g ^ s) v) =
    ρ (g ^ s) (Compact.orbitMean ((ρ.comp N.subtype).comp C.toSubgroup.subtype) v)
  refine Compact.orbitMean_eq_apply_of_orbit_eq_image _ _ (ρ (g ^ s))
    (Representation.apply_bijective ρ (g ^ s)).injective ?_
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨u, hu, hk⟩ := exists_upper_translate ρ K N M Nbar h.factor (g ^ s)
      (fun l hl => (h.lower_pow s l hl).1) (fun m hm => (h.levi_pow s m hm).1) v hv k.val
      k.property
    have hy : (g ^ s)⁻¹ * u * (g ^ s)⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hgN' u).mp hu.2
    rw [inv_inv] at hy
    have hyC : (⟨_, hy⟩ : N) ∈ C := by
      rw [mem_conjugateOpenSubgroup]
      have e : g ^ s * ((g ^ s)⁻¹ * u * g ^ s) * (g ^ s)⁻¹ = u := by group
      rw [e]
      exact hu.1
    refine ⟨ρ ((g ^ s)⁻¹ * u * g ^ s) v, ⟨⟨_, hyC⟩, rfl⟩, ?_⟩
    change ρ (g ^ s) (ρ ((g ^ s)⁻¹ * u * g ^ s) v) = ρ k.val (ρ (g ^ s) v)
    rw [hk]
    simp only [← Module.End.mul_apply, ← map_mul ρ]
    congr 1
    group
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine ⟨⟨g ^ s * c.val.val * (g ^ s)⁻¹, mem_conjugateOpenSubgroup.mp c.property⟩, ?_⟩
    change ρ (g ^ s * c.val.val * (g ^ s)⁻¹) (ρ (g ^ s) v) = ρ (g ^ s) (ρ c.val.val v)
    simp only [← Module.End.mul_apply, ← map_mul ρ]
    congr 1
    group

/-- Renard VI.9.1, Remark 2, kernel half, for every power: the kernel of the `s`-th power of
the compression is the kernel of averaging over `C_s = {x ∈ N | g ^ s x g ^ (-s) ∈ K}`. -/
theorem ker_compressedAction_pow_eq (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hN : IsClosed (N : Set G)) (s : ℕ) :
    LinearMap.ker (compressedAction ρ hρ K hK g ^ s) =
      LinearMap.ker ((Compact.averageMap (ρ.comp N.subtype)
        (isSmooth_comp N.subtype continuous_subtype_val hρ)
        (conjugateOpenSubgroup K N (g ^ s)) (isCompact_conjugateOpenSubgroup hK hN (g ^ s))).comp
          (fixedVectors ρ K.toSubgroup).subtype) := by
  rw [← h.compressedAction_pow ρ hρ hK s]
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
    ← Submodule.coe_eq_zero, compressedAction_apply,
    averageMap_apply_pow_eq ρ hρ hK h hMN hN s v.val v.property]
  exact map_eq_zero_iff _ (Representation.apply_bijective ρ (g ^ s)).injective

/-- The `C̄_s = {x ∈ Nbar | g ^ (-s) x g ^ s ∈ K}`-orbit of `w` is the translate by `g ^ s`
of the `K ∩ Nbar`-orbit of `ρ (g ^ s)⁻¹ w`. -/
theorem averageMap_lower_eq (h : IsIwahoriContraction K N M Nbar g)
    (hMNbar : M ≤ Subgroup.normalizer Nbar) (hNbar : IsClosed (Nbar : Set G)) (s : ℕ)
    (w : V) :
    Compact.averageMap (ρ.comp Nbar.subtype)
        (isSmooth_comp Nbar.subtype continuous_subtype_val hρ)
        (conjugateOpenSubgroup K Nbar (g ^ s)⁻¹)
        (isCompact_conjugateOpenSubgroup hK hNbar (g ^ s)⁻¹) w =
      ρ (g ^ s) (Compact.orbitMean (ρ.comp (K.toSubgroup ⊓ Nbar).subtype)
        (ρ (g ^ s)⁻¹ w)) := by
  have hgN : g ^ s ∈ Subgroup.normalizer Nbar := pow_mem (hMNbar h.mem_levi) s
  have hgN' : (g ^ s)⁻¹ ∈ Subgroup.normalizer Nbar := inv_mem hgN
  let C := conjugateOpenSubgroup K Nbar (g ^ s)⁻¹
  have := finite_orbit_inf ρ hρ hK Nbar (ρ (g ^ s)⁻¹ w)
  change Compact.orbitMean ((ρ.comp Nbar.subtype).comp C.toSubgroup.subtype) w = _
  refine Compact.orbitMean_eq_apply_of_orbit_eq_image _ _ (ρ (g ^ s))
    (Representation.apply_bijective ρ (g ^ s)).injective ?_
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    have hcK : (g ^ s)⁻¹ * c.val.val * (g ^ s)⁻¹⁻¹ ∈ K := mem_conjugateOpenSubgroup.mp c.property
    have hcN : (g ^ s)⁻¹ * c.val.val * (g ^ s)⁻¹⁻¹ ∈ Nbar :=
      (Subgroup.mem_normalizer_iff.mp hgN' c.val.val).mp c.val.property
    rw [inv_inv] at hcK hcN
    refine ⟨ρ ((g ^ s)⁻¹ * c.val.val * g ^ s) (ρ (g ^ s)⁻¹ w), ⟨⟨_, hcK, hcN⟩, rfl⟩, ?_⟩
    change ρ (g ^ s) (ρ ((g ^ s)⁻¹ * c.val.val * g ^ s) (ρ (g ^ s)⁻¹ w)) = ρ c.val.val w
    simp only [← Module.End.mul_apply, ← map_mul ρ]
    congr 1
    group
  · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
    have hlN : g ^ s * l.val * (g ^ s)⁻¹ ∈ Nbar :=
      (Subgroup.mem_normalizer_iff.mp hgN l.val).mp l.property.2
    have hlC : (⟨_, hlN⟩ : Nbar) ∈ C := by
      rw [mem_conjugateOpenSubgroup]
      have e : (g ^ s)⁻¹ * (g ^ s * l.val * (g ^ s)⁻¹) * (g ^ s)⁻¹⁻¹ = l.val := by group
      rw [e]
      exact l.property.1
    refine ⟨⟨_, hlC⟩, ?_⟩
    change ρ (g ^ s * l.val * (g ^ s)⁻¹) w = ρ (g ^ s) (ρ l.val (ρ (g ^ s)⁻¹ w))
    simp only [← Module.End.mul_apply, ← map_mul ρ]
    congr 1
    group

/-- Renard VI.9.1, Remark 2, range half, for every power: the range of the `s`-th power of
the compression, as vectors of `V`, is the image of averaging over `K` after averaging
over `C̄_s = {x ∈ Nbar | g ^ (-s) x g ^ s ∈ K}`. -/
theorem range_compressedAction_pow_eq (h : IsIwahoriContraction K N M Nbar g)
    (hcent : ∀ m ∈ M, m * g = g * m) (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hNbar : IsClosed (Nbar : Set G)) (s : ℕ) :
    (LinearMap.range (compressedAction ρ hρ K hK g ^ s)).map
        (fixedVectors ρ K.toSubgroup).subtype =
      LinearMap.range ((Compact.averageMap ρ hρ K hK).comp
        (Compact.averageMap (ρ.comp Nbar.subtype)
          (isSmooth_comp Nbar.subtype continuous_subtype_val hρ)
          (conjugateOpenSubgroup K Nbar (g ^ s)⁻¹)
          (isCompact_conjugateOpenSubgroup hK hNbar (g ^ s)⁻¹))) := by
  rw [← h.compressedAction_pow ρ hρ hK s]
  apply le_antisymm
  · rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨ρ (g ^ s) z.val, ?_⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, compressedAction_apply]
    congr 1
    apply Compact.averageMap_id
    intro c
    have hcK : (g ^ s)⁻¹ * c.val.val * (g ^ s)⁻¹⁻¹ ∈ K := mem_conjugateOpenSubgroup.mp c.property
    rw [inv_inv] at hcK
    exact apply_apply_eq_of_conj_mem ρ z.property (g ^ s) c.val.val hcK
  · rintro x ⟨w, rfl⟩
    let τL := ρ.comp (K.toSubgroup ⊓ Nbar).subtype
    have := finite_orbit_inf ρ hρ hK Nbar (ρ (g ^ s)⁻¹ w)
    set y := Compact.orbitMean τL (ρ (g ^ s)⁻¹ w) with hy
    have hfix : ∀ l ∈ K.toSubgroup ⊓ Nbar, ρ l y = y := fun l hl =>
      Compact.orbitMean_invariant τL (ρ (g ^ s)⁻¹ w) ⟨l, hl⟩
    have hsub : ∀ k ∈ K, ∃ k' ∈ K, ρ (g ^ s) (ρ k y) = ρ k' (ρ (g ^ s) y) := by
      intro k hk
      obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k⁻¹ (K.inv_mem hk)
      have heq : k = u⁻¹ * m⁻¹ * l⁻¹ := by
        rw [← inv_inv k, hprod]
        group
      have hc : m⁻¹ * g ^ s = g ^ s * m⁻¹ := ((Commute.inv_left (hcent m hm.2)).pow_right s).eq
      have hconj : (g ^ s)⁻¹ * m⁻¹ * g ^ s = m⁻¹ := by
        rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
      refine ⟨g ^ s * u⁻¹ * (g ^ s)⁻¹ * m⁻¹,
        K.mul_mem (h.upper_pow s u⁻¹ ((K.toSubgroup ⊓ N).inv_mem hu)).1
          (K.inv_mem hm.1), ?_⟩
      calc
        ρ (g ^ s) (ρ k y) = ρ (g ^ s) (ρ (u⁻¹ * m⁻¹) (ρ l⁻¹ y)) := by
          rw [heq, map_mul ρ (u⁻¹ * m⁻¹), Module.End.mul_apply]
        _ = ρ (g ^ s) (ρ (u⁻¹ * m⁻¹) y) := by
          rw [hfix l⁻¹ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
        _ = ρ (g ^ s * u⁻¹ * (g ^ s)⁻¹ * m⁻¹) (ρ (g ^ s) y) := by
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 1
          rw [show g ^ s * u⁻¹ * (g ^ s)⁻¹ * m⁻¹ * g ^ s =
            g ^ s * u⁻¹ * ((g ^ s)⁻¹ * m⁻¹ * g ^ s) by group, hconj]
          group
    have hyK := Compact.averageMap_mem_fixedVectors ρ hρ K hK y
    refine ⟨compressedAction ρ hρ K hK (g ^ s) ⟨_, hyK⟩, ⟨_, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, compressedAction_apply, LinearMap.comp_apply,
      averageMap_lower_eq ρ hρ hK h hMNbar hNbar s w]
    exact averageMap_apply_averageMap ρ hρ K hK (g ^ s) y hsub

end RemarkTwo

section Assembly

/-- If the compression splits and its `c`-th power kills the kernel supremum, then every
power of exponent at least `c` has kernel the kernel supremum and range the stable image. -/
theorem stabilization_of_pow_kill (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hsplit : CompactCompressionSplits ρ hρ K hK g) (c : ℕ)
    (hkill : ∀ v ∈ powerKernelSup ρ hρ K hK g, (compressedAction ρ hρ K hK g ^ c) v = 0) :
    ∀ s : ℕ, c ≤ s →
      stableImage ρ hρ K hK g = LinearMap.range (compressedAction ρ hρ K hK g ^ s) ∧
        powerKernelSup ρ hρ K hK g = LinearMap.ker (compressedAction ρ hρ K hK g ^ s) := by
  intro s hs
  set A := compressedAction ρ hρ K hK g
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hpowS : ∀ r : ℕ, ∀ v ∈ stableImage ρ hρ K hK g, (A ^ r) v ∈ stableImage ρ hρ K hK g := by
    intro r
    induction r with
    | zero => intro v hv; simpa using hv
    | succ r ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact compressedAction_mem_stableImage ρ hρ K hK g _ (ih v hv)
  have hkill' : ∀ v ∈ powerKernelSup ρ hρ K hK g, (A ^ (c + t)) v = 0 := by
    intro v hv
    rw [add_comm, pow_add, Module.End.mul_apply, hkill v hv, map_zero]
  refine ⟨le_antisymm (iInf_le _ (c + t)) ?_, le_antisymm ?_
    (le_iSup (fun r : ℕ => LinearMap.ker (A ^ r)) (c + t))⟩
  · rintro x ⟨y, rfl⟩
    have hy : y ∈ powerKernelSup ρ hρ K hK g ⊔ stableImage ρ hρ K hK g := by
      rw [hsplit.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, hkill' y₀ hy₀, zero_add]
    exact hpowS _ y₁ hy₁
  · intro v hv
    exact hkill' v hv

variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}

/-- Renard VI.9.1, Remarks 1 and 2, for abstract closed subgroups: from the uniform
stabilization of the Proposition for every `M`-central Iwahori contraction, the kernel
supremum and the stable image do not depend on the contraction, and are the kernel of
`e_C` on `K`-fixed vectors and the image of `e_K ∘ e_{C̄}` for fixed compact open
`C ≤ N` and `C̄ ≤ Nbar`. -/
theorem remarks_of_uniformStabilization
    (hN : IsClosed (N : Set G)) (hNbar : IsClosed (Nbar : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hU : ∀ g' : G, (∀ m ∈ M, m * g' = g' * m) → IsIwahoriContraction K N M Nbar g' →
      ∃ b : ℕ, ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
        (σ : Representation ℂ G W) (hσ : IsSmooth σ),
        (∀ s : ℕ, b ≤ s →
          stableImage σ hσ K hK g' = LinearMap.range (compressedAction σ hσ K hK g' ^ s) ∧
            powerKernelSup σ hσ K hK g' = LinearMap.ker (compressedAction σ hσ K hK g' ^ s)) ∧
          CompactCompressionSplits σ hσ K hK g')
    (hcent : ∀ m ∈ M, m * g = g * m) (h : IsIwahoriContraction K N M Nbar g) :
    (∀ g' : G, (∀ m ∈ M, m * g' = g' * m) → IsIwahoriContraction K N M Nbar g' →
        ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ G W) (hσ : IsSmooth σ),
          powerKernelSup σ hσ K hK g' = powerKernelSup σ hσ K hK g ∧
            stableImage σ hσ K hK g' = stableImage σ hσ K hK g) ∧
      ∃ (C : OpenSubgroup N) (hC : IsCompact (C : Set N))
        (Cbar : OpenSubgroup Nbar) (hCbar : IsCompact (Cbar : Set Nbar)),
        ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ G W) (hσ : IsSmooth σ),
          let eC : W →ₗ[ℂ] W := Compact.averageMap (σ.comp N.subtype)
            (isSmooth_comp N.subtype continuous_subtype_val hσ) C hC
          let eCbar : W →ₗ[ℂ] W := Compact.averageMap (σ.comp Nbar.subtype)
            (isSmooth_comp Nbar.subtype continuous_subtype_val hσ) Cbar hCbar
          powerKernelSup σ hσ K hK g =
              LinearMap.ker (eC.comp (fixedVectors σ K.toSubgroup).subtype) ∧
            (stableImage σ hσ K hK g).map (fixedVectors σ K.toSubgroup).subtype =
              LinearMap.range ((Compact.averageMap σ hσ K hK).comp eCbar) := by
  refine ⟨fun g' hcent' h' W _ _ σ hσ => ?_, ?_⟩
  · have hcgg : ∀ m ∈ M, m * (g * g') = g * g' * m := fun m hm => by
      rw [← mul_assoc, hcent m hm, mul_assoc, hcent' m hm, ← mul_assoc]
    obtain ⟨b, hb⟩ := hU g hcent h
    obtain ⟨b', hb'⟩ := hU g' hcent' h'
    obtain ⟨b'', hb''⟩ := hU (g * g') hcgg (h.mul h' hcent' hMN)
    exact ⟨powerKernelSup_eq_of_iwahoriContraction σ hσ hK h h' hMN,
      stableImage_eq_of_iwahoriContraction σ hσ hK h h' hcent hcent' hMN (hb W σ hσ).2
        (hb' W σ hσ).2 (hb'' W σ hσ).2⟩
  · obtain ⟨b, hb⟩ := hU g hcent h
    refine ⟨conjugateOpenSubgroup K N (g ^ b), isCompact_conjugateOpenSubgroup hK hN (g ^ b),
      conjugateOpenSubgroup K Nbar (g ^ b)⁻¹, isCompact_conjugateOpenSubgroup hK hNbar (g ^ b)⁻¹,
      fun W _ _ σ hσ => ?_⟩
    obtain ⟨hS, hKer⟩ := (hb W σ hσ).1 b le_rfl
    exact ⟨hKer.trans (ker_compressedAction_pow_eq σ hσ hK h hMN hN b),
      (congrArg _ hS).trans (range_compressedAction_pow_eq σ hσ hK h hcent hMNbar hNbar b)⟩

end Assembly

end Langlands.Jacquet
