import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.StableCompressionPower
import Langlands.Representation.Compact.OrbitMeanTranslation

/-!
# The stable compression image as an averaged fixed space

The image of the `b`-th compression power is the `K`-average of the
vectors fixed by `g^b (K ∩ Nbar) g^-b`. Stationarity then identifies this
averaged space with the stable image, as in Renard VI.9.1, Remark 2.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The conjugate of the lower factor used in the `b`-th compression power. -/
def expandedLowerSubgroup (K : OpenSubgroup G) (Nbar : Subgroup G)
    (g : G) (b : ℕ) : Subgroup G :=
  (K.toSubgroup ⊓ Nbar).map (MulAut.conj (g ^ b)).toMonoidHom

theorem expandedLowerSubgroup_isCompact (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (Nbar : Subgroup G)
    (hNbar : IsClosed (Nbar : Set G)) (g : G) (b : ℕ) :
    IsCompact (expandedLowerSubgroup K Nbar g b : Set G) := by
  exact (hK.inter_right hNbar).image
    ((continuous_const.mul continuous_id).mul continuous_const)

omit [IsTopologicalGroup G] in
theorem expandedLowerSubgroup_le (K : OpenSubgroup G) (Nbar : Subgroup G)
    (g : G) (hg : g ∈ Subgroup.normalizer Nbar) (b : ℕ) :
    expandedLowerSubgroup K Nbar g b ≤ Nbar := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (pow_mem hg b) x).mp hx.2

private theorem averageMap_apply_mem (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k v) = Compact.averageMap ρ hρ K hK v :=
  Compact.orbitMean_apply (ρ.comp K.toSubgroup.subtype) ⟨k, hk⟩ v

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
variable {N M Nbar : Subgroup G} {g : G}

omit [IsTopologicalGroup G] in
/-- Translating a `K`-fixed vector by `g^b` makes it fixed by the expanded
lower factor. -/
theorem translate_mem_expandedLower_fixed (b : ℕ)
    (v : fixedVectors ρ K.toSubgroup) :
    ρ (g ^ b) (v : V) ∈ fixedVectors ρ (expandedLowerSubgroup K Nbar g b) := by
  rintro ⟨_, x, hx, rfl⟩
  change ρ (g ^ b * x * (g ^ b)⁻¹) (ρ (g ^ b) (v : V)) = _
  calc
    _ = ρ (g ^ b) (ρ x (v : V)) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 2
      group
    _ = _ := congrArg (ρ (g ^ b)) (v.property ⟨x, hx.1⟩)

private theorem averageMap_translate_averageMap_of_expandedLower_fixed
    (h : IsIwahoriContraction K N M Nbar g)
    (hcentral : ∀ m ∈ M, m * g = g * m) (b : ℕ)
    (v : V) (hv : v ∈ fixedVectors ρ (expandedLowerSubgroup K Nbar g b)) :
    Compact.averageMap ρ hρ K hK
        (ρ (g ^ b) (Compact.averageMap ρ hρ K hK (ρ (g ^ b)⁻¹ v))) =
      Compact.averageMap ρ hρ K hK v := by
  apply map_averageMap_of_forall_eq ρ hρ K hK
    ((Compact.averageMap ρ hρ K hK).comp (ρ (g ^ b))) (ρ (g ^ b)⁻¹ v)
  intro k
  obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
  have heq : k.val = u⁻¹ * m⁻¹ * l⁻¹ := by
    rw [← inv_inv k.val, hprod]
    group
  have hlfix : ρ l⁻¹ (ρ (g ^ b)⁻¹ v) = ρ (g ^ b)⁻¹ v := by
    have hf := hv ⟨g ^ b * l⁻¹ * (g ^ b)⁻¹,
      ⟨l⁻¹, (K.toSubgroup ⊓ Nbar).inv_mem hl, rfl⟩⟩
    calc
      _ = ρ (g ^ b)⁻¹ (ρ (g ^ b * l⁻¹ * (g ^ b)⁻¹) v) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 2
        group
      _ = _ := congrArg (ρ (g ^ b)⁻¹) hf
  have hmcomm : m⁻¹ * g ^ b = g ^ b * m⁻¹ :=
    (Commute.pow_right (hcentral m⁻¹ (M.inv_mem hm.2)) b).eq
  have hmid : g ^ b * m⁻¹ * (g ^ b)⁻¹ ∈ K := by
    rw [← hmcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact K.inv_mem hm.1
  have hup : g ^ b * u⁻¹ * (g ^ b)⁻¹ ∈ K :=
    (h.upper_pow b _ ((K.toSubgroup ⊓ N).inv_mem hu)).1
  change Compact.averageMap ρ hρ K hK
    (ρ (g ^ b) (ρ k.val (ρ (g ^ b)⁻¹ v))) = _
  rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hlfix]
  calc
    _ = Compact.averageMap ρ hρ K hK
        (ρ (g ^ b * u⁻¹ * (g ^ b)⁻¹)
          (ρ (g ^ b * m⁻¹ * (g ^ b)⁻¹) v)) := by
      congr 1
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 2
      group
    _ = _ := by
      rw [averageMap_apply_mem ρ hρ K hK _ hup,
        averageMap_apply_mem ρ hρ K hK _ hmid]

/-- The actual compression-power range is the average of the fixed vectors
of the expanded lower factor. This identity does not assume stationarity. -/
theorem compressionRange_eq_average_expandedLower_fixed
    (h : IsIwahoriContraction K N M Nbar g)
    (hcentral : ∀ m ∈ M, m * g = g * m) (b : ℕ) :
    (LinearMap.range (compressedAction ρ hρ K hK g ^ b)).map
        (fixedVectors ρ K.toSubgroup).subtype =
      (fixedVectors ρ (expandedLowerSubgroup K Nbar g b)).map
        (Compact.averageMap ρ hρ K hK) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨ρ (g ^ b) (v : V), translate_mem_expandedLower_fixed ρ b v, ?_⟩
    rw [← h.compressedAction_pow ρ hρ hK b]
    rfl
  · rintro _ ⟨v, hv, rfl⟩
    let w : fixedVectors ρ K.toSubgroup :=
      ⟨Compact.averageMap ρ hρ K hK (ρ (g ^ b)⁻¹ v),
        Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩
    refine ⟨(compressedAction ρ hρ K hK g ^ b) w,
      LinearMap.mem_range_self _ w, ?_⟩
    rw [← h.compressedAction_pow ρ hρ hK b]
    exact averageMap_translate_averageMap_of_expandedLower_fixed ρ hρ hK h hcentral b v hv

/-- At a stationary exponent the stable image is an averaged compact-fixed
space. The stationarity hypothesis is explicit. -/
theorem stableImage_eq_average_expandedLower_fixed
    (h : IsIwahoriContraction K N M Nbar g)
    (hcentral : ∀ m ∈ M, m * g = g * m) (b : ℕ)
    (hb : stableImage ρ hρ K hK g =
      LinearMap.range (compressedAction ρ hρ K hK g ^ b)) :
    (stableImage ρ hρ K hK g).map (fixedVectors ρ K.toSubgroup).subtype =
      (fixedVectors ρ (expandedLowerSubgroup K Nbar g b)).map
        (Compact.averageMap ρ hρ K hK) := by
  rw [hb]
  exact compressionRange_eq_average_expandedLower_fixed ρ hρ hK h hcentral b

/-- A stationary compression has the averaged-image input used in the
fixed-completion comparison, for its actual lower subgroup. -/
theorem exists_compact_average_fixed_le_stableImage
    (h : IsIwahoriContraction K N M Nbar g)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (hNbar : IsClosed (Nbar : Set G)) (hg : g ∈ Subgroup.normalizer Nbar)
    (hstationary : ∃ b : ℕ, stableImage ρ hρ K hK g =
      LinearMap.range (compressedAction ρ hρ K hK g ^ b)) :
    ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ Nbar ∧
      (fixedVectors ρ C).map (Compact.averageMap ρ hρ K hK) ≤
        (stableImage ρ hρ K hK g).map (fixedVectors ρ K.toSubgroup).subtype := by
  obtain ⟨b, hb⟩ := hstationary
  refine ⟨expandedLowerSubgroup K Nbar g b,
    expandedLowerSubgroup_isCompact K hK Nbar hNbar g b,
    expandedLowerSubgroup_le K Nbar g hg b, ?_⟩
  exact (stableImage_eq_average_expandedLower_fixed ρ hρ hK h hcentral b hb).symm.le

end Langlands.Jacquet
