import Langlands.Representation.Hecke.UniformFixedLevelBounds
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Pi

/-! # Common compact coefficient envelopes from positive orthant charts -/

noncomputable section

namespace Langlands.Jacquet

universe uΔ uG uV uW

variable (Δ : Type uΔ)

/-- The finite natural-coordinate box determined by a common exponent. -/
def orthantBox (d : ℕ) : Set (Δ → ℕ) :=
  {n | ∀ i, n i < d}

theorem finite_orthantBox [Finite Δ] (d : ℕ) : (orthantBox Δ d).Finite :=
  Set.Finite.pi' fun _ => Set.finite_Iio d

variable {Δ} {G : Type uG} [Group G]

/-- Bounded positive translates of the finite residual set of a Cartan chart. -/
def orthantBoxResidual (e : Multiplicative (Δ → ℕ) →* G) (d : ℕ)
    (T : Set G) : Set G :=
  (fun p : (Δ → ℕ) × G => e (.ofAdd p.1) * p.2) '' (orthantBox Δ d ×ˢ T)

theorem finite_orthantBoxResidual [Finite Δ]
    (e : Multiplicative (Δ → ℕ) →* G) (d : ℕ) {T : Set G} (hT : T.Finite) :
    (orthantBoxResidual e d T).Finite :=
  ((finite_orthantBox Δ d).prod hT).image _

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inverse image, followed by inversion in the subgroup, of the central
double cover of the bounded positive chart set. It has no representation input. -/
def orthantSupportEnvelope (H J : Subgroup G)
    (e : Multiplicative (Δ → ℕ) →* G) (d : ℕ) (T : Set G) : Set H :=
  Inv.inv '' ((Subtype.val : H → G) ⁻¹'
    centralDoubleCover J (orthantBoxResidual e d T))

theorem isCompact_orthantSupportEnvelope [Finite Δ]
    (H J : Subgroup G) (hH : IsClosed (H : Set G))
    (hJ : IsCompact (J : Set G)) (hJH : J ≤ H)
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    (e : Multiplicative (Δ → ℕ) →* G) (d : ℕ) {T : Set G} (hT : T.Finite) :
    IsCompact (orthantSupportEnvelope H J e d T) :=
  (isCompact_centralDoubleCover_preimage H J hH hJ hJH hHZ
    (orthantBoxResidual e d T) (finite_orthantBoxResidual e d hT)).image continuous_inv

section Compression

variable [DecidableEq Δ]
  (e : Multiplicative (Δ → ℕ) →* G)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
  (N M Nbar : Δ → Subgroup G)
  (hcon : ∀ i, IsIwahoriContraction K (N i) (M i) (Nbar i)
    (e (.ofAdd (Pi.single i 1))))
  (hMN : ∀ i, M i ≤ Subgroup.normalizer (N i))
  (hupper : ∀ i n, ∀ u ∈ K.toSubgroup ⊓ N i,
    e (.ofAdd n) * u * (e (.ofAdd n))⁻¹ ∈ K)
  (hrel : ∀ i, relations ρ (N i) = ⊤)
  (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
  (d : ℕ) (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)

include hρ hK hcon hMN hupper hrel hfin hd in
/-- A coordinate at least the common fixed-space bound forces every invariant
linear output to vanish on the entire positive translate. -/
theorem invariant_map_orthant_eq_zero_of_large_coordinate
    (n : Δ → ℕ) (i : Δ) (hi : d ≤ n i)
    (L : V →ₗ[ℂ] W) (hL : ∀ k ∈ K, ∀ w, L (ρ k w) = L w)
    (v : fixedVectors ρ K.toSubgroup) :
    L (ρ (e (.ofAdd n)) v.val) = 0 := by
  let m : Δ → ℕ := n - Pi.single i d
  have hsplit : n = m + Pi.single i d := by
    ext j
    by_cases hj : j = i
    · subst j
      simpa [m] using (Nat.sub_add_cancel hi).symm
    · simp [m, hj]
  have hsingle : (Pi.single i d : Δ → ℕ) = d • Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have he : e (.ofAdd n) = e (.ofAdd m) * e (.ofAdd (Pi.single i 1)) ^ d := by
    rw [hsplit, ofAdd_add, map_mul, hsingle, ofAdd_nsmul, map_pow]
  rw [he]
  exact invariant_map_mul_pow_eq_zero_of_relations_eq_top ρ hρ hK
    (hcon i) (hMN i) (hrel i) hfin d hd (e (.ofAdd m)) (hupper i m) L hL v

include hρ hK hcon hMN hupper hrel hfin hd in
/-- Nonzero invariant outputs restrict every positive coordinate to the same
finite box, including the empty-label and zero-exponent cases. -/
theorem mem_orthantBox_of_invariant_map_ne_zero
    (n : Δ → ℕ) (L : V →ₗ[ℂ] W)
    (hL : ∀ k ∈ K, ∀ w, L (ρ k w) = L w)
    (v : fixedVectors ρ K.toSubgroup) (hne : L (ρ (e (.ofAdd n)) v.val) ≠ 0) :
    n ∈ orthantBox Δ d := by
  intro i
  by_contra hi
  exact hne (invariant_map_orthant_eq_zero_of_large_coordinate e ρ hρ hK
    N M Nbar hcon hMN hupper hrel hfin d hd n i (Nat.le_of_not_gt hi) L hL v)

end Compression

section Support

variable [DecidableEq Δ]
  (H J U : Subgroup G)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (e : Multiplicative (Δ → ℕ) →* G) (T : Set G)
  (hcharts : ∀ g : G, ∃ n : Δ → ℕ, ∃ k₁ ∈ J, ∃ t ∈ T, ∃ k₂ ∈ J,
    ∃ z ∈ Subgroup.center G, g = k₁ * e (.ofAdd n) * t * k₂ * z)
  (hleft : ∀ k ∈ J, ∀ l ∈ K, k * l * k⁻¹ ∈ U)
  (hright : ∀ t ∈ T, ∀ k ∈ J, ∀ l ∈ K, (t * k)⁻¹ * l * (t * k) ∈ U)
  (N M Nbar : Δ → Subgroup G)
  (hcon : ∀ i, IsIwahoriContraction K (N i) (M i) (Nbar i)
    (e (.ofAdd (Pi.single i 1))))
  (hMN : ∀ i, M i ≤ Subgroup.normalizer (N i))
  (hupper : ∀ i n, ∀ u ∈ K.toSubgroup ⊓ N i,
    e (.ofAdd n) * u * (e (.ofAdd n))⁻¹ ∈ K)
  (d : ℕ)

include hK hcharts hleft hright hcon hMN hupper in
/-- The same explicit envelope contains all inverse coefficients satisfying
the dimension and Jacquet-zero hypotheses at the compression level. The tested
level is `U`; the two conjugation containments transport it through every outer
compact factor and residual chart factor. -/
theorem inverse_coefficient_support_subset_orthantSupportEnvelope
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hrel : ∀ i, relations ρ (N i) = ⊤)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    (v : V) (hv : v ∈ fixedVectors ρ U)
    (ℓ : Module.Dual ℂ V) (hℓ : ∀ k ∈ U, ∀ w, ℓ (ρ k w) = ℓ w) :
    Function.support (fun g : H => ℓ (ρ ((g : G)⁻¹) v)) ⊆
      orthantSupportEnvelope H J e d T := by
  intro g hg
  obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hge⟩ := hcharts ((g : G)⁻¹)
  let L : Module.Dual ℂ V := ℓ.comp (ρ k₁)
  have hL : ∀ l ∈ K, ∀ w, L (ρ l w) = L w := by
    intro l hl w
    change ℓ (ρ k₁ (ρ l w)) = ℓ (ρ k₁ w)
    rw [← Module.End.mul_apply, ← map_mul,
      show k₁ * l = (k₁ * l * k₁⁻¹) * k₁ by group, map_mul,
      Module.End.mul_apply, hℓ _ (hleft k₁ hk₁ l hl)]
  have hvz : ρ z v ∈ fixedVectors ρ U := by
    intro k
    change ρ k.val (ρ z v) = ρ z v
    have hvk : ρ k.val v = v := hv k
    rw [← Module.End.mul_apply, ← map_mul,
      Subgroup.mem_center_iff.mp hz k.val, map_mul, Module.End.mul_apply, hvk]
  let w : fixedVectors ρ K.toSubgroup :=
    ⟨ρ (t * k₂) (ρ z v), by
      intro l
      change ρ l.val (ρ (t * k₂) (ρ z v)) = ρ (t * k₂) (ρ z v)
      have hfixed : ρ ((t * k₂)⁻¹ * l.val * (t * k₂)) (ρ z v) = ρ z v :=
        hvz ⟨_, hright t ht k₂ hk₂ l.val l.property⟩
      rw [← Module.End.mul_apply, ← map_mul,
        show l.val * (t * k₂) =
          (t * k₂) * ((t * k₂)⁻¹ * l.val * (t * k₂)) by group,
        map_mul, Module.End.mul_apply, hfixed]⟩
  have heval : L (ρ (e (.ofAdd n)) w.val) = ℓ (ρ ((g : G)⁻¹) v) := by
    change ℓ (ρ k₁ (ρ (e (.ofAdd n)) (ρ (t * k₂) (ρ z v)))) = _
    rw [hge]
    simp only [map_mul, Module.End.mul_apply]
  have hn : n ∈ orthantBox Δ d :=
    mem_orthantBox_of_invariant_map_ne_zero e ρ hρ hK N M Nbar hcon hMN hupper
      hrel hfin d hd n L hL w (fun h => hg (heval.symm.trans h))
  refine ⟨g⁻¹, ?_, inv_inv g⟩
  change (g : G)⁻¹ ∈ centralDoubleCover J (orthantBoxResidual e d T)
  refine ⟨k₁ * (e (.ofAdd n) * t) * k₂,
    ⟨k₁ * (e (.ofAdd n) * t),
      ⟨k₁, hk₁, e (.ofAdd n) * t, ⟨(n, t), ⟨hn, ht⟩, rfl⟩, rfl⟩,
      k₂, hk₂, rfl⟩, z, hz, ?_⟩
  simpa only [mul_assoc] using hge.symm

end Support

end Langlands.Jacquet
