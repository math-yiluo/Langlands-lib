import Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-!
# Stable evaluation pairing between upper and opposite Jacquet modules

An abstract form of Casselman's canonical pairing. For a compact open subgroup
`K` in a supplied good family, pair a `K`-fixed smooth functional with a vector
in the stable image of compression by `g⁻¹`. Class preservation under nested
averaging makes this independent of `K`, and the compact evaluation duality of
stable images makes the resulting pairing perfect.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uW uL uX

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A fixed vector is fixed by each element of its subgroup. -/
theorem apply_eq_of_mem_fixedVectors (ρ : Representation ℂ G V) {K : Subgroup G} {w : V}
    (hw : w ∈ fixedVectors ρ K) {k : G} (hk : k ∈ K) : ρ k w = w :=
  hw ⟨k, hk⟩

/-- Averaging over `K` is unchanged by first translating by an element of `K`. -/
theorem averageMap_apply_of_mem (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
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

/-- Averaging over a larger subgroup absorbs averaging over a smaller one. -/
theorem averageMap_averageMap_of_le (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K L : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G))
    (hLK : L ≤ K) (v : V) :
    Compact.averageMap ρ hρ K hK (Compact.averageMap ρ hρ L hL v) =
      Compact.averageMap ρ hρ K hK v :=
  map_averageMap_of_forall_eq ρ hρ L hL (Compact.averageMap ρ hρ K hK) v
    (Compact.averageMap ρ hρ K hK v)
    (fun l => averageMap_apply_of_mem ρ hρ K hK (hLK l.property) v)

/-- The conjugate `m K m⁻¹` of an open subgroup. -/
def conjOpenSubgroup (m : G) (K : OpenSubgroup G) : OpenSubgroup G :=
  K.comap (MulAut.conj m⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj m⁻¹)

theorem mem_conjOpenSubgroup (m : G) (K : OpenSubgroup G) (x : G) :
    x ∈ conjOpenSubgroup m K ↔ m⁻¹ * x * m ∈ K := by
  change m⁻¹ * x * m⁻¹⁻¹ ∈ K ↔ _
  rw [inv_inv]

theorem conjOpenSubgroup_mono (m : G) {K L : OpenSubgroup G} (h : K ≤ L) :
    conjOpenSubgroup m K ≤ conjOpenSubgroup m L := by
  intro x hx
  rw [mem_conjOpenSubgroup] at hx ⊢
  exact h hx

theorem conjOpenSubgroup_conj_inv (m : G) (K : OpenSubgroup G) :
    conjOpenSubgroup m⁻¹ (conjOpenSubgroup m K) = K := by
  ext x
  rw [mem_conjOpenSubgroup, mem_conjOpenSubgroup, inv_inv]
  constructor
  · intro hx
    simpa [mul_assoc] using hx
  · intro hx
    simpa [mul_assoc] using hx

theorem isCompact_conjOpenSubgroup (m : G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : IsCompact (conjOpenSubgroup m K : Set G) := by
  have h : (conjOpenSubgroup m K : Set G) = (fun y => m * y * m⁻¹) '' (K : Set G) := by
    ext x
    simp only [SetLike.mem_coe, mem_conjOpenSubgroup, Set.mem_image]
    constructor
    · intro hx
      exact ⟨m⁻¹ * x * m, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  rw [h]
  exact hK.image (IsTopologicalGroup.continuous_conj m)

/-- Translating by `m` carries `K`-fixed vectors to `m K m⁻¹`-fixed vectors. -/
theorem conj_mem_fixedVectors (ρ : Representation ℂ G V) (m : G) (K : OpenSubgroup G)
    {w : V} (hw : w ∈ fixedVectors ρ K.toSubgroup) :
    ρ m w ∈ fixedVectors ρ (conjOpenSubgroup m K).toSubgroup := by
  intro k
  have hk : m⁻¹ * (k : G) * m ∈ K := (mem_conjOpenSubgroup m K k).mp k.property
  have h := hw ⟨_, hk⟩
  change ρ (m⁻¹ * (k : G) * m) w = w at h
  change ρ (k : G) (ρ m w) = ρ m w
  calc ρ (k : G) (ρ m w) = ρ m (ρ (m⁻¹ * (k : G) * m) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ m w := by rw [h]

/-- Averaging over a conjugate subgroup is the conjugated average. -/
theorem averageMap_conj (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (m : G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsCompact (conjOpenSubgroup m K : Set G)) (v : V) :
    Compact.averageMap ρ hρ (conjOpenSubgroup m K) hK' (ρ m v) =
      ρ m (Compact.averageMap ρ hρ K hK v) := by
  let K' := conjOpenSubgroup m K
  let φ : K.toSubgroup →* K'.toSubgroup :=
    { toFun := fun k => ⟨m * (k : G) * m⁻¹, by
        change _ ∈ conjOpenSubgroup m K
        rw [mem_conjOpenSubgroup]
        simp [mul_assoc]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  let τ₁ := ρ.comp K.toSubgroup.subtype
  let τ' := ρ.comp K'.toSubgroup.subtype
  let τ₂ := τ'.comp φ
  have hf : ∀ (k : K.toSubgroup) (w : V), ρ m (τ₁ k w) = τ₂ k (ρ m w) := by
    intro k w
    change ρ m (ρ (k : G) w) = ρ (m * (k : G) * m⁻¹) (ρ m w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have horbit : ∀ w, Compact.orbit τ₂ w = Compact.orbit τ' w := by
    intro w
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨φ k, rfl⟩
    · rintro ⟨k', rfl⟩
      refine ⟨⟨m⁻¹ * (k' : G) * m, (mem_conjOpenSubgroup m K k').mp k'.property⟩, ?_⟩
      change ρ (m * (m⁻¹ * (k' : G) * m) * m⁻¹) w = ρ (k' : G) w
      congr 2
      group
  let := Compact.finite_orbit_of_smooth ρ hρ K hK v
  have hfin : Finite (Compact.orbit τ₂ (ρ m v)) := by
    rw [horbit]
    exact Compact.finite_orbit_of_smooth ρ hρ K' hK' (ρ m v)
  have h := Compact.orbitMean_map τ₁ τ₂ (ρ m) hf v (targetFinite := hfin)
  change Compact.orbitMean τ' (ρ m v) = ρ m (Compact.orbitMean τ₁ v)
  rw [h]
  unfold Compact.orbitMean
  rw [horbit]

/-- The fixed vector `ρ m w` of the conjugate subgroup. -/
def conjFixedVector (ρ : Representation ℂ G V) (m : G) (K : OpenSubgroup G)
    (w : fixedVectors ρ K.toSubgroup) :
    fixedVectors ρ (conjOpenSubgroup m K).toSubgroup :=
  ⟨ρ m w, conj_mem_fixedVectors ρ m K w.property⟩

/-- Compression commutes with translation by an element commuting with `h`. -/
theorem compressedAction_pow_conj (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (m h : G) (hmh : m * h = h * m) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsCompact (conjOpenSubgroup m K : Set G)) (r : ℕ)
    (w : fixedVectors ρ K.toSubgroup) :
    (compressedAction ρ hρ (conjOpenSubgroup m K) hK' h ^ r) (conjFixedVector ρ m K w) =
      conjFixedVector ρ m K ((compressedAction ρ hρ K hK h ^ r) w) := by
  induction r generalizing w with
  | zero => rfl
  | succ r ih =>
    simp only [pow_succ, Module.End.mul_apply]
    have h1 : compressedAction ρ hρ (conjOpenSubgroup m K) hK' h (conjFixedVector ρ m K w) =
        conjFixedVector ρ m K (compressedAction ρ hρ K hK h w) := by
      apply Subtype.ext
      change Compact.averageMap ρ hρ (conjOpenSubgroup m K) hK' (ρ h (ρ m w)) =
        ρ m (Compact.averageMap ρ hρ K hK (ρ h w))
      have hc : ρ h (ρ m (w : V)) = ρ m (ρ h w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hmh, map_mul, Module.End.mul_apply]
      rw [hc]
      exact averageMap_conj ρ hρ m K hK hK' (ρ h w)
    rw [h1, ih]

/-- Translation by an element commuting with `h` preserves stable images. -/
theorem conjFixedVector_mem_stableImage (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (m h : G) (hmh : m * h = h * m) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsCompact (conjOpenSubgroup m K : Set G))
    (t : fixedVectors ρ K.toSubgroup) (ht : t ∈ stableImage ρ hρ K hK h) :
    conjFixedVector ρ m K t ∈ stableImage ρ hρ (conjOpenSubgroup m K) hK' h := by
  rw [mem_stableImage] at ht ⊢
  intro r
  obtain ⟨w, hw⟩ := ht r
  exact ⟨conjFixedVector ρ m K w, by
    rw [compressedAction_pow_conj ρ hρ m h hmh K hK hK' r w, hw]⟩

omit [IsTopologicalGroup G] in
/-- A vector fixed by an open subgroup is fixed by every smaller open subgroup. -/
theorem mem_fixedVectors_of_le (π : Representation ℂ G V) {K U : OpenSubgroup G}
    (h : K ≤ U) {v : V} (hv : v ∈ fixedVectors π U.toSubgroup) :
    v ∈ fixedVectors π K.toSubgroup :=
  fixedVectors_antitone π (OpenSubgroup.toSubgroup_le.mpr h) hv

omit [IsTopologicalGroup G] in
/-- Every class in a coinvariant quotient of a smooth representation has a
representative fixed by every open subgroup of some open subgroup. -/
theorem exists_open_fixed_lift (π : Representation ℂ G V) (hπ : IsSmooth π)
    (H : Subgroup G) (x : Coinvariants π H) :
    ∃ U : OpenSubgroup G, ∀ K : OpenSubgroup G, K ≤ U →
      ∃ v : fixedVectors π K.toSubgroup, mk π H v = x := by
  obtain ⟨v, rfl⟩ := mk_surjective π H x
  obtain ⟨U, hU⟩ := hπ v
  exact ⟨U, fun K hKU => ⟨⟨v, mem_fixedVectors_of_le π hKU hU⟩, rfl⟩⟩

/-- A smooth functional fixed by `K` takes the same value at a vector and at
its `K`-average. -/
theorem smoothDualPairing_averageMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {ℓ : SmoothDual ρ}
    (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup) (v : V) :
    smoothDualPairing ρ ℓ (Compact.averageMap ρ hρ K hK v) = smoothDualPairing ρ ℓ v :=
  map_averageMap_of_forall_eq ρ hρ K hK (smoothDualPairing ρ ℓ) v _ (fun k => by
    have h := smoothDualPairing_invariant (ρ := ρ) (k : G) ℓ v
    rwa [apply_eq_of_mem_fixedVectors (smoothContragredient ρ) hℓ k.property] at h)

/-- Powers of compression by `g` on the smooth dual are adjoint to powers of
compression by `g⁻¹`. -/
theorem compressedAction_pow_adjoint (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (n : ℕ)
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (v : fixedVectors ρ K.toSubgroup) :
    smoothDualFixedRestriction ρ K.toSubgroup
        ((compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
          K hK g ^ n) ℓ) v =
      smoothDualFixedRestriction ρ K.toSubgroup ℓ
        ((compressedAction ρ hρ K hK g⁻¹ ^ n) v) := by
  have h := compressedAction_adjoint ρ hρ K hK g⁻¹
  simp only [inv_inv] at h
  induction n generalizing ℓ v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, ← Module.End.mul_apply, ← pow_succ]

/-- Power kernels of compression by `g` on the smooth dual annihilate the stable
image of compression by `g⁻¹`. -/
theorem smoothDualFixedRestriction_eq_zero_of_mem_powerKernelSup
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup}
    (hℓ : ℓ ∈ powerKernelSup (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
      K hK g)
    {t : fixedVectors ρ K.toSubgroup} (ht : t ∈ stableImage ρ hρ K hK g⁻¹) :
    smoothDualFixedRestriction ρ K.toSubgroup ℓ t = 0 := by
  refine Submodule.iSup_induction
    (fun r : ℕ => LinearMap.ker (compressedAction (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K hK g ^ r))
    (motive := fun ℓ => smoothDualFixedRestriction ρ K.toSubgroup ℓ t = 0) hℓ ?_ ?_ ?_
  · intro r ℓ hℓ
    obtain ⟨w, rfl⟩ := (mem_stableImage ρ hρ K hK g⁻¹ t).mp ht r
    rw [← compressedAction_pow_adjoint ρ hρ K hK g r, LinearMap.mem_ker.mp hℓ, map_zero,
      LinearMap.zero_apply]
  · rw [map_zero, LinearMap.zero_apply]
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- The stable image of compression by `g` on the smooth dual annihilates the
power kernels of compression by `g⁻¹`. -/
theorem smoothDualFixedRestriction_eq_zero_of_mem_powerKernelSup_inv
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup}
    (hℓ : ℓ ∈ stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g)
    {v : fixedVectors ρ K.toSubgroup} (hv : v ∈ powerKernelSup ρ hρ K hK g⁻¹) :
    smoothDualFixedRestriction ρ K.toSubgroup ℓ v = 0 := by
  refine Submodule.iSup_induction
    (fun r : ℕ => LinearMap.ker (compressedAction ρ hρ K hK g⁻¹ ^ r))
    (motive := fun v => smoothDualFixedRestriction ρ K.toSubgroup ℓ v = 0) hv ?_ ?_ ?_
  · intro r v hv
    obtain ⟨μ, rfl⟩ := (mem_stableImage _ _ K hK g ℓ).mp hℓ r
    rw [compressedAction_pow_adjoint ρ hρ K hK g r, LinearMap.mem_ker.mp hv, map_zero]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

end Averaging

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Group data for the stable evaluation pairing: an upper subgroup `N`, an
opposite subgroup `Nbar`, a subgroup `M` normalizing both, an element `g`
commuting with `M` whose conjugation contracts `N`, and a cofinal family of
good compact open subgroups with an `Nbar M N` factorization. -/
structure StablePairingData (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The upper subgroup. -/
  N : Subgroup G
  /-- The opposite subgroup. -/
  Nbar : Subgroup G
  /-- The common Levi-type subgroup. -/
  M : Subgroup G
  hMN : M ≤ Subgroup.normalizer N
  hMNbar : M ≤ Subgroup.normalizer Nbar
  /-- The contracting element. -/
  g : G
  commute : ∀ m ∈ M, m * g = g * m
  /-- The good compact open subgroups. -/
  Good : OpenSubgroup G → Prop
  isCompact : ∀ K, Good K → IsCompact (K : Set G)
  exists_good_subset : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
    ∃ K, Good K ∧ (K : Set G) ⊆ O
  good_conj : ∀ m ∈ M, ∀ K, Good K → Good (conjOpenSubgroup m K)
  factor : ∀ K, Good K → ∀ k ∈ K, ∃ l ∈ K, l ∈ Nbar ∧ ∃ m ∈ K, m ∈ M ∧
    ∃ u ∈ K, u ∈ N ∧ k = l * m * u
  lower_conj : ∀ K, Good K → ∀ l ∈ K, l ∈ Nbar → g⁻¹ * l * g ∈ K
  upper_conj : ∀ K, Good K → ∀ u ∈ K, u ∈ N → ∀ r : ℕ, g ^ r * u * (g ^ r)⁻¹ ∈ K
  deep : ∀ K₀ K₁, Good K₀ → Good K₁ →
    ∃ r : ℕ, ∀ u ∈ K₀, u ∈ N → g ^ r * u * (g ^ r)⁻¹ ∈ K₁

namespace StablePairingData

variable (D : StablePairingData G)

/-- Finiteness and canonical-lift hypotheses on a smooth representation: the
upper quotient of the smooth dual is reached from the stable image of
compression by `g`, the opposite quotient from the stable image of compression
by `g⁻¹`, and in both cases the quotient kernel lies in the power kernel. -/
structure Admits (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) : Prop where
  finite : ∀ K, D.Good K → FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)
  upper_surjective : ∀ K (hK : D.Good K),
    Function.Surjective (stableImageJacquetMap (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K (D.isCompact K hK) D.g D.N D.M D.hMN)
  upper_kernel : ∀ K (hK : D.Good K),
    LinearMap.ker (fixedJacquetMap (smoothContragredient ρ) D.N D.M D.hMN K.toSubgroup) ≤
      powerKernelSup (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
        (D.isCompact K hK) D.g
  lower_surjective : ∀ K (hK : D.Good K),
    Function.Surjective (stableImageJacquetMap ρ hρ K (D.isCompact K hK) D.g⁻¹
      D.Nbar D.M D.hMNbar)
  lower_kernel : ∀ K (hK : D.Good K),
    LinearMap.ker (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup) ≤
      powerKernelSup ρ hρ K (D.isCompact K hK) D.g⁻¹

theorem exists_good_le (U : OpenSubgroup G) : ∃ K, D.Good K ∧ K ≤ U := by
  obtain ⟨K, hK, hKU⟩ := D.exists_good_subset U U.isOpen U.one_mem
  exact ⟨K, hK, hKU⟩

theorem commute_pow (m : G) (hm : m ∈ D.M) (r : ℕ) :
    m * D.g⁻¹ ^ r = D.g⁻¹ ^ r * m := by
  have h : Commute m D.g := D.commute m hm
  exact (h.inv_right.pow_right r).eq

/-- Powers of compression by `g⁻¹` are averages of powers of `g⁻¹`. -/
theorem compressedAction_inv_pow_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : D.Good K) (r : ℕ) (w : fixedVectors ρ K.toSubgroup) :
    ((compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹ ^ r) w : V) =
      Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ (D.g⁻¹ ^ r) w) := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, map_one, Module.End.one_apply, Module.End.one_apply]
    exact (Compact.averageMap_id ρ hρ K _ w w.property).symm
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, compressedAction_apply, ih]
    apply map_averageMap_of_forall_eq ρ hρ K _
      ((Compact.averageMap ρ hρ K (D.isCompact K hK)).comp (ρ D.g⁻¹))
    intro k
    obtain ⟨l, hlK, hlN, m, hmK, hmM, u, huK, huN, hk⟩ := D.factor K hK k k.property
    have hu : ρ (D.g ^ r * u * (D.g ^ r)⁻¹) (w : V) = w :=
      apply_eq_of_mem_fixedVectors ρ w.property (D.upper_conj K hK u huK huN r)
    have hm : D.g⁻¹ * m * D.g = m := by
      rw [mul_assoc, D.commute m hmM, ← mul_assoc, inv_mul_cancel, one_mul]
    have key : D.g⁻¹ * (k : G) * D.g⁻¹ ^ r =
        (D.g⁻¹ * l * D.g) * m * D.g⁻¹ ^ (r + 1) * (D.g ^ r * u * (D.g ^ r)⁻¹) := by
      have e : D.g⁻¹ * (k : G) * D.g⁻¹ ^ r =
          (D.g⁻¹ * l * D.g) * (D.g⁻¹ * m * D.g) * D.g⁻¹ ^ (r + 1) *
            (D.g ^ r * u * (D.g ^ r)⁻¹) := by
        rw [hk]
        group
      rw [e, hm]
    change Compact.averageMap ρ hρ K (D.isCompact K hK)
      (ρ D.g⁻¹ (ρ (k : G) (ρ (D.g⁻¹ ^ r) (w : V)))) = _
    have e1 : ρ D.g⁻¹ (ρ (k : G) (ρ (D.g⁻¹ ^ r) (w : V))) =
        ρ (D.g⁻¹ * (k : G) * D.g⁻¹ ^ r) w := by
      simp only [map_mul, Module.End.mul_apply]
    rw [e1, key, map_mul, Module.End.mul_apply, hu, map_mul, Module.End.mul_apply,
      map_mul, Module.End.mul_apply,
      averageMap_apply_of_mem ρ hρ K (D.isCompact K hK) (D.lower_conj K hK l hlK hlN),
      averageMap_apply_of_mem ρ hρ K (D.isCompact K hK) hmK]

/-- Class preservation under nested averaging: a linear map on the opposite
quotient which is invariant under `K₀ ∩ M` at the class of a stable vector for
`K₁ ≤ K₀` takes the same value at the class of its `K₀`-average. -/
theorem map_mk_averageMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K₀ K₁ : OpenSubgroup G} (h₀ : D.Good K₀) (h₁ : D.Good K₁) (hle : K₁ ≤ K₀)
    (s : fixedVectors ρ K₁.toSubgroup)
    (hs : s ∈ stableImage ρ hρ K₁ (D.isCompact K₁ h₁) D.g⁻¹)
    (f : Coinvariants ρ D.Nbar →ₗ[ℂ] W)
    (hf : ∀ m : D.M, (m : G) ∈ K₀ →
      f (action ρ D.Nbar D.M D.hMNbar m (Jacquet.mk ρ D.Nbar s)) = f (Jacquet.mk ρ D.Nbar s)) :
    f (Jacquet.mk ρ D.Nbar (Compact.averageMap ρ hρ K₀ (D.isCompact K₀ h₀) s)) =
      f (Jacquet.mk ρ D.Nbar s) := by
  obtain ⟨r, hr⟩ := D.deep K₀ K₁ h₀ h₁
  obtain ⟨w, hw⟩ := (mem_stableImage ρ hρ K₁ _ D.g⁻¹ s).mp hs r
  set u : V := ρ (D.g⁻¹ ^ r) (w : V) with hu
  have hsu : (s : V) = Compact.averageMap ρ hρ K₁ (D.isCompact K₁ h₁) u := by
    rw [← hw, D.compressedAction_inv_pow_apply ρ hρ K₁ h₁]
  have hfixN : ∀ x ∈ K₀, x ∈ D.N → ρ x u = u := by
    intro x hx hxN
    have e : x * D.g⁻¹ ^ r = D.g⁻¹ ^ r * (D.g ^ r * x * (D.g ^ r)⁻¹) := by group
    rw [hu, ← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply,
      apply_eq_of_mem_fixedVectors ρ w.property (hr x hx hxN)]
  have hfixM : ∀ m ∈ D.M, m ∈ K₁ → ρ m u = u := by
    intro m hmM hmK
    rw [hu, ← Module.End.mul_apply, ← map_mul, D.commute_pow m hmM r, map_mul,
      Module.End.mul_apply, apply_eq_of_mem_fixedVectors ρ w.property hmK]
  have hmks : Jacquet.mk ρ D.Nbar (s : V) = Jacquet.mk ρ D.Nbar u := by
    rw [hsu]
    apply map_averageMap_of_forall_eq ρ hρ K₁ _ (Jacquet.mk ρ D.Nbar) u
    intro k
    obtain ⟨l, -, hlN, m, hmK, hmM, x, hxK, hxN, hk⟩ := D.factor K₁ h₁ k k.property
    rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfixN x (hle hxK) hxN, hfixM m hmM hmK]
    exact mk_apply_subgroup ρ D.Nbar ⟨l, hlN⟩ u
  have havg : Compact.averageMap ρ hρ K₀ (D.isCompact K₀ h₀) (s : V) =
      Compact.averageMap ρ hρ K₀ (D.isCompact K₀ h₀) u := by
    rw [hsu, averageMap_averageMap_of_le ρ hρ K₀ K₁ _ _ hle]
  rw [havg]
  apply map_averageMap_of_forall_eq ρ hρ K₀ _ (f.comp (Jacquet.mk ρ D.Nbar)) u
  intro k
  obtain ⟨l, -, hlN, m, hmK, hmM, x, hxK, hxN, hk⟩ := D.factor K₀ h₀ k k.property
  change f (Jacquet.mk ρ D.Nbar (ρ (k : G) u)) = _
  rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    hfixN x hxK hxN, mk_apply_subgroup ρ D.Nbar ⟨l, hlN⟩, hmks]
  have h := hf ⟨m, hmM⟩ hmK
  rw [hmks, action_mk] at h
  exact h


theorem exists_good_le_inf (U₁ U₂ : OpenSubgroup G) :
    ∃ K, D.Good K ∧ K ≤ U₁ ∧ K ≤ U₂ := by
  obtain ⟨K, hK, hKU⟩ := D.exists_good_le (U₁ ⊓ U₂)
  exact ⟨K, hK, hKU.trans inf_le_left, hKU.trans inf_le_right⟩

variable {D}
variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}

/-- A fixed vector has a stable vector with the same opposite class. -/
theorem exists_stable_mk_eq (hA : D.Admits ρ hρ) {K : OpenSubgroup G} (hK : D.Good K)
    (v : fixedVectors ρ K.toSubgroup) :
    ∃ t : fixedVectors ρ K.toSubgroup, t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ ∧
      Jacquet.mk ρ D.Nbar t = Jacquet.mk ρ D.Nbar v := by
  obtain ⟨t, ht⟩ := hA.lower_surjective K hK
    (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup v)
  exact ⟨t.val, t.property, congrArg Subtype.val ht⟩

/-- A fixed smooth functional has a stable functional with the same upper class. -/
theorem exists_dual_stable_mk_eq (hA : D.Admits ρ hρ) {K : OpenSubgroup G}
    (hK : D.Good K) (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    ∃ ℓ' : fixedVectors (smoothContragredient ρ) K.toSubgroup,
      ℓ' ∈ stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
        (D.isCompact K hK) D.g ∧
      Jacquet.mk (smoothContragredient ρ) D.N (ℓ' : SmoothDual ρ) =
        Jacquet.mk (smoothContragredient ρ) D.N ℓ := by
  obtain ⟨ℓ', h⟩ := hA.upper_surjective K hK
    (fixedJacquetMap (smoothContragredient ρ) D.N D.M D.hMN K.toSubgroup ℓ)
  exact ⟨ℓ'.val, ℓ'.property, congrArg Subtype.val h⟩

/-- Every opposite class has stable representatives for all small good subgroups. -/
theorem exists_open_stable_lift (hA : D.Admits ρ hρ) (y : Coinvariants ρ D.Nbar) :
    ∃ U : OpenSubgroup G, ∀ K (hK : D.Good K), K ≤ U →
      ∃ t : fixedVectors ρ K.toSubgroup,
        t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ ∧ Jacquet.mk ρ D.Nbar t = y := by
  obtain ⟨U, hU⟩ := exists_open_fixed_lift ρ hρ D.Nbar y
  refine ⟨U, fun K hK hKU => ?_⟩
  obtain ⟨v, hv⟩ := hU K hKU
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK v
  exact ⟨t, ht, hmk.trans hv⟩

/-- Fixed smooth functionals with the same upper class agree on stable vectors. -/
theorem pairing_eq_of_dual_mk_eq (hA : D.Admits ρ hρ) {K : OpenSubgroup G}
    (hK : D.Good K) {ℓ ℓ' : fixedVectors (smoothContragredient ρ) K.toSubgroup}
    (h : Jacquet.mk (smoothContragredient ρ) D.N (ℓ : SmoothDual ρ) =
      Jacquet.mk (smoothContragredient ρ) D.N ℓ')
    {t : fixedVectors ρ K.toSubgroup}
    (ht : t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹) :
    smoothDualPairing ρ ℓ t = smoothDualPairing ρ ℓ' t := by
  have hker : ℓ - ℓ' ∈ LinearMap.ker
      (fixedJacquetMap (smoothContragredient ρ) D.N D.M D.hMN K.toSubgroup) := by
    have e : fixedJacquetMap (smoothContragredient ρ) D.N D.M D.hMN K.toSubgroup ℓ =
        fixedJacquetMap (smoothContragredient ρ) D.N D.M D.hMN K.toSubgroup ℓ' :=
      Subtype.ext h
    exact (LinearMap.sub_mem_ker_iff (f := fixedJacquetMap (smoothContragredient ρ) D.N D.M
      D.hMN K.toSubgroup) (x := ℓ) (y := ℓ')).mpr e
  have h0 := smoothDualFixedRestriction_eq_zero_of_mem_powerKernelSup ρ hρ K
    (D.isCompact K hK) D.g (hA.upper_kernel K hK hker) ht
  change (ℓ : SmoothDual ρ).val t - (ℓ' : SmoothDual ρ).val t = 0 at h0
  exact sub_eq_zero.mp h0

/-- A stable smooth functional takes equal values at fixed vectors with the same
opposite class. -/
theorem pairing_eq_of_mk_eq (hA : D.Admits ρ hρ) {K : OpenSubgroup G} (hK : D.Good K)
    {ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup}
    (hℓ : ℓ ∈ stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
      (D.isCompact K hK) D.g)
    {v v' : fixedVectors ρ K.toSubgroup}
    (h : Jacquet.mk ρ D.Nbar (v : V) = Jacquet.mk ρ D.Nbar v') :
    smoothDualPairing ρ ℓ v = smoothDualPairing ρ ℓ v' := by
  have hker : v - v' ∈ LinearMap.ker
      (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact Subtype.ext h
  have h0 := smoothDualFixedRestriction_eq_zero_of_mem_powerKernelSup_inv ρ hρ K
    (D.isCompact K hK) D.g hℓ (hA.lower_kernel K hK hker)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- Nested comparison: for good `K₁ ≤ K₀`, a `K₀`-fixed smooth functional takes
equal values at stable vectors for `K₀` and for `K₁` with the same opposite
class. -/
theorem pairing_eq_of_le (hA : D.Admits ρ hρ) {K₀ K₁ : OpenSubgroup G}
    (h₀ : D.Good K₀) (h₁ : D.Good K₁) (hle : K₁ ≤ K₀) {ℓ : SmoothDual ρ}
    (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K₀.toSubgroup)
    {t₀ : fixedVectors ρ K₀.toSubgroup}
    (ht₀ : t₀ ∈ stableImage ρ hρ K₀ (D.isCompact K₀ h₀) D.g⁻¹)
    {t₁ : fixedVectors ρ K₁.toSubgroup}
    (ht₁ : t₁ ∈ stableImage ρ hρ K₁ (D.isCompact K₁ h₁) D.g⁻¹)
    (h : Jacquet.mk ρ D.Nbar (t₀ : V) = Jacquet.mk ρ D.Nbar t₁) :
    smoothDualPairing ρ ℓ t₀ = smoothDualPairing ρ ℓ t₁ := by
  obtain ⟨ℓ', hℓ', hmk⟩ := D.exists_dual_stable_mk_eq hA h₀ ⟨ℓ, hℓ⟩
  have e₀ : smoothDualPairing ρ ℓ t₀ = smoothDualPairing ρ ℓ' t₀ :=
    D.pairing_eq_of_dual_mk_eq hA h₀ (ℓ := ⟨ℓ, hℓ⟩) (ℓ' := ℓ') hmk.symm ht₀
  have e₁ : smoothDualPairing ρ ℓ t₁ = smoothDualPairing ρ ℓ' t₁ :=
    D.pairing_eq_of_dual_mk_eq hA h₁
      (ℓ := ⟨ℓ, mem_fixedVectors_of_le _ hle hℓ⟩)
      (ℓ' := ⟨ℓ', mem_fixedVectors_of_le _ hle ℓ'.property⟩) hmk.symm ht₁
  set a : V := Compact.averageMap ρ hρ K₀ (D.isCompact K₀ h₀) t₁ with ha_def
  have ha : a ∈ fixedVectors ρ K₀.toSubgroup :=
    Compact.averageMap_mem_fixedVectors ρ hρ K₀ _ t₁
  have e₂ : smoothDualPairing ρ ℓ' t₁ = smoothDualPairing ρ ℓ' a :=
    (smoothDualPairing_averageMap ρ hρ K₀ _ ℓ'.property t₁).symm
  have hmka : Jacquet.mk ρ D.Nbar a = Jacquet.mk ρ D.Nbar t₀ := by
    rw [h]
    refine D.map_mk_averageMap ρ hρ h₀ h₁ hle t₁ ht₁ LinearMap.id ?_
    intro m hm
    rw [LinearMap.id_apply, LinearMap.id_apply, ← h, action_mk]
    exact congrArg _ (apply_eq_of_mem_fixedVectors ρ t₀.property hm)
  have e₃ : smoothDualPairing ρ ℓ' a = smoothDualPairing ρ ℓ' t₀ :=
    D.pairing_eq_of_mk_eq hA h₀ hℓ' (v := ⟨a, ha⟩) (v' := t₀) hmka
  rw [e₀, e₁, e₂, e₃]

/-- The evaluation of a fixed smooth functional at a stable vector depends only
on their classes. -/
theorem exists_value (hA : D.Admits ρ hρ) (x : Coinvariants (smoothContragredient ρ) D.N)
    (y : Coinvariants ρ D.Nbar) :
    ∃ c : ℂ, ∀ (K : OpenSubgroup G) (hK : D.Good K)
      (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
      (t : fixedVectors ρ K.toSubgroup),
      t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ →
      Jacquet.mk (smoothContragredient ρ) D.N (ℓ : SmoothDual ρ) = x →
      Jacquet.mk ρ D.Nbar (t : V) = y → smoothDualPairing ρ ℓ t = c := by
  obtain ⟨U, hU⟩ := exists_open_fixed_lift (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) D.N x
  obtain ⟨U', hU'⟩ := D.exists_open_stable_lift hA y
  obtain ⟨K₀, h₀, hK₀U, hK₀U'⟩ := D.exists_good_le_inf U U'
  obtain ⟨ℓ₀, hℓ₀⟩ := hU K₀ hK₀U
  obtain ⟨t₀, ht₀, ht₀y⟩ := hU' K₀ h₀ hK₀U'
  refine ⟨smoothDualPairing ρ ℓ₀ t₀, ?_⟩
  intro K hK ℓ t ht hℓx hty
  obtain ⟨K₂, h₂, hK₂K, hK₂K₀⟩ := D.exists_good_le_inf K K₀
  obtain ⟨t₂, ht₂, hmk₂⟩ := D.exists_stable_mk_eq hA h₂
    ⟨t, mem_fixedVectors_of_le ρ hK₂K t.property⟩
  have e₁ : smoothDualPairing ρ ℓ t = smoothDualPairing ρ ℓ t₂ :=
    D.pairing_eq_of_le hA hK h₂ hK₂K ℓ.property ht ht₂ hmk₂.symm
  have e₂ : smoothDualPairing ρ ℓ₀ t₀ = smoothDualPairing ρ ℓ₀ t₂ :=
    D.pairing_eq_of_le hA h₀ h₂ hK₂K₀ ℓ₀.property ht₀ ht₂
      (ht₀y.trans (hty.symm.trans hmk₂.symm))
  have e₃ : smoothDualPairing ρ ℓ t₂ = smoothDualPairing ρ ℓ₀ t₂ :=
    D.pairing_eq_of_dual_mk_eq hA h₂
      (ℓ := ⟨ℓ, mem_fixedVectors_of_le _ hK₂K ℓ.property⟩)
      (ℓ' := ⟨ℓ₀, mem_fixedVectors_of_le _ hK₂K₀ ℓ₀.property⟩) (hℓx.trans hℓ₀.symm) ht₂
  rw [e₁, e₃, e₂]

variable (D) in
/-- A bilinear pairing between the upper quotient of the smooth dual and the
opposite quotient is *stable* if, for every good subgroup `K`, it pairs the class
of a `K`-fixed smooth functional with the class of a vector in the stable image
of compression by `g⁻¹` by evaluation. -/
def IsStablePairing (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
      Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ) : Prop :=
  ∀ (K : OpenSubgroup G) (hK : D.Good K)
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (t : fixedVectors ρ K.toSubgroup),
    t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ →
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar t) =
        smoothDualPairing ρ ℓ t

/-- Two upper classes and two opposite classes have fixed and stable
representatives for a common good subgroup. -/
theorem exists_common_lift (hA : D.Admits ρ hρ)
    (x₁ x₂ : Coinvariants (smoothContragredient ρ) D.N) (y₁ y₂ : Coinvariants ρ D.Nbar) :
    ∃ K, ∃ hK : D.Good K, ∃ ℓ₁ ℓ₂ : fixedVectors (smoothContragredient ρ) K.toSubgroup,
      ∃ t₁ t₂ : fixedVectors ρ K.toSubgroup,
        t₁ ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ ∧
        t₂ ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ ∧
        Jacquet.mk (smoothContragredient ρ) D.N (ℓ₁ : SmoothDual ρ) = x₁ ∧
        Jacquet.mk (smoothContragredient ρ) D.N (ℓ₂ : SmoothDual ρ) = x₂ ∧
        Jacquet.mk ρ D.Nbar (t₁ : V) = y₁ ∧ Jacquet.mk ρ D.Nbar (t₂ : V) = y₂ := by
  obtain ⟨U₁, hU₁⟩ := exists_open_fixed_lift (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) D.N x₁
  obtain ⟨U₂, hU₂⟩ := exists_open_fixed_lift (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) D.N x₂
  obtain ⟨U₃, hU₃⟩ := D.exists_open_stable_lift hA y₁
  obtain ⟨U₄, hU₄⟩ := D.exists_open_stable_lift hA y₂
  obtain ⟨K, hK, hKU⟩ := D.exists_good_le (U₁ ⊓ U₂ ⊓ (U₃ ⊓ U₄))
  have h₁ : K ≤ U₁ := hKU.trans (inf_le_left.trans inf_le_left)
  have h₂ : K ≤ U₂ := hKU.trans (inf_le_left.trans inf_le_right)
  have h₃ : K ≤ U₃ := hKU.trans (inf_le_right.trans inf_le_left)
  have h₄ : K ≤ U₄ := hKU.trans (inf_le_right.trans inf_le_right)
  obtain ⟨ℓ₁, e₁⟩ := hU₁ K h₁
  obtain ⟨ℓ₂, e₂⟩ := hU₂ K h₂
  obtain ⟨t₁, ht₁, e₃⟩ := hU₃ K hK h₃
  obtain ⟨t₂, ht₂, e₄⟩ := hU₄ K hK h₄
  exact ⟨K, hK, ℓ₁, ℓ₂, t₁, t₂, ht₁, ht₂, e₁, e₂, e₃, e₄⟩

/-- A stable pairing exists. -/
theorem exists_isStablePairing (hA : D.Admits ρ hρ) :
    ∃ b, D.IsStablePairing ρ hρ b := by
  choose f hf using fun x y => D.exists_value hA x y
  have key : ∀ (K : OpenSubgroup G) (hK : D.Good K)
      (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
      (t : fixedVectors ρ K.toSubgroup),
      t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ →
      f (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar t) =
        smoothDualPairing ρ ℓ t :=
    fun K hK ℓ t ht => (hf _ _ K hK ℓ t ht rfl rfl).symm
  refine ⟨LinearMap.mk₂ ℂ f ?_ ?_ ?_ ?_, fun K hK ℓ t ht => key K hK ℓ t ht⟩
  · intro x₁ x₂ y
    obtain ⟨K, hK, ℓ₁, ℓ₂, t, -, ht, -, rfl, rfl, rfl, -⟩ := D.exists_common_lift hA x₁ x₂ y y
    have e := key K hK (ℓ₁ + ℓ₂) t ht
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply] at e
    rw [e, key K hK ℓ₁ t ht, key K hK ℓ₂ t ht]
  · intro c x y
    obtain ⟨K, hK, ℓ, -, t, -, ht, -, rfl, -, rfl, -⟩ := D.exists_common_lift hA x x y y
    have e := key K hK (c • ℓ) t ht
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply] at e
    rw [e, key K hK ℓ t ht]
  · intro x y₁ y₂
    obtain ⟨K, hK, ℓ, -, t₁, t₂, ht₁, ht₂, rfl, -, rfl, rfl⟩ :=
      D.exists_common_lift hA x x y₁ y₂
    have e := key K hK ℓ (t₁ + t₂) (add_mem ht₁ ht₂)
    simp only [Submodule.coe_add, map_add] at e
    rw [e, key K hK ℓ t₁ ht₁, key K hK ℓ t₂ ht₂]
  · intro c x y
    obtain ⟨K, hK, ℓ, -, t, -, ht, -, rfl, -, rfl, -⟩ := D.exists_common_lift hA x x y y
    have e := key K hK ℓ (c • t) (Submodule.smul_mem _ c ht)
    simp only [Submodule.coe_smul, map_smul] at e
    rw [e, key K hK ℓ t ht]

namespace IsStablePairing

variable {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- A stable pairing is nondegenerate on the upper side. -/
theorem injective (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b) :
    Function.Injective b := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨U, hU⟩ := exists_open_fixed_lift (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) D.N x
  obtain ⟨K, hK, hKU⟩ := D.exists_good_le U
  obtain ⟨ℓ, rfl⟩ := hU K hKU
  obtain ⟨ℓ', hℓ', hmk⟩ := D.exists_dual_stable_mk_eq hA hK ℓ
  have hd := compactCompression_stableEvaluationDuality ρ hρ K (D.isCompact K hK) D.g⁻¹
    (hA.finite K hK)
  obtain ⟨E, hE⟩ := hd
  have hℓ'' : ℓ' ∈ stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
      (D.isCompact K hK) D.g⁻¹⁻¹ := by
    rwa [inv_inv]
  have h0 : E ⟨ℓ', hℓ''⟩ = 0 := by
    refine LinearMap.ext fun t => ?_
    rw [hE, LinearMap.zero_apply]
    change smoothDualPairing ρ (ℓ' : SmoothDual ρ) ((t : fixedVectors ρ K.toSubgroup) : V) = 0
    rw [← hb K hK ℓ' t.val t.property, hmk, hx, LinearMap.zero_apply]
  have h1 := congrArg Subtype.val (E.map_eq_zero_iff.mp h0)
  change ℓ' = 0 at h1
  rw [← hmk, h1, ZeroMemClass.coe_zero, map_zero]

/-- Every opposite-side functional invariant under `K ∩ M` for a good `K` is
given by a stable pairing. -/
theorem exists_eq (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    {K : OpenSubgroup G} (hK : D.Good K) (φ : Module.Dual ℂ (Coinvariants ρ D.Nbar))
    (hφ : ∀ m : D.M, (m : G) ∈ K → ∀ y,
      φ (action ρ D.Nbar D.M D.hMNbar m y) = φ y) :
    ∃ x, b x = φ := by
  have hd := compactCompression_stableEvaluationDuality ρ hρ K (D.isCompact K hK) D.g⁻¹
    (hA.finite K hK)
  obtain ⟨E, hE⟩ := hd
  let ψ : Module.Dual ℂ (stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹) :=
    φ.comp ((Jacquet.mk ρ D.Nbar).comp
      (stableImageToRepresentation ρ hρ K (D.isCompact K hK) D.g⁻¹))
  set ℓ := E.symm ψ with hℓ_def
  have key : ∀ t : stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹,
      smoothDualPairing ρ ((ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) :
        SmoothDual ρ) ((t : fixedVectors ρ K.toSubgroup) : V) =
        φ (Jacquet.mk ρ D.Nbar ((t : fixedVectors ρ K.toSubgroup) : V)) := by
    intro t
    have h := hE ℓ t
    rw [hℓ_def, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨Jacquet.mk (smoothContragredient ρ) D.N
    ((ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) : SmoothDual ρ),
    LinearMap.ext fun y => ?_⟩
  obtain ⟨U, hU⟩ := D.exists_open_stable_lift hA y
  obtain ⟨K₁, h₁, hK₁K, hK₁U⟩ := D.exists_good_le_inf K U
  obtain ⟨t₁, ht₁, rfl⟩ := hU K₁ h₁ hK₁U
  have e₁ := hb K₁ h₁ ⟨_, mem_fixedVectors_of_le _ hK₁K (ℓ : fixedVectors
    (smoothContragredient ρ) K.toSubgroup).property⟩ t₁ ht₁
  set a : V := Compact.averageMap ρ hρ K (D.isCompact K hK) t₁ with ha_def
  have ha : a ∈ fixedVectors ρ K.toSubgroup :=
    Compact.averageMap_mem_fixedVectors ρ hρ K _ t₁
  have e₂ := smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK)
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup).property t₁
  obtain ⟨t, ht, hmkt⟩ := D.exists_stable_mk_eq hA hK ⟨a, ha⟩
  have hℓs : (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) ∈
      stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
        (D.isCompact K hK) D.g := by
    have h : ∀ x, x ∈ stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K
        (D.isCompact K hK) D.g⁻¹⁻¹ → x ∈ stableImage (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K (D.isCompact K hK) D.g := fun x hx => by
      rwa [inv_inv] at hx
    exact h _ ℓ.property
  have e₃ := D.pairing_eq_of_mk_eq hA hK hℓs (v := ⟨a, ha⟩) (v' := t) hmkt.symm
  have e₄ := key ⟨t, ht⟩
  have e₅ := D.map_mk_averageMap ρ hρ hK h₁ hK₁K t₁ ht₁ φ (fun m hm => hφ m hm _)
  refine e₁.trans (e₂.symm.trans (e₃.trans (e₄.trans ?_)))
  change φ (Jacquet.mk ρ D.Nbar t) = φ (Jacquet.mk ρ D.Nbar t₁)
  rw [hmkt]
  exact e₅

/-- A stable pairing is invariant under the common subgroup `M`. -/
theorem map_action (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b) (m : D.M)
    (x : Coinvariants (smoothContragredient ρ) D.N) (y : Coinvariants ρ D.Nbar) :
    b (action (smoothContragredient ρ) D.N D.M D.hMN m x)
        (action ρ D.Nbar D.M D.hMNbar m y) = b x y := by
  obtain ⟨K, hK, ℓ, -, t, -, ht, -, rfl, -, rfl, -⟩ := D.exists_common_lift hA x x y y
  have hK' := D.good_conj m m.property K hK
  have hc : (m : G) * D.g⁻¹ = D.g⁻¹ * m := by
    simpa using D.commute_pow m m.property 1
  have ht' := conjFixedVector_mem_stableImage ρ hρ m D.g⁻¹ hc K (D.isCompact K hK)
    (D.isCompact _ hK') t ht
  have e := hb _ hK' (conjFixedVector (smoothContragredient ρ) m K ℓ)
    (conjFixedVector ρ m K t) ht'
  rw [action_mk, action_mk, hb K hK ℓ t ht]
  exact e.trans (smoothDualPairing_invariant (m : G) (ℓ : SmoothDual ρ) (t : V))

/-- Each functional of a stable pairing is invariant under `U ∩ M` for some open
subgroup `U`. -/
theorem exists_open_invariant (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    (x : Coinvariants (smoothContragredient ρ) D.N) :
    ∃ U : OpenSubgroup G, ∀ m : D.M, (m : G) ∈ U → ∀ y,
      b x (action ρ D.Nbar D.M D.hMNbar m y) = b x y := by
  obtain ⟨U, hU⟩ := exists_open_fixed_lift (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) D.N x
  obtain ⟨ℓ, rfl⟩ := hU U le_rfl
  refine ⟨U, fun m hm y => ?_⟩
  have h := hb.map_action hA m⁻¹ (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
    (action ρ D.Nbar D.M D.hMNbar m y)
  have h₁ : action (smoothContragredient ρ) D.N D.M D.hMN m⁻¹
      (Jacquet.mk (smoothContragredient ρ) D.N ℓ) =
      Jacquet.mk (smoothContragredient ρ) D.N ℓ := by
    rw [action_mk]
    exact congrArg _ (apply_eq_of_mem_fixedVectors _ ℓ.property (U.inv_mem hm))
  have h₂ : action ρ D.Nbar D.M D.hMNbar m⁻¹ (action ρ D.Nbar D.M D.hMNbar m y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h₁, h₂] at h
  exact h.symm

/-- Stable pairings are natural in intertwiners. -/
theorem natural {σ : Representation ℂ G W} {hσ : IsSmooth σ} (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b)
    {bσ : Coinvariants (smoothContragredient σ) D.N →ₗ[ℂ] Coinvariants σ D.Nbar →ₗ[ℂ] ℂ}
    (hbσ : D.IsStablePairing σ hσ bσ) (a : ρ.IntertwiningMap σ)
    (x : Coinvariants (smoothContragredient σ) D.N) (y : Coinvariants ρ D.Nbar) :
    b (Jacquet.map D.N D.M D.hMN (contragredientMap a) x) y =
      bσ x (Jacquet.map D.Nbar D.M D.hMNbar a y) := by
  obtain ⟨U₁, hU₁⟩ := exists_open_fixed_lift (smoothContragredient σ)
    (isSmooth_smoothContragredient σ) D.N x
  obtain ⟨U₂, hU₂⟩ := D.exists_open_stable_lift hA y
  obtain ⟨K, hK, hKU₁, hKU₂⟩ := D.exists_good_le_inf U₁ U₂
  obtain ⟨ℓ, rfl⟩ := hU₁ K hKU₁
  obtain ⟨t, ht, rfl⟩ := hU₂ K hK hKU₂
  rw [Jacquet.map_mk, Jacquet.map_mk]
  have e₁ := hb K hK (fixedVectorsMap (contragredientMap a) K.toSubgroup ℓ) t ht
  have e₂ := hbσ K hK ℓ (fixedVectorsMap a K.toSubgroup t)
    (fixedVectorsMap_mem_stableImage ρ σ hρ hσ K (D.isCompact K hK) D.g⁻¹ a t ht)
  exact e₁.trans e₂.symm

/-- A stable pairing gives an equivalence from a character twist of the upper
quotient of the smooth dual to the smooth contragredient of a character twist of
the opposite quotient, both acting through a topological isomorphism `ι` onto
`M`, provided the two twisting characters are mutually inverse and the opposite
one has open kernel. -/
theorem exists_equiv (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] (ι : L ≃ₜ* D.M)
    (χU : L → ℂ) (χO : L →* ℂˣ) (hχ : ∀ l, χU l * (χO l : ℂ) = 1)
    (hχO : IsOpen (χO.ker : Set L))
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (σU : Representation ℂ L X)
    (eX : X ≃ₗ[ℂ] Coinvariants (smoothContragredient ρ) D.N)
    (heX : ∀ l x, eX (σU l x) =
      χU l • action (smoothContragredient ρ) D.N D.M D.hMN (ι l) (eX x))
    (σO : Representation ℂ L (Coinvariants ρ D.Nbar))
    (hσO : ∀ l y, σO l y = (χO l : ℂ) • action ρ D.Nbar D.M D.hMNbar (ι l) y) :
    ∃ E : Representation.Equiv σU (smoothContragredient σO),
      ∀ x y, (E x).1 y = b (eX x) y := by
  let ker : OpenSubgroup L := { toSubgroup := χO.ker, isOpen' := hχO }
  have hsmooth : ∀ x : X, (b ∘ₗ eX.toLinearMap) x ∈ smoothVectors σO.dual := by
    intro x
    obtain ⟨U, hU⟩ := hb.exists_open_invariant hA (eX x)
    let f : L →* G := D.M.subtype.comp ι.toMonoidHom
    have hf : Continuous f := continuous_subtype_val.comp ι.continuous
    refine ⟨U.comap f hf ⊓ ker, ?_⟩
    intro h
    obtain ⟨hhU, hhker⟩ := OpenSubgroup.mem_inf.mp h.property
    have hχh : χO ((h : L)⁻¹) = 1 := by
      rw [map_inv, MonoidHom.mem_ker.mp hhker, inv_one]
    have hfU : f ((h : L)⁻¹) ∈ U := by
      rw [map_inv]
      exact U.inv_mem (OpenSubgroup.mem_comap.mp hhU)
    apply LinearMap.ext
    intro y
    change b (eX x) (σO (h : L)⁻¹ y) = b (eX x) y
    rw [hσO, hχh, Units.val_one, one_smul]
    exact hU (ι (h : L)⁻¹) hfU y
  let Φ : X →ₗ[ℂ] SmoothDual σO :=
    LinearMap.codRestrict (smoothVectors σO.dual) (b ∘ₗ eX.toLinearMap) hsmooth
  have hint : ∀ l x, Φ (σU l x) = smoothContragredient σO l (Φ x) := by
    intro l x
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change b (eX (σU l x)) y = b (eX x) (σO l⁻¹ y)
    have hy : action ρ D.Nbar D.M D.hMNbar (ι l)
        (action ρ D.Nbar D.M D.hMNbar (ι l⁻¹) y) = y := by
      rw [map_inv]
      exact Representation.self_inv_apply _ _ _
    have hm := hb.map_action hA (ι l) (eX x) (action ρ D.Nbar D.M D.hMNbar (ι l⁻¹) y)
    rw [hy] at hm
    have hχl : χU l = ((χO l⁻¹ : ℂˣ) : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left (hχ l)
    rw [heX, hσO, map_smul, LinearMap.smul_apply, map_smul, hm, hχl]
  let Ψ : σU.IntertwiningMap (smoothContragredient σO) :=
    { toLinearMap := Φ
      isIntertwining' := fun l => LinearMap.ext fun x => hint l x }
  have hinj : Function.Injective Ψ := by
    intro x x' h
    exact eX.injective (hb.injective hA (congrArg Subtype.val h))
  have hsurj : Function.Surjective Ψ := by
    intro φ
    obtain ⟨H, hH⟩ := φ.property
    let H' : OpenSubgroup L := H ⊓ ker
    have hopen : IsOpen (ι '' (H' : Set L)) := ι.toHomeomorph.isOpenMap _ H'.isOpen
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hopen
    have h1 : (1 : G) ∈ O := by
      have h : (1 : D.M) ∈ ι '' (H' : Set L) := ⟨1, H'.one_mem, map_one ι⟩
      rw [← hOeq] at h
      exact h
    obtain ⟨K, hK, hKO⟩ := D.exists_good_subset O hO h1
    obtain ⟨x', hx'⟩ := hb.exists_eq hA hK φ.val (fun m hm y => by
      have hmO : m ∈ Subtype.val ⁻¹' O := hKO hm
      rw [hOeq] at hmO
      obtain ⟨h, hh, rfl⟩ := hmO
      obtain ⟨hhH, hhker⟩ := OpenSubgroup.mem_inf.mp hh
      have e := congrArg (fun ψ : Module.Dual ℂ (Coinvariants ρ D.Nbar) => ψ y)
        (hH ⟨h⁻¹, H.inv_mem hhH⟩)
      change φ.val (σO h⁻¹⁻¹ y) = φ.val y at e
      rw [inv_inv, hσO, MonoidHom.mem_ker.mp hhker, Units.val_one, one_smul] at e
      exact e)
    refine ⟨eX.symm x', Subtype.ext ?_⟩
    change b (eX (eX.symm x')) = φ.val
    rw [LinearEquiv.apply_symm_apply, hx']
  exact ⟨Ψ.ofBijective ⟨hinj, hsurj⟩, fun x y => rfl⟩

end IsStablePairing

end StablePairingData

end Pairing

end Langlands.Jacquet
