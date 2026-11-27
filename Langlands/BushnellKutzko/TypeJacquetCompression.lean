import Langlands.Representation.Jacquet.JointIwahoriEigenCoefficient

/-! # Nonvanishing Jacquet modules from injective compression -/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

private theorem IsWeakIwahoriContraction.eventually_mem
    {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (h : IsWeakIwahoriContraction K N M Nbar g)
    (hexhaust : ∀ x ∈ N, ∃ r : ℕ, g ^ r * x * (g ^ r)⁻¹ ∈ K)
    (hMN : M ≤ Subgroup.normalizer N) (x : N) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → g ^ s * x.val * (g ^ s)⁻¹ ∈ K := by
  obtain ⟨r, hr⟩ := hexhaust x.val x.property
  refine ⟨r, fun s hs => ?_⟩
  have hgN : g ^ r ∈ Subgroup.normalizer N := pow_mem (hMN h.mem_levi) r
  have hN : g ^ r * x.val * (g ^ r)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hgN x.val).mp x.property
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e : g ^ (r + t) * x.val * (g ^ (r + t))⁻¹ =
      g ^ t * (g ^ r * x.val * (g ^ r)⁻¹) * (g ^ t)⁻¹ := by
    group
  rw [e]
  exact ((h.pow t).upper _ ⟨hr, hN⟩).1

variable [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The compressed action of `g` acts by `g` and then averages over `K`.
It is a linear endomorphism of the whole space. -/
def compressionMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) : V →ₗ[ℂ] V :=
  (Compact.averageMap ρ hρ K hK).comp (ρ g)

@[simp] theorem compressionMap_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (v : V) :
    compressionMap ρ hρ K hK g v = Compact.averageMap ρ hρ K hK (ρ g v) := rfl

/-- Compression is multiplicative on `K`-fixed vectors when every element of `K` factors as
`u * l` with `x u x⁻¹ ∈ K` and `y⁻¹ l y ∈ K`. -/
theorem compressionMap_mul_of_factor (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x y : G)
    (hfac : ∀ k ∈ K, ∃ u l : G, k = u * l ∧ x * u * x⁻¹ ∈ K ∧ y⁻¹ * l * y ∈ K)
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    compressionMap ρ hρ K hK x (compressionMap ρ hρ K hK y v) =
      compressionMap ρ hρ K hK (x * y) v := by
  simp only [compressionMap_apply]
  refine map_averageMap_of_forall_eq ρ hρ K hK ((Compact.averageMap ρ hρ K hK).comp (ρ x))
    (ρ y v) _ ?_
  intro k
  obtain ⟨u, l, hk, hu, hl⟩ := hfac k.val k.property
  have hlv : ρ l (ρ y v) = ρ y v := by
    calc ρ l (ρ y v) = ρ y (ρ (y⁻¹ * l * y) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ y v := by
          have h' : ρ (y⁻¹ * l * y) v = v := hv ⟨_, hl⟩
          rw [h']
  change Compact.averageMap ρ hρ K hK (ρ x (ρ k.val (ρ y v))) = _
  rw [hk, map_mul, Module.End.mul_apply, hlv]
  calc Compact.averageMap ρ hρ K hK (ρ x (ρ u (ρ y v)))
      = Compact.averageMap ρ hρ K hK (ρ (x * u * x⁻¹) (ρ (x * y) v)) := by
        simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
    _ = _ := averageMap_apply_of_mem ρ hρ K hK hu _

/-- Compression by an element normalizing `K` is the action of that element on `K`-fixed
vectors. -/
theorem compressionMap_of_normalizes (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (hx : ∀ k ∈ K, x⁻¹ * k * x ∈ K) (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    compressionMap ρ hρ K hK x v = ρ x v := by
  rw [compressionMap_apply]
  refine Compact.averageMap_id ρ hρ K hK _ ?_
  intro k
  change ρ k.val (ρ x v) = ρ x v
  calc ρ k.val (ρ x v) = ρ x (ρ (x⁻¹ * k.val * x) v) := by
        simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
    _ = ρ x v := by
        have h' : ρ (x⁻¹ * k.val * x) v = v := hv ⟨_, hx k.val k.property⟩
        rw [h']

/-- Transfer the power identity for compression on fixed vectors to the whole-space map. -/
private theorem compressionMap_pow (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (h : IsWeakIwahoriContraction K N M Nbar g) (r : ℕ) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    (compressionMap ρ hρ K hK g ^ r) v = compressionMap ρ hρ K hK (g ^ r) v := by
  have hpow (s : ℕ) (w : fixedVectors ρ K.toSubgroup) :
      (compressionMap ρ hρ K hK g ^ s) (w : V) =
        ((compressedAction ρ hρ K hK g ^ s) w : V) := by
    induction s with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ s ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  calc
    (compressionMap ρ hρ K hK g ^ r) v =
        ((compressedAction ρ hρ K hK g ^ r) ⟨v, hv⟩ : V) := hpow r ⟨v, hv⟩
    _ = compressionMap ρ hρ K hK (g ^ r) v := by
      rw [← h.compressedAction_pow ρ hρ hK hfactor r]
      rfl

/-- For a factorized compact open subgroup `K` and a weak contraction `g` whose powers
carry each element of `N` into `K`, vanishing of `N`-coinvariants makes the compression
locally nilpotent on `K`-fixed vectors. -/
theorem exists_pow_compressionMap_eq_zero (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}
    (h : IsWeakIwahoriContraction K N M Nbar g)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (hexhaust : ∀ x ∈ N, ∃ r : ℕ, g ^ r * x * (g ^ r)⁻¹ ∈ K)
    (hMN : M ≤ Subgroup.normalizer N)
    (hN : Subsingleton (Coinvariants ρ N)) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    ∃ r : ℕ, (compressionMap ρ hρ K hK g ^ r) v = 0 := by
  have hrel : v ∈ relations ρ N := (mk_eq_zero ρ N v).mp (Subsingleton.elim _ _)
  have hev : ∀ x ∈ relations ρ N, ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      Compact.averageMap ρ hρ K hK (ρ (g ^ s) x) = 0 := by
    intro x hx
    rw [relations_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨n, w⟩, rfl⟩ := hw
      obtain ⟨r, hr⟩ := h.eventually_mem hexhaust hMN n
      refine ⟨r, fun s hs => ?_⟩
      rw [map_sub, map_sub, sub_eq_zero]
      calc
        _ = Compact.averageMap ρ hρ K hK
            (ρ (g ^ s * n.val * (g ^ s)⁻¹) (ρ (g ^ s) w)) := by
          congr 1
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 1
          group
        _ = _ := averageMap_apply_of_mem ρ hρ K hK (hr s hs) _
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
  obtain ⟨r, hr⟩ := hev v hrel
  refine ⟨r, ?_⟩
  rw [compressionMap_pow ρ hρ hK hfactor h r v hv, compressionMap_apply]
  exact hr r le_rfl

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Jacquet nonvanishing from injective compression.** Let `g` be a weak Iwahori
contraction for a factorized compact open subgroup `K` relative to `(N, M, Nbar)`, with
each element of `N` carried into `K` by a power of `g`. Let `P` be a
property of linear maps from a finite-dimensional space `W` with values in the
`K`-fixed vectors, stable under composition with the compression by `g`, and such
that this composition is zero only for the zero map. If some nonzero map has `P`, then
the Jacquet module along `N` is nonzero. -/
theorem not_subsingleton_coinvariants_of_compression (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {N M Nbar : Subgroup G} {g : G} (h : IsWeakIwahoriContraction K N M Nbar g)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (hexhaust : ∀ x ∈ N, ∃ r : ℕ, g ^ r * x * (g ^ r)⁻¹ ∈ K)
    (hMN : M ≤ Subgroup.normalizer N) [FiniteDimensional ℂ W]
    (P : (W →ₗ[ℂ] V) → Prop)
    (hrange : ∀ f, P f → ∀ w, f w ∈ fixedVectors ρ K.toSubgroup)
    (hstep : ∀ f, P f → P ((compressionMap ρ hρ K hK g).comp f))
    (hinj : ∀ f, P f → (compressionMap ρ hρ K hK g).comp f = 0 → f = 0)
    (f : W →ₗ[ℂ] V) (hf : P f) (hf0 : f ≠ 0) :
    ¬ Subsingleton (Coinvariants ρ N) := by
  intro hN
  classical
  let A := compressionMap ρ hρ K hK g
  let b := Module.finBasis ℂ W
  have hzero : ∀ i, ∃ r : ℕ, (A ^ r) (f (b i)) = 0 := fun i =>
    exists_pow_compressionMap_eq_zero ρ hρ hK h hfactor hexhaust hMN hN _ (hrange f hf (b i))
  choose r hr using hzero
  let R := Finset.univ.sup r
  have hP : ∀ t : ℕ, P ((A ^ t).comp f) := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
      exact hf
    | succ t ih =>
      have := hstep _ ih
      rwa [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]
  have hR : (A ^ R).comp f = 0 := by
    apply b.ext
    intro i
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := r) (Finset.mem_univ i))
    change (A ^ R) (f (b i)) = 0
    rw [show R = c + r i by omega, pow_add, Module.End.mul_apply, hr i, map_zero]
  have hdown : ∀ t : ℕ, (A ^ t).comp f = 0 → f = 0 := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
      exact id
    | succ t ih =>
      intro ht
      apply ih
      apply hinj _ (hP t)
      rwa [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc] at ht
  exact hf0 (hdown R hR)

end Langlands.Jacquet
