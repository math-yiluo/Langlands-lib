import Langlands.BushnellKutzko.SplitTypeJacquet.CoarseContraction

/-! # Jacquet nonvanishing along the coarse corner from a vanishing test map

Let `K = J1` and let `g` be the coarse contraction. For a type `ρ` of `J0`, trivial on `J1`,
compression by `g` preserves the intertwiners from `ρ`. It is injective on them as soon as each
nonzero intertwiner `f` admits a linear retraction `ψ` that is `J1`-invariant on the translates
of the image of `f` by the integral late-early corner and kills those translates by corners not
congruent to zero. The criterion of `TypeJacquetCompression` then gives a nonzero Jacquet module
along the late-early corner. -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {blk : ι → ℕ} {j : ℕ} {ϖ : 𝒪[F]}

omit [Fintype ι] [DecidableEq ι] in
theorem val_uniformizer_inv_mul_le_one (hϖ : Irreducible ϖ) {x : F} (hx : valuation F x < 1) :
    valuation F ((ϖ : F)⁻¹ * x) ≤ 1 := by
  have hmem : (⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩ : 𝒪[F]) ∈
      IsLocalRing.maximalIdeal 𝒪[F] :=
    (valuation F).mem_maximalIdeal_iff.mpr hx
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hx' : x = (y : F) * ϖ := by
    have := congrArg Subtype.val hy
    simpa using this.symm
  rw [hx', mul_comm (y : F), ← mul_assoc, inv_mul_cancel₀ (uniformizer_ne_zero' hϖ), one_mul]
  exact y.2

variable (blk j) in
/-- The element of the late-early corner with the given entries. -/
abbrev upperC (Z : Matrix (Late blk j) (Early blk j) F) : GL ι F :=
  (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Z))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_inv_conj_upperC (hϖ : Irreducible ϖ) (Y : Matrix (Late blk j) (Early blk j) F) :
    (aElt blk j hϖ)⁻¹ * upperC blk j Y * aElt blk j hϖ = upperC blk j ((ϖ : F)⁻¹ • Y) := by
  have h := aElt_conj_upper (blk := blk) (j := j) hϖ ((ϖ : F)⁻¹ • Y)
  rw [smul_smul, mul_inv_cancel₀ (uniformizer_ne_zero' hϖ), one_smul] at h
  show (aElt blk j hϖ)⁻¹ * (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) *
      aElt blk j hϖ = (coarseReindex F blk j).symm
        (upperHom (Multiplicative.ofAdd ((ϖ : F)⁻¹ • Y)))
  rw [← h]
  group

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL ι F) V) (hπ : IsSmooth π)
  (K : OpenSubgroup (GL ι F)) (hK : IsCompact (K : Set (GL ι F)))

include hπ in
/-- Averaging over `K` commutes with an element normalizing `K`. -/
theorem averageMap_apply_normalizing (m : GL ι F) (hm : ∀ x, x ∈ K ↔ m⁻¹ * x * m ∈ K)
    (x : V) :
    Compact.averageMap π hπ K hK (π m x) = π m (Compact.averageMap π hπ K hK x) := by
  have hEq : conjOpenSubgroup m K = K := by
    ext y
    rw [mem_conjOpenSubgroup]
    exact (hm y).symm
  have hgen : ∀ (L : OpenSubgroup (GL ι F)) (hL : IsCompact (L : Set (GL ι F))), L = K →
      Compact.averageMap π hπ L hL = Compact.averageMap π hπ K hK := by
    rintro L hL rfl; rfl
  rw [← averageMap_conj π hπ m K hK (isCompact_conjOpenSubgroup m K hK) x, hgen _ _ hEq]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_J1_iff_conj {m : GL ι F} (hm : m ∈ J0 F blk) (x : GL ι F) :
    x ∈ J1 F blk ↔ m⁻¹ * x * m ∈ J1 F blk := by
  constructor
  · intro hx
    simpa using conj_mem_J1 ((J0 F blk).inv_mem hm) hx
  · intro hx
    simpa [mul_assoc] using conj_mem_J1 hm hx

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

include hπ hK in
/-- **Compression preserves type intertwiners.** -/
theorem compression_intertwines (hϖ : Irreducible ϖ) (hKJ : K.toSubgroup = J1 F blk)
    (ρ : Representation ℂ (J0 F blk) W)
    (hρ1 : ∀ x : J0 F blk, (x : GL ι F) ∈ J1 F blk → ρ x = 1)
    (g : W →ₗ[ℂ] V) (hg : ∀ (x : J0 F blk) (w : W), g (ρ x w) = π x (g w))
    (x : J0 F blk) (w : W) :
    compressionMap π hπ K hK (aElt blk j hϖ) (g (ρ x w)) =
      π x (compressionMap π hπ K hK (aElt blk j hϖ) (g w)) := by
  have hJK : ∀ y, y ∈ K ↔ y ∈ J1 F blk := fun y => by
    change y ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hnorm : ∀ y ∈ J0 F blk, ∀ z, z ∈ K ↔ y⁻¹ * z * y ∈ K := by
    intro y hy z
    rw [hJK, hJK]
    exact mem_J1_iff_conj hy z
  obtain ⟨l, ⟨hl1, _⟩, m, ⟨hm0, hm2⟩, u, ⟨hu1, _⟩, hx⟩ := coarse_factor (j := j) x.2
  have hρx : ρ x = ρ ⟨m, hm0⟩ := by
    have hx' : x = ⟨l, J1_le_J0 hl1⟩ * ⟨m, hm0⟩ * ⟨u, J1_le_J0 hu1⟩ := Subtype.ext hx
    rw [hx', map_mul, map_mul, hρ1 ⟨l, J1_le_J0 hl1⟩ hl1, hρ1 ⟨u, J1_le_J0 hu1⟩ hu1, one_mul,
      mul_one]
  have hcomm : (aElt blk j hϖ) * m = m * aElt blk j hϖ := by
    have := aElt_inv_conj_levi (blk := blk) (j := j) hϖ hm2
    calc aElt blk j hϖ * m = aElt blk j hϖ * ((aElt blk j hϖ)⁻¹ * m * aElt blk j hϖ) := by
          rw [this]
      _ = m * aElt blk j hϖ := by group
  set z := compressionMap π hπ K hK (aElt blk j hϖ) (g w) with hz
  have hzfix : z ∈ fixedVectors π K.toSubgroup :=
    Compact.averageMap_mem_fixedVectors π hπ K hK _
  have hmz : π m z ∈ fixedVectors π K.toSubgroup := by
    intro k
    change π k (π m z) = π m z
    have hk : m⁻¹ * k * m ∈ K := (hnorm m hm0 k).mp k.property
    calc π k (π m z) = π m (π (m⁻¹ * k * m) z) := by
          simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = π m z := by
          have : π (m⁻¹ * k * m) z = z := hzfix ⟨_, hk⟩
          rw [this]
  rw [hρx, hg, compressionMap_apply]
  have e1 : π (aElt blk j hϖ) (π m (g w)) = π m (π (aElt blk j hϖ) (g w)) := by
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  rw [show ((⟨m, hm0⟩ : J0 F blk) : GL ι F) = m from rfl, e1,
    averageMap_apply_normalizing π hπ K hK m (hnorm m hm0), ← compressionMap_apply, ← hz]
  rw [show (x : GL ι F) = l * m * u from hx, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply]
  have hu : π u z = z := hzfix ⟨u, (hJK u).mpr hu1⟩
  have hl : π l (π m z) = π m z := hmz ⟨l, (hJK l).mpr hl1⟩
  rw [hu, hl]

include hπ hK in
/-- **The vanishing test.** Let `f` take values fixed by `J1` and let `ψ` be a linear
retraction of `f`. Suppose that `ψ` is `J1`-invariant on the translates of the image of `f` by
integral late-early corners and kills the translates by integral corners not congruent to zero.
If compression by the coarse contraction kills `f`, then the source of `f` is zero. -/
theorem eq_zero_of_compression_eq_zero (hϖ : Irreducible ϖ) (hKJ : K.toSubgroup = J1 F blk)
    (f : W →ₗ[ℂ] V) (hf1 : ∀ h ∈ J1 F blk, ∀ w, π h (f w) = f w)
    (ψ : V →ₗ[ℂ] W) (hψf : ∀ w, ψ (f w) = w)
    (hinv : ∀ h ∈ J1 F blk, ∀ Z : Matrix (Late blk j) (Early blk j) F,
      (∀ a b, valuation F (Z a b) ≤ 1) → ∀ w,
        ψ (π h (π (upperC blk j Z) (f w))) = ψ (π (upperC blk j Z) (f w)))
    (hvan : ∀ Z : Matrix (Late blk j) (Early blk j) F, (∀ a b, valuation F (Z a b) ≤ 1) →
      (¬ ∀ a b, valuation F (Z a b) < 1) → ∀ w, ψ (π (upperC blk j Z) (f w)) = 0)
    (h0 : (compressionMap π hπ K hK (aElt blk j hϖ)).comp f = 0) (w : W) : w = 0 := by
  classical
  have hJK : ∀ y, y ∈ K ↔ y ∈ J1 F blk := fun y => by
    change y ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hcon := coarse_isCompressionContraction (j := j) hϖ K hKJ
  set a := aElt blk j hϖ with ha
  set v := f w with hv
  let K'' := conjOpenSubgroup a⁻¹ K
  have hK'' : IsCompact (K'' : Set (GL ι F)) := isCompact_conjOpenSubgroup a⁻¹ K hK
  -- the average of `v` over `K''` vanishes
  have havg : Compact.averageMap π hπ K'' hK'' v = 0 := by
    have hc : Compact.averageMap π hπ K hK (π a v) = 0 := by
      have := LinearMap.congr_fun h0 w
      simpa [compressionMap_apply] using this
    have := averageMap_conj π hπ a⁻¹ K hK hK'' (π a v)
    rw [hc, map_zero, Representation.inv_self_apply] at this
    exact this
  -- every point of the orbit is `v` or is killed by `ψ`
  have hpt : ∀ k : K''.toSubgroup, π k.val v = v ∨ ψ (π k.val v) = 0 := by
    intro k
    have hk' : a * k.val * a⁻¹ ∈ J1 F blk := by
      have := (mem_conjOpenSubgroup a⁻¹ K k.val).mp k.property
      rw [inv_inv] at this
      exact (hJK _).mp this
    obtain ⟨l, ⟨hl1, hl2⟩, m, ⟨_, hm2⟩, u, ⟨hu1, ⟨Y, hY⟩⟩, hlmu⟩ :=
      coarse_factor (j := j) (J1_le_J0 hk')
    have hm1 : m ∈ J1 F blk := by
      have : m = l⁻¹ * (a * k.val * a⁻¹) * u⁻¹ := by rw [hlmu]; group
      rw [this]
      exact (J1 F blk).mul_mem ((J1 F blk).mul_mem ((J1 F blk).inv_mem hl1) hk')
        ((J1 F blk).inv_mem hu1)
    have hl' : a⁻¹ * l * a ∈ K := (hcon.lower l ⟨(hJK l).mpr hl1, hl2⟩).1
    have hm' : a⁻¹ * m * a ∈ K := (hcon.levi m ⟨(hJK m).mpr hm1, hm2⟩).1
    set h := (a⁻¹ * l * a) * (a⁻¹ * m * a) with hh
    have hhJ : h ∈ J1 F blk := (hJK h).mp (K.mul_mem hl' hm')
    have hu : u = upperC blk j (Multiplicative.toAdd Y) := by
      show u = (coarseReindex F blk j).symm
        (upperHom (Multiplicative.ofAdd (Multiplicative.toAdd Y)))
      rw [ofAdd_toAdd, hY]
      simp
    have hYlt : ∀ p q, valuation F (Multiplicative.toAdd Y p q) < 1 := by
      intro p q
      rw [upper_entry (Y := Multiplicative.toAdd Y) hY]
      have hp := p.2
      have hq := q.2
      change ¬ j ≤ blk q.1 at hq
      have hpq : p.1 ≠ q.1 := fun h => hq (h ▸ hp)
      have := (hu1.2 p.1 q.1).2 (by omega)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hpq, sub_zero] at this
    set Z := (ϖ : F)⁻¹ • Multiplicative.toAdd Y with hZ
    have hZint : ∀ p q, valuation F (Z p q) ≤ 1 := by
      intro p q
      rw [hZ, Matrix.smul_apply, smul_eq_mul]
      exact val_uniformizer_inv_mul_le_one hϖ (hYlt p q)
    have hn : a⁻¹ * upperC blk j (Multiplicative.toAdd Y) * a = upperC blk j Z := by
      rw [ha]; exact aElt_inv_conj_upperC hϖ _
    have hkeq : k.val = h * upperC blk j Z := by
      have e : k.val = a⁻¹ * (a * k.val * a⁻¹) * a := by group
      rw [e, hlmu, hh, ← hn, hu]
      group
    by_cases hZlt : ∀ p q, valuation F (Z p q) < 1
    · left
      have hnJ : upperC blk j Z ∈ J1 F blk := coarse_upper_mem_J1 hZlt
      rw [hkeq]
      exact hf1 _ ((J1 F blk).mul_mem hhJ hnJ) w
    · right
      rw [hkeq, map_mul, Module.End.mul_apply, hinv h hhJ Z hZint w]
      exact hvan Z hZint hZlt w
  -- conclude with the orbit mean
  let τ := π.comp K''.toSubgroup.subtype
  have := Compact.finite_orbit_of_smooth π hπ K'' hK'' v
  let := Fintype.ofFinite (Compact.orbit τ v)
  have hmean : Compact.averageMap π hπ K'' hK'' v =
      Compact.finiteMean (fun x : Compact.orbit τ v => x.val) :=
    Compact.orbitMean_eq_finiteMean τ v
  rw [hmean] at havg
  have hψ := congrArg ψ havg
  rw [map_zero] at hψ
  unfold Compact.finiteMean at hψ
  rw [map_smul, map_sum] at hψ
  let v₀ : Compact.orbit τ v := ⟨v, ⟨1, by simp [τ]⟩⟩
  have hsum : ∑ x : Compact.orbit τ v, ψ x.val = w := by
    rw [Finset.sum_eq_single v₀]
    · exact hψf w
    · intro x _ hx
      obtain ⟨k, hk⟩ := x.property
      rcases hpt k with h | h
      · exfalso
        apply hx
        apply Subtype.ext
        change x.val = v
        rw [← hk]
        exact h
      · rw [← hk]
        exact h
    · intro h
      exact absurd (Finset.mem_univ v₀) h
  rw [hsum] at hψ
  have hcard : (Fintype.card (Compact.orbit τ v) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact (smul_eq_zero.mp hψ).resolve_left hcard

include hπ hK in
/-- **Jacquet nonvanishing along the late-early corner.** Let `ρ` be a finite-dimensional
representation of `J0`, trivial on `J1 = K`, with a nonzero intertwiner into `π`. Suppose each
nonzero intertwiner `g` from `ρ` admits a linear retraction `ψ` passing the vanishing test of
`eq_zero_of_compression_eq_zero`. Then the Jacquet module of `π` along `coarseN` is nonzero. -/
theorem not_subsingleton_coinvariants_coarseN (hϖ : Irreducible ϖ)
    (hKJ : K.toSubgroup = J1 F blk) [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (J0 F blk) W)
    (hρ1 : ∀ x : J0 F blk, (x : GL ι F) ∈ J1 F blk → ρ x = 1)
    (htest : ∀ g : W →ₗ[ℂ] V, (∀ (x : J0 F blk) (w : W), g (ρ x w) = π x (g w)) → g ≠ 0 →
      ∃ ψ : V →ₗ[ℂ] W, (∀ w, ψ (g w) = w) ∧
        (∀ h ∈ J1 F blk, ∀ Z : Matrix (Late blk j) (Early blk j) F,
          (∀ a b, valuation F (Z a b) ≤ 1) → ∀ w,
            ψ (π h (π (upperC blk j Z) (g w))) = ψ (π (upperC blk j Z) (g w))) ∧
        (∀ Z : Matrix (Late blk j) (Early blk j) F, (∀ a b, valuation F (Z a b) ≤ 1) →
          (¬ ∀ a b, valuation F (Z a b) < 1) → ∀ w, ψ (π (upperC blk j Z) (g w)) = 0))
    (f : W →ₗ[ℂ] V) (hf : ∀ (x : J0 F blk) (w : W), f (ρ x w) = π x (f w)) (hf0 : f ≠ 0) :
    ¬ Subsingleton (Coinvariants π (coarseN F blk j)) := by
  have hJK : ∀ x, x ∈ K ↔ x ∈ J1 F blk := fun x => by
    change x ∈ K.toSubgroup ↔ _; rw [hKJ]
  let P : (W →ₗ[ℂ] V) → Prop := fun g => ∀ (x : J0 F blk) (w : W), g (ρ x w) = π x (g w)
  have hfix : ∀ g, P g → ∀ h ∈ J1 F blk, ∀ w, π h (g w) = g w := by
    intro g hg h hh w
    rw [← hg ⟨h, J1_le_J0 hh⟩, hρ1 _ hh]
    rfl
  have hrange : ∀ g, P g → ∀ w, g w ∈ fixedVectors π K.toSubgroup := by
    intro g hg w k
    exact hfix g hg k.val ((hJK k.val).mp k.property) w
  refine not_subsingleton_coinvariants_of_compressionContraction π hπ hK
    (coarse_isCompressionContraction (j := j) hϖ K hKJ) coarseM_le_normalizer P hrange ?_ ?_ f hf
    hf0
  · intro g hg x w
    exact compression_intertwines π hπ K hK hϖ hKJ ρ hρ1 g hg x w
  · intro g hg h0
    by_contra hg0
    obtain ⟨ψ, hψ, hinv, hvan⟩ := htest g hg hg0
    apply hg0
    ext w
    rw [eq_zero_of_compression_eq_zero π hπ K hK hϖ hKJ g (hfix g hg) ψ hψ hinv hvan h0 w,
      map_zero, LinearMap.zero_apply]

end Langlands.BushnellKutzko.SplitTypeJacquet
