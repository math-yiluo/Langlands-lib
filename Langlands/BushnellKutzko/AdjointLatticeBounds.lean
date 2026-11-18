import Langlands.BushnellKutzko.AdjointExactnessStatement

/-! # Bounds for the adjoint lattice filtration -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

/-- Restricting to the zeroth lattice embeds the order into a finite module. -/
theorem LatticeChain.endFiltration_zero_fg : (P 0).FG := by
  let L := 𝓛.lattice 0
  have : L.IsLattice F := 𝓛.isLattice 0
  let f : P 0 →ₗ[𝒪[F]] Module.End 𝒪[F] L :=
    { toFun := fun x => (x.val.restrictScalars 𝒪[F]).restrict fun v hv => by
        simpa using x.prop 0 v hv
      map_add' := fun x y => by ext v; rfl
      map_smul' := fun c x => by ext v; rfl }
  have hf : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    apply LinearMap.ext_on (𝓛.isLattice 0).span_eq_top
    intro v hv
    exact congrArg (fun g : Module.End 𝒪[F] L => (g ⟨v, hv⟩ : V)) heq
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective f hf)

variable {ϖ : 𝒪[F]}

/-- One period is multiplication by the chosen uniformizer. -/
theorem LatticeChain.uniformizer_lattice_mem_iff (hϖ : Irreducible ϖ) (i : ℤ) (v : V) :
    (ϖ : F) • v ∈ 𝓛.lattice (i + 𝓛.period) ↔ v ∈ 𝓛.lattice i := by
  rw [𝓛.lattice_add_period, jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨?_, fun hv => ⟨v, hv, rfl⟩⟩
  rintro ⟨w, hw, heq⟩
  exact (smul_right_injective V h0 heq) ▸ hw

/-- The same period formula holds in the endomorphism filtration. -/
theorem LatticeChain.uniformizer_end_mem_iff (hϖ : Irreducible ϖ) (n : ℤ) (x : A) :
    (ϖ : F) • x ∈ P (n + 𝓛.period) ↔ x ∈ P n := by
  simp only [𝓛.mem_endFiltration, LinearMap.smul_apply, ← add_assoc,
    𝓛.uniformizer_lattice_mem_iff hϖ]

/-- Powers of the uniformizer move an endomorphism by the corresponding number of periods. -/
theorem LatticeChain.uniformizer_pow_end_mem_iff (hϖ : Irreducible ϖ) (t : ℕ) (n : ℤ) (x : A) :
    (ϖ : F) ^ t • x ∈ P (n + t * 𝓛.period) ↔ x ∈ P n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, pow_succ', mul_smul,
      𝓛.uniformizer_end_mem_iff hϖ, ih]

/-- A vector belonging to every lattice is zero, by Krull intersection on `L₀`. -/
theorem LatticeChain.lattice_eq_zero_of_forall {v : V} (hv : ∀ i : ℤ, v ∈ 𝓛.lattice i) :
    v = 0 := by
  let L := 𝓛.lattice 0
  have : L.IsLattice F := 𝓛.isLattice 0
  let w : L := ⟨v, hv 0⟩
  have hpow : ∀ t : ℕ, 𝓛.lattice ((t : ℤ) * 𝓛.period) = 𝓂[F] ^ t • L := by
    intro t
    induction t with
    | zero => simp [L]
    | succ t ih =>
      rw [Nat.cast_succ, add_mul, one_mul, 𝓛.lattice_add_period,
        jacobson_integer_eq_maximalIdeal, ih, pow_succ', mul_smul]
  have hw : w ∈ ⨅ t : ℕ, 𝓂[F] ^ t • (⊤ : Submodule 𝒪[F] L) := by
    rw [Submodule.mem_iInf]
    intro t
    have hm : v ∈ 𝓂[F] ^ t • L := hpow t ▸ hv _
    have hmap : (𝓂[F] ^ t • (⊤ : Submodule 𝒪[F] L)).map L.subtype = 𝓂[F] ^ t • L := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← hmap] at hm
    obtain ⟨u, hu, heq⟩ := hm
    exact (Subtype.ext heq : u = w) ▸ hu
  have hbot : (⨅ t : ℕ, 𝓂[F] ^ t • (⊤ : Submodule 𝒪[F] L)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := 𝓂[F]) (M := L)
      (Ideal.IsPrime.ne_top inferInstance)
  rw [hbot, Submodule.mem_bot] at hw
  exact congrArg (fun z : L => (z : V)) hw

/-- The endomorphism filtration is separated. -/
theorem LatticeChain.endFiltration_eq_zero_of_forall {x : A} (hx : ∀ n : ℤ, x ∈ P n) :
    x = 0 := by
  apply LinearMap.ext_on (𝓛.isLattice 0).span_eq_top
  intro v hv
  exact 𝓛.lattice_eq_zero_of_forall fun n => by simpa only [zero_add] using hx n 0 v hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The F-linear commutator and its restricted form have the same values. -/
theorem adjointMap_restrict_apply (b x : A) : adjointMap 𝒪[F] b x = adjointMap F b x := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element of an adjoint lattice is integral and has commutator of the specified depth. -/
theorem mem_adjointLattice_iff {b : A} {n : ℤ} {x : A} :
    x ∈ adjointLattice 𝓛 b n ↔ x ∈ P 0 ∧ adjointMap F b x ∈ P n := Iff.rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Membership in a centralizer lattice means integral depth and vanishing commutator. -/
theorem mem_centralizerLattice_iff {b : A} {n : ℤ} {x : A} :
    x ∈ centralizerLattice 𝓛 b n ↔ x ∈ P n ∧ adjointMap F b x = 0 := Iff.rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The adjoint lattices decrease with depth. -/
theorem adjointLattice_antitone (b : A) : Antitone (adjointLattice 𝓛 b) := by
  intro m n hmn x hx
  exact ⟨hx.1, 𝓛.endFiltration_antitone hmn hx.2⟩

/-- The intersection of all adjoint lattices is the integral centralizer. -/
theorem iInf_adjointLattice (b : A) :
    (⨅ k : ℤ, adjointLattice 𝓛 b k) = centralizerLattice 𝓛 b 0 := by
  ext x
  rw [Submodule.mem_iInf]
  change (∀ k, x ∈ P 0 ∧ adjointMap F b x ∈ P k) ↔ x ∈ P 0 ∧ adjointMap F b x = 0
  constructor
  · intro h
    exact ⟨(h 0).1, 𝓛.endFiltration_eq_zero_of_forall fun k => (h k).2⟩
  · rintro ⟨hx, hb⟩ k
    exact ⟨hx, hb ▸ (P k).zero_mem⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A linear right inverse on the image extends to the ambient vector space. -/
private theorem adjointSection (b : A) :
    ∃ f : A →ₗ[F] A, ∀ x, adjointMap F b (f (adjointMap F b x)) = adjointMap F b x := by
  let a := adjointMap F b
  obtain ⟨g, hg⟩ := a.range.subtype.exists_leftInverse_of_injective a.range.ker_subtype
  obtain ⟨r, hr⟩ := a.rangeRestrict.exists_rightInverse_of_surjective a.range_rangeRestrict
  refine ⟨r.comp g, fun x => ?_⟩
  have h₁ : g (a x) = a.rangeRestrict x := LinearMap.congr_fun hg (a.rangeRestrict x)
  have h₂ : a (r (a.rangeRestrict x)) = a x :=
    congrArg Subtype.val (LinearMap.congr_fun hr (a.rangeRestrict x))
  change a (r (g (a x))) = a x
  rwa [h₁]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A single power of a scalar suffices for all generators of a finite submodule. -/
private theorem exists_pow_map_mem_of_fg {W : Type*} [AddCommGroup W] [Module F W]
    {M N : Submodule 𝒪[F] W} (hM : M.FG)
    (f : W →ₗ[F] W) (c : 𝒪[F]) (h : ∀ x ∈ M, ∃ n : ℕ, c ^ n • f x ∈ N) :
    ∃ n : ℕ, ∀ x ∈ M, c ^ n • f x ∈ N := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hgen : ∀ v ∈ s, ∃ n : ℕ, c ^ n • f v ∈ N := fun v hv =>
    h v (hs ▸ Submodule.subset_span hv)
  have hmono {v : W} {n m : ℕ} (hₙ : c ^ n • f v ∈ N) (hnm : n ≤ m) :
      c ^ m • f v ∈ N := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [add_comm n d, pow_add, mul_smul]
    exact N.smul_mem _ hₙ
  have hs' : ∃ n : ℕ, ∀ v ∈ s, c ^ n • f v ∈ N := by
    choose depth hdepth using hgen
    let n := s.attach.sup fun v => depth v v.prop
    exact ⟨n, fun v hv => hmono (hdepth v hv) (Finset.le_sup (f := fun v : s => depth v v.prop)
      (Finset.mem_attach s ⟨v, hv⟩))⟩
  obtain ⟨n, hn⟩ := hs'
  refine ⟨n, ?_⟩
  let g := c ^ n • f.restrictScalars 𝒪[F]
  have hle : M ≤ N.comap g := by
    rw [← hs, Submodule.span_le]
    exact hn
  exact hle

private theorem exists_pow_mul_integer (hϖ : Irreducible ϖ) (c : F) :
    ∃ (n : ℕ) (d : 𝒪[F]), (ϖ : F) ^ n * c = d := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective 𝒪[F] c
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hb) hϖ
  have hϖ₀ : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu : ((u : 𝒪[F]) : F) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  refine ⟨n, (↑u⁻¹ : 𝒪[F]) * a, ?_⟩
  have hinv : (((↑u⁻¹ : 𝒪[F]) : F)) * ((u : 𝒪[F]) : F) = 1 := by
    exact congrArg (fun x : 𝒪[F] => (x : F)) u.inv_mul
  change (ϖ : F) ^ n * ((a : F) / (((u : 𝒪[F]) : F) * (ϖ : F) ^ n)) =
    (((↑u⁻¹ : 𝒪[F]) : F)) * (a : F)
  rw [← mul_div_assoc, div_eq_iff (mul_ne_zero hu (pow_ne_zero _ hϖ₀))]
  linear_combination -(ϖ : F) ^ n * (a : F) * hinv

/-- Multiplying a vector by a sufficiently large power puts it in a prescribed lattice. -/
theorem LatticeChain.exists_uniformizer_pow_mem_lattice (hϖ : Irreducible ϖ) (i : ℤ) (v : V) :
    ∃ t : ℕ, (ϖ : F) ^ t • v ∈ 𝓛.lattice i := by
  let L := 𝓛.lattice i
  let S : Submodule F V :=
    { carrier := {v | ∃ t : ℕ, (ϖ : F) ^ t • v ∈ L}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        rw [smul_add]
        apply L.add_mem
        · rw [add_comm m n, pow_add, mul_smul]
          exact L.smul_mem (ϖ ^ n) hm
        · rw [pow_add, mul_smul]
          exact L.smul_mem (ϖ ^ m) hn
      smul_mem' := by
        rintro c x ⟨m, hm⟩
        obtain ⟨n, d, hd⟩ := exists_pow_mul_integer hϖ c
        refine ⟨m + n, ?_⟩
        rw [pow_add, smul_smul, mul_assoc, hd, mul_comm, mul_smul]
        exact L.smul_mem d hm }
  have hle : Submodule.span F (L : Set V) ≤ S :=
    Submodule.span_le.mpr fun _ hx => ⟨0, by simpa using hx⟩
  rw [(𝓛.isLattice i).span_eq_top] at hle
  exact hle (Submodule.mem_top (x := v))

/-- The vector lattices exhaust the ambient space. -/
theorem LatticeChain.exists_lattice_depth (hϖ : Irreducible ϖ) (v : V) :
    ∃ i : ℤ, v ∈ 𝓛.lattice i := by
  obtain ⟨t, ht⟩ := 𝓛.exists_uniformizer_pow_mem_lattice hϖ 0 v
  have hshift (j : ℤ) (n : ℕ) :
      (ϖ : F) ^ n • v ∈ 𝓛.lattice (j + n * 𝓛.period) ↔ v ∈ 𝓛.lattice j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, pow_succ', mul_smul,
        𝓛.uniformizer_lattice_mem_iff hϖ, ih]
  refine ⟨-(t : ℤ) * 𝓛.period, (hshift _ t).mp ?_⟩
  simpa only [neg_mul, neg_add_cancel] using ht

/-- Clearing a scalar denominator on the first period controls the entire chain. -/
theorem LatticeChain.exists_uniformizer_pow_mem_endFiltration (hϖ : Irreducible ϖ)
    (x : A) (m : ℤ) : ∃ t : ℕ, (ϖ : F) ^ t • x ∈ P m := by
  let e : ℤ := 𝓛.period
  have he : 0 < e := Int.natCast_pos.mpr 𝓛.period_pos
  obtain ⟨t, ht⟩ := exists_pow_map_mem_of_fg (𝓛.isLattice 0).fg x ϖ
    fun v _ => 𝓛.exists_uniformizer_pow_mem_lattice hϖ (m + e) (x v)
  let y := (ϖ : F) ^ t • x
  let H (i : ℤ) := ∀ v ∈ 𝓛.lattice i, y v ∈ 𝓛.lattice (i + m)
  have hbase (i : ℤ) (hi : 0 ≤ i) (hie : i < e) : H i := by
    intro v hv
    have hmem : y v ∈ 𝓛.lattice (m + e) := ht v (𝓛.antitone hi hv)
    exact 𝓛.antitone (show i + m ≤ m + e by omega) hmem
  have hper (i : ℤ) : H (i + e) ↔ H i := by
    constructor
    · intro h v hv
      apply (𝓛.uniformizer_lattice_mem_iff hϖ (i + m) (y v)).mp
      rw [← y.map_smul, add_right_comm i m e]
      exact h _ ((𝓛.uniformizer_lattice_mem_iff hϖ i v).mpr hv)
    · intro h v hv
      let w := (ϖ : F)⁻¹ • v
      have hϖ₀ : (ϖ : F) ≠ 0 := fun hz => hϖ.ne_zero (Subtype.ext hz)
      have hw : (ϖ : F) • w = v := smul_inv_smul₀ hϖ₀ v
      have hwi := (𝓛.uniformizer_lattice_mem_iff hϖ i w).mp (hw.symm ▸ hv)
      rw [← hw, y.map_smul, add_right_comm i e m]
      exact (𝓛.uniformizer_lattice_mem_iff hϖ (i + m) (y w)).mpr (h w hwi)
  refine ⟨t, 𝓛.mem_endFiltration.mpr fun i => ?_⟩
  have hmod (q : ℤ) : H (i % e + e * q) := by
    refine Int.inductionOn' q 0 ?_ ?_ ?_
    · have hi := hbase (i % e) (Int.emod_nonneg _ he.ne') (Int.emod_lt_of_pos _ he)
      simpa only [mul_zero, add_zero] using hi
    · intro q _ ih
      rwa [mul_add, mul_one, ← add_assoc, hper]
    · intro q _ ih
      rw [mul_sub, mul_one, ← add_sub_assoc]
      apply (hper _).mp
      simpa only [sub_add_cancel] using ih
  have hi := hmod (i / e)
  rwa [Int.emod_add_mul_ediv] at hi

/-- The first full period of the endomorphism filtration is the uniformizer times step zero. -/
theorem LatticeChain.maximalIdeal_smul_endFiltration_zero (hϖ : Irreducible ϖ) :
    𝓂[F] • P 0 = P (𝓛.period : ℤ) := by
  rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  have hϖ₀ : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (ϖ : F) • y ∈ P (𝓛.period : ℤ)
    simpa only [zero_add] using (𝓛.uniformizer_end_mem_iff hϖ 0 y).mpr hy
  · intro hx
    let y := (ϖ : F)⁻¹ • x
    have hy : (ϖ : F) • y = x := smul_inv_smul₀ hϖ₀ x
    refine ⟨y, (𝓛.uniformizer_end_mem_iff hϖ 0 y).mp ?_, hy⟩
    simpa only [zero_add, hy] using hx

/-- Clearing denominators in the filtration bounds the image of a linear map. -/
theorem LatticeChain.exists_endFiltration_mapsTo_one (hϖ : Irreducible ϖ)
    (hclear : ∀ x : A, ∃ t : ℕ, (ϖ : F) ^ t • x ∈ P 0) (f : A →ₗ[F] A) :
    ∃ n : ℤ, Set.MapsTo f (P n) (P 1) := by
  have hlocal (x : A) : ∃ t : ℕ, ϖ ^ t • f x ∈ P 1 := by
    obtain ⟨t, ht⟩ := hclear (f x)
    refine ⟨t + 1, 𝓛.endFiltration_antitone (b := (𝓛.period : ℤ)) (by
      exact_mod_cast 𝓛.period_pos) ?_⟩
    have h := (𝓛.uniformizer_end_mem_iff hϖ 0 _).2 ht
    change (ϖ : F) ^ (t + 1) • f x ∈ P (𝓛.period : ℤ)
    simpa only [pow_succ', mul_smul, zero_add] using h
  obtain ⟨t, ht⟩ := exists_pow_map_mem_of_fg 𝓛.endFiltration_zero_fg f ϖ (fun x _ => hlocal x)
  refine ⟨(t : ℤ) * 𝓛.period, ?_⟩
  intro x hx
  let y := ((ϖ : F) ^ t)⁻¹ • x
  have hy : (ϖ : F) ^ t • y = x := by
    have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    simp [y, smul_smul, h0]
  have hy0 : y ∈ P 0 := (𝓛.uniformizer_pow_end_mem_iff hϖ t 0 y).1 (by simpa [hy] using hx)
  have hz := ht y hy0
  change (ϖ : F) ^ t • f y ∈ P 1 at hz
  rwa [← f.map_smul, hy] at hz

/-- The critical-index set is bounded above. -/
theorem criticalIndexSet_bddAbove (b : A) (hϖ : Irreducible ϖ)
    (hclear : ∀ x : A, ∃ t : ℕ, (ϖ : F) ^ t • x ∈ P 0) :
    BddAbove (criticalIndexSet 𝓛 b) := by
  obtain ⟨f, hf⟩ := adjointSection b
  obtain ⟨n, hn⟩ := 𝓛.exists_endFiltration_mapsTo_one hϖ hclear f
  have hle : adjointLattice 𝓛 b n ≤ centralizerLattice 𝓛 b 0 ⊔ P 1 := by
    intro x hx
    obtain ⟨hx0, hx⟩ : x ∈ P 0 ∧ adjointMap F b x ∈ P n := hx
    have hy := hn hx
    have hy0 : f (adjointMap F b x) ∈ P 0 := 𝓛.endFiltration_antitone (by omega) hy
    rw [Submodule.mem_sup]
    refine ⟨x - f (adjointMap F b x), ?_, _, hy, sub_add_cancel _ _⟩
    change x - f (adjointMap F b x) ∈ P 0 ∧ adjointMap F b (x - f (adjointMap F b x)) = 0
    exact ⟨sub_mem hx0 hy0, by rw [map_sub, hf, sub_self]⟩
  refine ⟨n, fun k hk => ?_⟩
  by_contra hkn
  exact hk ((adjointLattice_antitone 𝓛 b (le_of_not_ge hkn)).trans hle)

end LocalField

end Langlands.BushnellKutzko
