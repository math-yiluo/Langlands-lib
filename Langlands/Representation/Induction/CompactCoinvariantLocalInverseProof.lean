import Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement

/-!
# The normalized local-section map into compact-induction coinvariants

This module proves `CompactCoinvariantLocalInverseExists`. For a compact open
subgroup `K` and a vector `v` fixed by `H ∩ K`, the normalized class of the
double-coset section on `H * K` is unchanged when `K` is refined to a compact
open subgroup `N ≤ K`: summing the right translates of the `N`-section over the
finite coset space `K / N` gives a natural multiple of the `K`-section, and the
same count relates the quotient masses of the two orbits. Common refinements
then give choice independence and linearity, and conjugating `K` by `h ∈ H`
turns the section of `σ h v` into a right translate of the section of `v`.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

universe uG uV

section LocalInverse

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H : Subgroup G) (σ : Representation ℂ H V)

/-! ### Orbits of open subgroups in the left quotient -/

omit [IsTopologicalGroup G] in
private theorem mem_orbit_iff (K : OpenSubgroup G) (y : G) :
    quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K ↔
      ∃ (h : H) (k : K), y = (h : G) * (k : G) := by
  constructor
  · rintro ⟨k, hk, he⟩
    have hy : y * k⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    exact ⟨⟨y * k⁻¹, hy⟩, ⟨k, hk⟩, by simp⟩
  · rintro ⟨h, k, rfl⟩
    refine ⟨k, k.property, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simp [mul_assoc]

omit [IsTopologicalGroup G] in
private theorem mem_orbit_mul_iff (K : OpenSubgroup G) (y : G) {k : G} (hk : k ∈ K) :
    quotientMap H (y * k) ∈ QuotientIntegration.compactOpenQuotientOrbit H K ↔
      quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K := by
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, l, he⟩
    refine ⟨h, l * ⟨k, hk⟩⁻¹, ?_⟩
    calc y = y * k * k⁻¹ := by group
      _ = (h : G) * (l : G) * k⁻¹ := by rw [he]
      _ = _ := by simp [mul_assoc]
  · rintro ⟨h, l, rfl⟩
    exact ⟨h, l * ⟨k, hk⟩, by simp [mul_assoc]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem quotientMap_mul_left (h : H) (y : G) :
    quotientMap H ((h : G) * y) = quotientMap H y :=
  Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))

omit [IsTopologicalGroup G] in
private theorem orbit_of_mul_mem {K N : OpenSubgroup G} (hNK : N ≤ K) {y z : G} (hz : z ∈ K)
    (h : quotientMap H (y * z) ∈ QuotientIntegration.compactOpenQuotientOrbit H N) :
    quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K := by
  obtain ⟨p, n, he⟩ := (mem_orbit_iff H N _).mp h
  rw [← mem_orbit_mul_iff H K y hz]
  exact (mem_orbit_iff H K _).mpr ⟨p, ⟨n, hNK n.property⟩, he⟩

/-! ### Values of double-coset sections at the identity -/

private theorem section_ext {f f' : CompactFunctions H σ}
    (h : ∀ x, eval H σ f.1 x = eval H σ f'.1 x) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

private def evalHom (y : G) : CompactFunctions H σ →+ V where
  toFun f := eval H σ f.1 y
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem admissible_mono {K N : OpenSubgroup G} (hNK : N ≤ K) {v : V}
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    v ∈ fixedVectors σ (conjOpenSubgroup H N 1).toSubgroup :=
  fun p => hv ⟨p, mem_conjOpenSubgroup.mpr (hNK (mem_conjOpenSubgroup.mp p.property))⟩

private theorem section_apply_mul (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) (h : H) (k : K) :
    eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).1 ((h : G) * (k : G)) = σ h v := by
  simpa using compactDoubleCosetSection_apply H σ K hK 1 v hv h k

private theorem section_apply_of_not_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : V) (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) {y : G}
    (hy : quotientMap H y ∉ QuotientIntegration.compactOpenQuotientOrbit H K) :
    eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).1 y = 0 := by
  by_contra hne
  obtain ⟨k, hk, he⟩ :=
    compactDoubleCosetSection_support_subset H σ K hK 1 v hv ⟨y, hne, rfl⟩
  exact hy ⟨k, hk, by simpa only [one_mul] using he⟩

private theorem section_add (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v w : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hw : w ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hvw : v + w ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    compactDoubleCosetSection H σ K hK 1 (v + w) hvw =
      compactDoubleCosetSection H σ K hK 1 v hv + compactDoubleCosetSection H σ K hK 1 w hw := by
  apply section_ext
  intro y
  change _ = eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).1 y +
    eval H σ (compactDoubleCosetSection H σ K hK 1 w hw).1 y
  by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
  · obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
    rw [section_apply_mul, section_apply_mul, section_apply_mul, map_add]
  · rw [section_apply_of_not_mem H σ K hK _ _ hy, section_apply_of_not_mem H σ K hK _ _ hy,
      section_apply_of_not_mem H σ K hK _ _ hy, add_zero]

private theorem section_smul (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (a : ℂ) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hav : a • v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    compactDoubleCosetSection H σ K hK 1 (a • v) hav =
      a • compactDoubleCosetSection H σ K hK 1 v hv := by
  apply section_ext
  intro y
  change _ = a • eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).1 y
  by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
  · obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
    rw [section_apply_mul, section_apply_mul, map_smul]
  · rw [section_apply_of_not_mem H σ K hK _ _ hy, section_apply_of_not_mem H σ K hK _ _ hy,
      smul_zero]

/-! ### Conjugating the subgroup by an element of `H` -/

/-- The open subgroup `g K g⁻¹`. -/
private def conjSubgroup (K : OpenSubgroup G) (g : G) : OpenSubgroup G :=
  K.comap (MulAut.conj g⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj g⁻¹)

private theorem mem_conjSubgroup {K : OpenSubgroup G} {g x : G} :
    x ∈ conjSubgroup K g ↔ g⁻¹ * x * g ∈ K := by
  simp [conjSubgroup]

private theorem isCompact_conjSubgroup {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    (g : G) : IsCompact (conjSubgroup K g : Set G) := by
  have he : (conjSubgroup K g : Set G) = (fun x => g * x * g⁻¹) '' (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨g⁻¹ * x * g, mem_conjSubgroup.mp hx, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using hk)
  rw [he]
  exact hK.image (IsTopologicalGroup.continuous_conj g)

private theorem translate_admissible (K : OpenSubgroup G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) (h : H) :
    σ h v ∈ fixedVectors σ (conjOpenSubgroup H (conjSubgroup K h) 1).toSubgroup := by
  intro p
  have hp : (h : G)⁻¹ * ((p : H) : G) * h ∈ K :=
    mem_conjSubgroup.mp (by simpa using mem_conjOpenSubgroup.mp p.property)
  have hfix := hv ⟨h⁻¹ * p * h, mem_conjOpenSubgroup.mpr (by simpa using hp)⟩
  change σ (h⁻¹ * p * h) v = v at hfix
  change σ (p : H) (σ h v) = σ h v
  calc σ (p : H) (σ h v) = σ ((p : H) * h) v := by rw [map_mul, Module.End.mul_apply]
    _ = σ (h * (h⁻¹ * p * h)) v := by congr 2; group
    _ = σ h (σ (h⁻¹ * p * h) v) := by rw [map_mul, Module.End.mul_apply]
    _ = σ h v := by rw [hfix]

private theorem orbit_conjSubgroup (K : OpenSubgroup G) (h : H) :
    QuotientIntegration.compactOpenQuotientOrbit H (conjSubgroup K h) =
      QuotientIntegration.rightTranslate H (h : G) ⁻¹'
        QuotientIntegration.compactOpenQuotientOrbit H K := by
  ext x
  induction x using Quotient.inductionOn with
  | h y =>
    change quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H (conjSubgroup K h) ↔
      quotientMap H (y * h) ∈ QuotientIntegration.compactOpenQuotientOrbit H K
    rw [mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨p, k, rfl⟩
      exact ⟨p * h, ⟨_, mem_conjSubgroup.mp k.property⟩, by simp [mul_assoc]⟩
    · rintro ⟨p, k, he⟩
      refine ⟨p * h⁻¹, ⟨(h : G) * k * (h : G)⁻¹,
        mem_conjSubgroup.mpr (by simp [mul_assoc])⟩, ?_⟩
      calc y = y * h * (h : G)⁻¹ := by group
        _ = (p : G) * k * (h : G)⁻¹ := by rw [he]
        _ = _ := by simp [mul_assoc]

private theorem section_translate (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) (h : H)
    (hK' : IsCompact (conjSubgroup K h : Set G))
    (hv' : σ h v ∈ fixedVectors σ (conjOpenSubgroup H (conjSubgroup K h) 1).toSubgroup) :
    compactDoubleCosetSection H σ (conjSubgroup K h) hK' 1 (σ h v) hv' =
      compactInduced H σ (h : G) (compactDoubleCosetSection H σ K hK 1 v hv) := by
  apply section_ext
  intro y
  change _ = eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).1 (y * h)
  by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H (conjSubgroup K h)
  · obtain ⟨p, k, rfl⟩ := (mem_orbit_iff H _ y).mp hy
    rw [section_apply_mul]
    have hk : (h : G)⁻¹ * k * h ∈ K := mem_conjSubgroup.mp k.property
    have he : (p : G) * k * h = ((p * h : H) : G) * ((⟨_, hk⟩ : K) : G) := by
      simp [mul_assoc]
    rw [he, section_apply_mul, map_mul, Module.End.mul_apply]
  · rw [section_apply_of_not_mem H σ _ _ _ _ hy]
    rw [orbit_conjSubgroup] at hy
    exact (section_apply_of_not_mem H σ K hK v hv hy).symm

/-! ### Refinement by a smaller compact open subgroup -/

/-- The finite coset space `K / N`, as a quotient of the subgroup `K`. -/
private abbrev CosetSpace (K N : OpenSubgroup G) :=
  K.toSubgroup ⧸ N.toSubgroup.subgroupOf K.toSubgroup

/-- The chosen representative in `G` of a coset in `K / N`. -/
private def cosetRep {K N : OpenSubgroup G} (q : CosetSpace K N) : G :=
  ((q.out : K.toSubgroup) : G)

omit [IsTopologicalGroup G] in
private theorem cosetRep_mem {K N : OpenSubgroup G} (q : CosetSpace K N) : cosetRep q ∈ K :=
  (q.out : K.toSubgroup).property

private theorem finite_cosetSpace {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    (N : OpenSubgroup G) : Finite (CosetSpace K N) := by
  have : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp hK
  exact Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen K.toSubgroup N.toSubgroup N.isOpen)

omit [IsTopologicalGroup G] in
/-- Summing a right-`N`-invariant function over `y * k * (K / N)` does not depend on
`k ∈ K`, since left multiplication by `k` permutes `K / N`. -/
private theorem sum_mul_rep {M : Type*} [AddCommMonoid M] {K N : OpenSubgroup G}
    [Fintype (CosetSpace K N)] (φ : G → M) (hφ : ∀ y : G, ∀ n ∈ N, φ (y * n) = φ y)
    (y : G) {k : G} (hk : k ∈ K) :
    ∑ q : CosetSpace K N, φ (y * k * cosetRep q) = ∑ q : CosetSpace K N, φ (y * cosetRep q) := by
  let k' : K.toSubgroup := ⟨k, hk⟩
  refine Fintype.sum_equiv (MulAction.toPerm k') _ _ fun q => ?_
  obtain ⟨n, hn⟩ :=
    QuotientGroup.mk_out_eq_mul (N.toSubgroup.subgroupOf K.toSubgroup) (k' * q.out)
  have hq : (MulAction.toPerm k' q : CosetSpace K N).out = k' * q.out * n := by
    rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul, hn]
  have hnN : ((n : K.toSubgroup) : G) ∈ N := Subgroup.mem_subgroupOf.mp n.property
  simp only [cosetRep, hq, Subgroup.coe_mul]
  rw [← hφ (y * k * ((q.out : K.toSubgroup) : G)) _ hnN]
  simp [k', mul_assoc]

/-- The number of cosets in `K / N` whose representatives lie in `H * N`. -/
private def cosetCount (K N : OpenSubgroup G) [Fintype (CosetSpace K N)] : ℕ := by
  classical
  exact ∑ q : CosetSpace K N,
    if quotientMap H (cosetRep q) ∈ QuotientIntegration.compactOpenQuotientOrbit H N then 1 else 0

private theorem sum_section_rep {K N : OpenSubgroup G} (hNK : N ≤ K)
    (hN : IsCompact (N : Set G)) [Fintype (CosetSpace K N)] (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hvN : v ∈ fixedVectors σ (conjOpenSubgroup H N 1).toSubgroup) :
    ∑ q : CosetSpace K N, eval H σ (compactDoubleCosetSection H σ N hN 1 v hvN).1 (cosetRep q) =
      cosetCount H K N • v := by
  classical
  rw [cosetCount, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · obtain ⟨p, n, hpn⟩ := (mem_orbit_iff H N _).mp hq
    rw [hpn, section_apply_mul, one_smul]
    have hpK : (p : G) ∈ K := by
      have he : (p : G) = cosetRep q * ((n : G))⁻¹ := by rw [hpn]; group
      rw [he]
      exact K.mul_mem (cosetRep_mem q) (K.inv_mem (hNK n.property))
    exact hv ⟨p, mem_conjOpenSubgroup.mpr (by simpa using hpK)⟩
  · rw [section_apply_of_not_mem H σ N hN v hvN hq, zero_smul]

/-- Summing the right translates of the `N`-section over `K / N` gives `cosetCount`
times the `K`-section. -/
private theorem sum_translate_section {K N : OpenSubgroup G} (hNK : N ≤ K)
    (hK : IsCompact (K : Set G)) (hN : IsCompact (N : Set G)) [Fintype (CosetSpace K N)]
    (v : V) (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hvN : v ∈ fixedVectors σ (conjOpenSubgroup H N 1).toSubgroup) :
    ∑ q : CosetSpace K N,
        compactInduced H σ (cosetRep q) (compactDoubleCosetSection H σ N hN 1 v hvN) =
      cosetCount H K N • compactDoubleCosetSection H σ K hK 1 v hv := by
  apply section_ext
  intro y
  have hsum : ∀ f : CosetSpace K N → CompactFunctions H σ,
      eval H σ (∑ q, f q).1 y = ∑ q, eval H σ (f q).1 y :=
    fun f => _root_.map_sum (evalHom H σ y) f Finset.univ
  have hnsmul : ∀ (c : ℕ) (f : CompactFunctions H σ),
      eval H σ (c • f).1 y = c • eval H σ f.1 y :=
    fun c f => map_nsmul (evalHom H σ y) c f
  rw [hsum, hnsmul]
  change ∑ q : CosetSpace K N,
      eval H σ (compactDoubleCosetSection H σ N hN 1 v hvN).1 (y * cosetRep q) = _
  have hφ : ∀ z : G, ∀ n ∈ N, eval H σ (compactDoubleCosetSection H σ N hN 1 v hvN).1 (z * n) =
      eval H σ (compactDoubleCosetSection H σ N hN 1 v hvN).1 z :=
    fun z n hn => compactDoubleCosetSection_mul H σ N hN 1 v hvN ⟨n, hn⟩ z
  by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
  · obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
    rw [section_apply_mul, sum_mul_rep _ hφ (h : G) k.property]
    simp_rw [eval_covariant]
    rw [← _root_.map_sum, sum_section_rep H σ hNK hN v hv hvN, map_nsmul]
  · rw [section_apply_of_not_mem H σ K hK v hv hy, smul_zero]
    refine Finset.sum_eq_zero fun q _ => section_apply_of_not_mem H σ N hN v hvN ?_
    exact fun hq => hy (orbit_of_mul_mem H hNK (cosetRep_mem q) hq)

omit [IsTopologicalGroup G] in
/-- The indicator of an `N`-orbit is invariant under right translation by `N`. -/
private theorem indicator_orbit_mul (N : OpenSubgroup G) (z : G) {n : G} (hn : n ∈ N) :
    (QuotientIntegration.compactOpenQuotientOrbit H N).indicator
        (1 : QuotientIntegration.LeftQuotient H → ℝ≥0∞) (quotientMap H (z * n)) =
      (QuotientIntegration.compactOpenQuotientOrbit H N).indicator 1 (quotientMap H z) := by
  by_cases hz : quotientMap H z ∈ QuotientIntegration.compactOpenQuotientOrbit H N
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((mem_orbit_mul_iff H N z hn).mpr hz),
      Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem fun h' => hz ((mem_orbit_mul_iff H N z hn).mp h')]

variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]

/-- The quotient masses of the two orbits satisfy the same counting relation. -/
private theorem orbit_mass_relation {K N : OpenSubgroup G} (hNK : N ≤ K)
    [Fintype (CosetSpace K N)] (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν) :
    (Fintype.card (CosetSpace K N) : ℝ≥0∞) *
        ν (QuotientIntegration.compactOpenQuotientOrbit H N) =
      (cosetCount H K N : ℝ≥0∞) * ν (QuotientIntegration.compactOpenQuotientOrbit H K) := by
  classical
  have hNm : MeasurableSet (QuotientIntegration.compactOpenQuotientOrbit H N) :=
    (QuotientIntegration.isOpen_compactOpenQuotientOrbit H N).measurableSet
  have hKm : MeasurableSet (QuotientIntegration.compactOpenQuotientOrbit H K) :=
    (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet
  have hpt : ∀ x, ∑ q : CosetSpace K N,
      (QuotientIntegration.compactOpenQuotientOrbit H N).indicator
        (1 : QuotientIntegration.LeftQuotient H → ℝ≥0∞)
        (QuotientIntegration.rightTranslate H (cosetRep q) x) =
        (cosetCount H K N : ℝ≥0∞) *
          (QuotientIntegration.compactOpenQuotientOrbit H K).indicator 1 x := by
    intro x
    induction x using Quotient.inductionOn with
    | h y =>
      change ∑ q : CosetSpace K N, (QuotientIntegration.compactOpenQuotientOrbit H N).indicator
          (1 : QuotientIntegration.LeftQuotient H → ℝ≥0∞) (quotientMap H (y * cosetRep q)) =
        (cosetCount H K N : ℝ≥0∞) *
          (QuotientIntegration.compactOpenQuotientOrbit H K).indicator 1 (quotientMap H y)
      by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
      · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
        obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
        refine (sum_mul_rep (fun z => (QuotientIntegration.compactOpenQuotientOrbit H N).indicator
          (1 : QuotientIntegration.LeftQuotient H → ℝ≥0∞) (quotientMap H z))
          (fun z n hn => indicator_orbit_mul H N z hn) (h : G) k.property).trans ?_
        simp only [quotientMap_mul_left]
        rw [cosetCount, Nat.cast_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        split_ifs with hq
        · rw [Set.indicator_of_mem hq, Pi.one_apply, Nat.cast_one]
        · rw [Set.indicator_of_notMem hq, Nat.cast_zero]
      · rw [Set.indicator_of_notMem hy, mul_zero]
        refine Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem ?_ _
        exact fun hq => hy (orbit_of_mul_mem H hNK (cosetRep_mem q) hq)
  calc (Fintype.card (CosetSpace K N) : ℝ≥0∞) *
        ν (QuotientIntegration.compactOpenQuotientOrbit H N) =
      ∑ _q : CosetSpace K N, ν (QuotientIntegration.compactOpenQuotientOrbit H N) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = ∑ q : CosetSpace K N, ∫⁻ x,
          (QuotientIntegration.compactOpenQuotientOrbit H N).indicator 1
            (QuotientIntegration.rightTranslate H (cosetRep q) x) ∂ν := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [(hinv (cosetRep q)).lintegral_comp (measurable_one.indicator hNm),
          lintegral_indicator_one hNm]
    _ = ∫⁻ x, ∑ q : CosetSpace K N,
          (QuotientIntegration.compactOpenQuotientOrbit H N).indicator 1
            (QuotientIntegration.rightTranslate H (cosetRep q) x) ∂ν := by
        rw [lintegral_finsetSum]
        intro q _
        exact (measurable_one.indicator hNm).comp
          (QuotientIntegration.rightTranslate H (cosetRep q)).continuous.measurable
    _ = ∫⁻ x, (cosetCount H K N : ℝ≥0∞) *
          (QuotientIntegration.compactOpenQuotientOrbit H K).indicator 1 x ∂ν := by
        simp_rw [hpt]
    _ = (cosetCount H K N : ℝ≥0∞) * ν (QuotientIntegration.compactOpenQuotientOrbit H K) := by
        rw [lintegral_const_mul _ (measurable_one.indicator hKm), lintegral_indicator_one hKm]

/-! ### The normalized class -/

/-- The normalized class `ν(C_K)⁻¹ • [section]` attached to an admissible `K`. -/
private def normalized (ν : Measure (QuotientIntegration.LeftQuotient H)) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    Representation.Coinvariants (compactInduced H σ) :=
  (Complex.ofReal ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal))⁻¹ •
    Representation.Coinvariants.mk (compactInduced H σ)
      (compactDoubleCosetSection H σ K hK 1 v hv)

private theorem normalized_refine (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    {K N : OpenSubgroup G} (hNK : N ≤ K) (hK : IsCompact (K : Set G))
    (hN : IsCompact (N : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hvN : v ∈ fixedVectors σ (conjOpenSubgroup H N 1).toSubgroup) :
    normalized H σ ν K hK v hv = normalized H σ ν N hN v hvN := by
  classical
  have := finite_cosetSpace hK N
  let := Fintype.ofFinite (CosetSpace K N)
  have hD := congrArg (Representation.Coinvariants.mk (compactInduced H σ))
    (sum_translate_section H σ hNK hK hN v hv hvN)
  rw [_root_.map_sum, map_nsmul] at hD
  simp_rw [Representation.Coinvariants.mk_self_apply] at hD
  rw [Finset.sum_const, Finset.card_univ] at hD
  have hE := orbit_mass_relation H hNK ν hinv
  obtain ⟨hK0, hKt⟩ := hmass K hK
  obtain ⟨hN0, hNt⟩ := hmass N hN
  have hE' : (Fintype.card (CosetSpace K N) : ℝ) *
      (ν (QuotientIntegration.compactOpenQuotientOrbit H N)).toReal =
      (cosetCount H K N : ℝ) * (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal := by
    have h := congrArg ENNReal.toReal hE
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  set a := Fintype.card (CosetSpace K N) with ha_def
  set c := cosetCount H K N with hc_def
  set mN := (ν (QuotientIntegration.compactOpenQuotientOrbit H N)).toReal with hmN_def
  set mK := (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal with hmK_def
  have hmN : 0 < mN := ENNReal.toReal_pos hN0.ne' hNt.ne
  have hmK : 0 < mK := ENNReal.toReal_pos hK0.ne' hKt.ne
  have ha : 0 < a := Fintype.card_pos
  have hc : (c : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hE'
    have : (0 : ℝ) < a * mN := mul_pos (by exact_mod_cast ha) hmN
    linarith
  have hD' : (a : ℂ) • Representation.Coinvariants.mk (compactInduced H σ)
        (compactDoubleCosetSection H σ N hN 1 v hvN) =
      (c : ℂ) • Representation.Coinvariants.mk (compactInduced H σ)
        (compactDoubleCosetSection H σ K hK 1 v hv) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact hD
  have hX : Representation.Coinvariants.mk (compactInduced H σ)
        (compactDoubleCosetSection H σ N hN 1 v hvN) =
      ((c : ℂ) / a) • Representation.Coinvariants.mk (compactInduced H σ)
        (compactDoubleCosetSection H σ K hK 1 v hv) := by
    rw [div_eq_inv_mul, mul_smul, ← hD', smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast ha.ne'), one_smul]
  have hEc : (a : ℂ) * (mN : ℂ) = (c : ℂ) * (mK : ℂ) := by exact_mod_cast hE'
  have hmN' : (mN : ℂ) ≠ 0 := by exact_mod_cast hmN.ne'
  have hmK' : (mK : ℂ) ≠ 0 := by exact_mod_cast hmK.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold normalized
  rw [← hmN_def, ← hmK_def, hX, smul_smul]
  congr 1
  field_simp
  linear_combination hEc

private theorem normalized_eq (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    {K K' : OpenSubgroup G} (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
    (v : V) (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hv' : v ∈ fixedVectors σ (conjOpenSubgroup H K' 1).toSubgroup) :
    normalized H σ ν K hK v hv = normalized H σ ν K' hK' v hv' := by
  have hJ : IsCompact ((K ⊓ K' : OpenSubgroup G) : Set G) := by
    rw [OpenSubgroup.coe_inf]
    exact hK.inter_right K'.isClosed
  rw [normalized_refine H σ ν hinv hmass inf_le_left hK hJ v hv
      (admissible_mono H σ inf_le_left hv),
    normalized_refine H σ ν hinv hmass inf_le_right hK' hJ v hv'
      (admissible_mono H σ inf_le_right hv')]

private theorem normalized_translate (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) (h : H) :
    normalized H σ ν (conjSubgroup K h) (isCompact_conjSubgroup hK h) (σ h v)
        (translate_admissible H σ K v hv h) =
      normalized H σ ν K hK v hv := by
  unfold normalized
  rw [section_translate H σ K hK v hv h, Representation.Coinvariants.mk_self_apply,
    orbit_conjSubgroup, (hinv (h : G)).measure_preimage
      (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet.nullMeasurableSet]

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
private theorem exists_admissible
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth σ) (v : V) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup := by
  obtain ⟨L, hL⟩ := hσ v
  obtain ⟨O, hO, he⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp L.isOpen
  have h1 : (1 : G) ∈ O := by
    have h1L : (1 : H) ∈ (L : Set H) := L.one_mem
    rw [← he] at h1L
    exact h1L
  obtain ⟨K, hK, hKO⟩ := hG O hO h1
  refine ⟨K, hK, fun p => ?_⟩
  have hpK : ((p : H) : G) ∈ K := by
    simpa using mem_conjOpenSubgroup.mp p.property
  have hpL : (p : H) ∈ (L : Set H) := by
    rw [← he]
    exact hKO hpK
  exact hL ⟨p, hpL⟩

/-- The linear map out of the inducing coinvariants, characterized by the normalized
double-coset-section value for every admissible compact open subgroup. -/
private theorem exists_localInverse
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth σ) (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤) :
    ∃ T : Representation.Coinvariants σ →ₗ[ℂ]
        Representation.Coinvariants (compactInduced H σ),
      ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
        (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup),
        T (Representation.Coinvariants.mk σ v) = normalized H σ ν K hK v hv := by
  choose Kv hKv hvK using exists_admissible H σ hG hσ
  have hinf : ∀ v w : V, IsCompact ((Kv v ⊓ Kv w : OpenSubgroup G) : Set G) := by
    intro v w
    rw [OpenSubgroup.coe_inf]
    exact (hKv v).inter_right (Kv w).isClosed
  let f : V →ₗ[ℂ] Representation.Coinvariants (compactInduced H σ) :=
    { toFun := fun v => normalized H σ ν (Kv v) (hKv v) v (hvK v)
      map_add' := by
        intro v w
        have hvJ := admissible_mono H σ (inf_le_left : Kv v ⊓ Kv w ≤ Kv v) (hvK v)
        have hwJ := admissible_mono H σ (inf_le_right : Kv v ⊓ Kv w ≤ Kv w) (hvK w)
        rw [normalized_eq H σ ν hinv hmass (hKv (v + w)) (hinf v w) (v + w) (hvK (v + w))
            (Submodule.add_mem _ hvJ hwJ),
          normalized_eq H σ ν hinv hmass (hKv v) (hinf v w) v (hvK v) hvJ,
          normalized_eq H σ ν hinv hmass (hKv w) (hinf v w) w (hvK w) hwJ]
        unfold normalized
        rw [section_add H σ _ (hinf v w) v w hvJ hwJ, map_add, smul_add]
      map_smul' := by
        intro a v
        have hav := Submodule.smul_mem _ a (hvK v)
        rw [normalized_eq H σ ν hinv hmass (hKv (a • v)) (hKv v) (a • v) (hvK (a • v)) hav]
        unfold normalized
        rw [section_smul H σ _ (hKv v) a v (hvK v), map_smul, RingHom.id_apply, smul_comm] }
  have hf : ∀ v : V, f v = normalized H σ ν (Kv v) (hKv v) v (hvK v) := fun v => rfl
  refine ⟨Representation.Coinvariants.lift σ f fun h => ?_, fun K hK v hv => ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, hf, hf,
      normalized_eq H σ ν hinv hmass (hKv (σ h v)) (isCompact_conjSubgroup (hKv v) h) (σ h v)
        (hvK (σ h v)) (translate_admissible H σ (Kv v) v (hvK v) h),
      normalized_translate H σ ν hinv (Kv v) (hKv v) v (hvK v) h]
  · rw [Representation.Coinvariants.lift_mk, hf]
    exact normalized_eq H σ ν hinv hmass (hKv v) hK v (hvK v) hv

end LocalInverse

/-- The normalized local-section map out of inducing coinvariants exists. -/
theorem compactCoinvariantLocalInverseExists :
    CompactCoinvariantLocalInverseExists.{uG, uV} := by
  intro G _ _ _ _ _ _ _ hG H _ _ _ μG μH _ _ _ _ _ _ _ _ ν _ hν V _ _ σ hσ
  exact exists_localInverse H σ hG hσ ν hν.right_invariant
    (fun J hJ => hν.compactOpenQuotientOrbit_mass J hJ)

end Langlands.Induction
