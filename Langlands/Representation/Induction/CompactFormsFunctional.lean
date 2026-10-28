import Langlands.Representation.Induction.CompactLocalSectionSpanningProof
import Langlands.Representation.Induction.CompactCoinvariantIntegral
import Langlands.Analysis.Local.QuotientMass
import Langlands.Representation.Filtration.InvariantBilinear
import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Twist.Definitions

/-!
# Invariant forms on compact induction and equivariant functionals

Let `H` be a closed subgroup of a group `G` with a basis of compact open
subgroups at the identity, `θ` a character of `H` with open kernel, `π` a smooth
representation of `G` and `ν` a right-invariant measure on `H \ G` giving positive
finite mass to the orbit of every compact open subgroup. Every bilinear form `B`
on `c-Ind_H^G θ × π` invariant under the simultaneous action of `G` defines the
functional `ℓ_B (w) = ν(H \ H K)⁻¹ B (s_K, w)`, where `K` is a compact open
subgroup fixing `w` on whose intersection with `H` the character is trivial,
and `s_K` is the section on `H K` with value one at the identity. The value does
not depend on `K`, `ℓ_B` is `(H, θ⁻¹)`-equivariant, and `B ↦ ℓ_B` is linear and
injective.

The refinement lemmas on double-coset sections and orbit masses are copied from
the private part of `CompactCoinvariantLocalInverseProof`.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal

universe uG uV uW

namespace FormsFunctional

section Refinement

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

private theorem section_congr (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {v v' : V}
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup)
    (hv' : v' ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) (h : v = v') :
    compactDoubleCosetSection H σ K hK 1 v hv = compactDoubleCosetSection H σ K hK 1 v' hv' := by
  subst h
  rfl

private theorem section_zero (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (0 : V) ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    compactDoubleCosetSection H σ K hK 1 0 hv = 0 := by
  apply section_ext
  intro y
  change _ = (0 : V)
  by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
  · obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
    rw [section_apply_mul, map_zero]
  · exact section_apply_of_not_mem H σ K hK 0 hv hy

/-- A double-coset section is fixed by right translation by its subgroup. -/
private theorem translate_section_of_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : V) (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) {k : G} (hk : k ∈ K) :
    compactInduced H σ k (compactDoubleCosetSection H σ K hK 1 v hv) =
      compactDoubleCosetSection H σ K hK 1 v hv := by
  apply section_ext
  intro y
  exact compactDoubleCosetSection_mul H σ K hK 1 v hv ⟨k, hk⟩ y

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

end Refinement

section Bridge

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (H : Subgroup G) (θ : H →* ℂˣ) (π : Representation ℂ G W)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem characterRepresentation_apply (h : H) (z : ℂ) :
    characterRepresentation θ h z = (θ h : ℂ) * z := rfl

/-- Invariance of a form, moved to the second argument. -/
private theorem form_translate {B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    (g : G) (f : CompactFunctions H (characterRepresentation θ)) (w : W) :
    B (compactInduced H (characterRepresentation θ) g f) w = B f (π g⁻¹ w) := by
  have h := hB g f (π g⁻¹ w)
  have e : π g (π g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e] at h
  exact h.trans (one_mul _)

private theorem form_translate_of_fixed
    {B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    {g : G} (f : CompactFunctions H (characterRepresentation θ)) {w : W} (hw : π g w = w) :
    B (compactInduced H (characterRepresentation θ) g f) w = B f w := by
  have h := hB g f w
  rw [hw] at h
  exact h.trans (one_mul _)

variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]
variable (ν : Measure (QuotientIntegration.LeftQuotient H))

/-- The value of a form at the unit section of `K`, divided by the mass of the
orbit of `K` in `H \ G`. -/
private def normalizedValue (B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup)
    (w : W) : ℂ :=
  (Complex.ofReal (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal)⁻¹ *
    B (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w

private theorem normalizedValue_refine
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    {B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    {K N : OpenSubgroup G} (hNK : N ≤ K) (hK : IsCompact (K : Set G))
    (hN : IsCompact (N : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup)
    (hvN : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H N 1).toSubgroup)
    {w : W} (hw : ∀ k ∈ K, π k w = w) :
    normalizedValue H θ ν B K hK hv w = normalizedValue H θ ν B N hN hvN w := by
  classical
  have := finite_cosetSpace hK N
  let := Fintype.ofFinite (CosetSpace K N)
  have hD := congrArg (B.flip w)
    (sum_translate_section H (characterRepresentation θ) hNK hK hN 1 hv hvN)
  rw [_root_.map_sum, map_nsmul] at hD
  have hT : ∀ q : CosetSpace K N, B.flip w (compactInduced H (characterRepresentation θ)
      (cosetRep q) (compactDoubleCosetSection H (characterRepresentation θ) N hN 1 1 hvN)) =
      B (compactDoubleCosetSection H (characterRepresentation θ) N hN 1 1 hvN) w :=
    fun q => form_translate_of_fixed H θ π hB _ (hw _ (cosetRep_mem q))
  simp only [hT, Finset.sum_const, Finset.card_univ, LinearMap.flip_apply, nsmul_eq_mul] at hD
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
  set BN := B (compactDoubleCosetSection H (characterRepresentation θ) N hN 1 1 hvN) w
  set BK := B (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w
  have hmN : 0 < mN := ENNReal.toReal_pos hN0.ne' hNt.ne
  have hmK : 0 < mK := ENNReal.toReal_pos hK0.ne' hKt.ne
  have ha : 0 < a := Fintype.card_pos
  have hc : (c : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hE'
    have : (0 : ℝ) < a * mN := mul_pos (by exact_mod_cast ha) hmN
    linarith
  have hEc : (a : ℂ) * (mN : ℂ) = (c : ℂ) * (mK : ℂ) := by exact_mod_cast hE'
  have hmN' : (mN : ℂ) ≠ 0 := by exact_mod_cast hmN.ne'
  have hmK' : (mK : ℂ) ≠ 0 := by exact_mod_cast hmK.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have key : (mN : ℂ) * BK = (mK : ℂ) * BN := by
    apply mul_left_cancel₀ hc'
    linear_combination (-(mN : ℂ)) * hD + BN * hEc
  unfold normalizedValue
  rw [← hmN_def, ← hmK_def]
  field_simp
  linear_combination key

private theorem normalizedValue_eq
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    {B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    {K K' : OpenSubgroup G} (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup)
    (hv' : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K' 1).toSubgroup)
    {w : W} (hw : ∀ k ∈ K, π k w = w) (hw' : ∀ k ∈ K', π k w = w) :
    normalizedValue H θ ν B K hK hv w = normalizedValue H θ ν B K' hK' hv' w := by
  have hJ : IsCompact ((K ⊓ K' : OpenSubgroup G) : Set G) := by
    rw [OpenSubgroup.coe_inf]
    exact hK.inter_right K'.isClosed
  rw [normalizedValue_refine H θ π ν hinv hmass hB inf_le_left hK hJ hv
      (admissible_mono H _ inf_le_left hv) hw,
    normalizedValue_refine H θ π ν hinv hmass hB inf_le_right hK' hJ hv'
      (admissible_mono H _ inf_le_right hv') hw']

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
/-- Some compact open subgroup is admissible for the unit section and fixes `w`. -/
private theorem exists_admissible
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π) (w : W) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup ∧
      ∀ k ∈ K, π k w = w := by
  obtain ⟨L, hL⟩ := hσ 1
  obtain ⟨O, hO, he⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp L.isOpen
  have h1 : (1 : G) ∈ O := by
    have h1L : (1 : H) ∈ (L : Set H) := L.one_mem
    rw [← he] at h1L
    exact h1L
  obtain ⟨K₁, hK₁, hKO⟩ := hG O hO h1
  obtain ⟨M, hM⟩ := hπ w
  refine ⟨K₁ ⊓ M, ?_, fun p => ?_, fun k hk => hM ⟨k, (OpenSubgroup.mem_inf.mp hk).2⟩⟩
  · rw [OpenSubgroup.coe_inf]
    exact hK₁.inter_right M.isClosed
  · have hpKM : ((p : H) : G) ∈ K₁ ⊓ M := by
      simpa using mem_conjOpenSubgroup.mp p.property
    have hpL : (p : H) ∈ (L : Set H) := by
      rw [← he]
      exact hKO (OpenSubgroup.mem_inf.mp hpKM).1
    exact hL ⟨p, hpL⟩

/-- The normalized value at a chosen admissible subgroup fixing `w`. -/
private def functionalValue
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    (B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ) (w : W) : ℂ :=
  normalizedValue H θ ν B (exists_admissible H θ π hG hσ hπ w).choose
    (exists_admissible H θ π hG hσ hπ w).choose_spec.1
    (exists_admissible H θ π hG hσ hπ w).choose_spec.2.1 w

private theorem functionalValue_spec
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    {B : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hB : B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup)
    {w : W} (hw : ∀ k ∈ K, π k w = w) :
    functionalValue H θ π ν hG hσ hπ B w = normalizedValue H θ ν B K hK hv w :=
  normalizedValue_eq H θ π ν hinv hmass hB _ hK _ hv
    (exists_admissible H θ π hG hσ hπ w).choose_spec.2.2 hw

/-- The functional attached to an invariant form. -/
private def functional
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    (B : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ))) : Module.Dual ℂ W where
  toFun := functionalValue H θ π ν hG hσ hπ B.1
  map_add' w₁ w₂ := by
    obtain ⟨K₁, hK₁, hv₁, hw₁⟩ := exists_admissible H θ π hG hσ hπ w₁
    obtain ⟨K₂, hK₂, -, hw₂⟩ := exists_admissible H θ π hG hσ hπ w₂
    have hJ : IsCompact ((K₁ ⊓ K₂ : OpenSubgroup G) : Set G) := by
      rw [OpenSubgroup.coe_inf]
      exact hK₁.inter_right K₂.isClosed
    have hvJ := admissible_mono H _ (inf_le_left : K₁ ⊓ K₂ ≤ K₁) hv₁
    have h₁ : ∀ k ∈ K₁ ⊓ K₂, π k w₁ = w₁ := fun k hk => hw₁ k (OpenSubgroup.mem_inf.mp hk).1
    have h₂ : ∀ k ∈ K₁ ⊓ K₂, π k w₂ = w₂ := fun k hk => hw₂ k (OpenSubgroup.mem_inf.mp hk).2
    have h₁₂ : ∀ k ∈ K₁ ⊓ K₂, π k (w₁ + w₂) = w₁ + w₂ := fun k hk => by
      rw [map_add, h₁ k hk, h₂ k hk]
    rw [functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hJ hvJ h₁₂,
      functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hJ hvJ h₁,
      functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hJ hvJ h₂]
    simp only [normalizedValue, map_add, mul_add]
  map_smul' a w := by
    obtain ⟨K, hK, hv, hw⟩ := exists_admissible H θ π hG hσ hπ w
    have haw : ∀ k ∈ K, π k (a • w) = a • w := fun k hk => by rw [map_smul, hw k hk]
    rw [functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hK hv haw,
      functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hK hv hw]
    simp only [normalizedValue, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

private theorem functional_apply
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    (B : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ))) (w : W) :
    functional H θ π ν hinv hmass hG hσ hπ B w = functionalValue H θ π ν hG hσ hπ B.1 w :=
  rfl

/-- The attached functional transforms by the inverse character. -/
private theorem functional_mem
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    {θ' : H →* ℂˣ} (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (B : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ))) :
    functional H θ π ν hinv hmass hG hσ hπ B ∈ Whittaker.functionals H θ' π := by
  intro h w
  obtain ⟨K, hK, hv, hw⟩ := exists_admissible H θ π hG hσ hπ w
  have hK' := isCompact_conjSubgroup hK (h : G)
  have hv'' := translate_admissible H (characterRepresentation θ) K 1 hv h
  have hv' : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H (conjSubgroup K h) 1).toSubgroup := by
    have := (fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H (conjSubgroup K h) 1).toSubgroup).smul_mem ((θ h : ℂ)⁻¹) hv''
    rwa [characterRepresentation_apply, smul_eq_mul, mul_one, inv_mul_cancel₀ (θ h).ne_zero]
      at this
  have hw' : ∀ k ∈ conjSubgroup K h, π k (π h w) = π h w := by
    intro k hk
    have hk' := hw _ (mem_conjSubgroup.mp hk)
    calc π k (π h w) = π ((h : G) * ((h : G)⁻¹ * k * h)) w := by
          rw [show (h : G) * ((h : G)⁻¹ * k * h) = k * h by group, map_mul, Module.End.mul_apply]
      _ = π h w := by rw [map_mul, Module.End.mul_apply, hk']
  rw [functional_apply, functional_apply,
    functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hK' hv' hw',
    functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hK hv hw]
  have hθv : (θ h : ℂ) • (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H (conjSubgroup K h) 1).toSubgroup :=
    Submodule.smul_mem _ _ hv'
  have hsec : compactInduced H (characterRepresentation θ) (h : G)
      (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) =
      (θ h : ℂ) • compactDoubleCosetSection H (characterRepresentation θ) (conjSubgroup K h)
        hK' 1 1 hv' := by
    rw [← section_translate H (characterRepresentation θ) K hK 1 hv h hK' hv'',
      ← section_smul H (characterRepresentation θ) (conjSubgroup K h) hK' (θ h) 1 hv' hθv]
    exact section_congr H _ _ hK' hv'' hθv (by rw [characterRepresentation_apply]; rfl)
  have hinvB := B.2 (h : G) (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w
  rw [hsec, one_mul, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at hinvB
  have hm : ν (QuotientIntegration.compactOpenQuotientOrbit H (conjSubgroup K h)) =
      ν (QuotientIntegration.compactOpenQuotientOrbit H K) := by
    rw [orbit_conjSubgroup]
    exact (hinv h).measure_preimage
      (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet.nullMeasurableSet
  unfold normalizedValue
  rw [hm, ← hinvB]
  linear_combination
    (-((Complex.ofReal (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal)⁻¹ *
      B.1 (compactDoubleCosetSection H (characterRepresentation θ) (conjSubgroup K h) hK' 1 1 hv')
        (π h w))) * hθ' h

/-- If the attached functional vanishes, so does the form. -/
private theorem eq_zero_of_functional_eq_zero [T2Space G] (hH : IsClosed (H : Set G))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    (B : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)))
    (h0 : functional H θ π ν hinv hmass hG hσ hπ B = 0) : B = 0 := by
  classical
  have step : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
      (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
        (conjOpenSubgroup H K 1).toSubgroup) (w : W),
      B.1 (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w = 0 := by
    intro K hK hv w
    obtain ⟨M, hM⟩ := hπ w
    have hN : IsCompact ((K ⊓ M : OpenSubgroup G) : Set G) := by
      rw [OpenSubgroup.coe_inf]
      exact hK.inter_right M.isClosed
    have := finite_cosetSpace hK (K ⊓ M)
    let := Fintype.ofFinite (CosetSpace K (K ⊓ M))
    have hφ : ∀ y : G, ∀ n ∈ K ⊓ M, π (y * n) w = π y w := fun y n hn => by
      rw [map_mul, Module.End.mul_apply]
      exact congrArg (π y) (hM ⟨n, (OpenSubgroup.mem_inf.mp hn).2⟩)
    have hfix : ∀ k ∈ K, π k (∑ q : CosetSpace K (K ⊓ M), π (cosetRep q) w) =
        ∑ q : CosetSpace K (K ⊓ M), π (cosetRep q) w := by
      intro k hk
      have hs := sum_mul_rep (fun y => π y w) hφ 1 hk
      simp only [one_mul] at hs
      rw [_root_.map_sum]
      refine (Finset.sum_congr rfl fun q _ => ?_).trans hs
      rw [map_mul, Module.End.mul_apply]
    have hzero := LinearMap.congr_fun h0 (∑ q : CosetSpace K (K ⊓ M), π (cosetRep q) w)
    rw [functional_apply, functionalValue_spec H θ π ν hinv hmass hG hσ hπ B.2 hK hv hfix,
      LinearMap.zero_apply] at hzero
    unfold normalizedValue at hzero
    obtain ⟨hK0, hKt⟩ := hmass K hK
    have hm : (Complex.ofReal (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal)⁻¹ ≠
        0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hK0.ne' hKt.ne).ne')
    have hterm : ∀ q : CosetSpace K (K ⊓ M),
        B.1 (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv)
          (π (cosetRep q) w) =
        B.1 (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w := by
      intro q
      have hq := B.2 (cosetRep q)
        (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w
      rwa [translate_section_of_mem H _ K hK 1 hv (cosetRep_mem q), one_mul] at hq
    rw [_root_.map_sum, Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hzero
    have hcard : (Fintype.card (CosetSpace K (K ⊓ M)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hm)).resolve_left hcard
  apply Subtype.ext
  refine LinearMap.ext_on (compactLocalSectionSpanning.{uG, 0} G hG H hH ℂ
    (characterRepresentation θ)) ?_
  rintro f ⟨g, K, hK, v, hv, rfl⟩
  refine LinearMap.ext fun w => ?_
  rw [form_translate H θ π B.2]
  change B.1 _ _ = 0
  by_cases hv0 : v = 0
  · subst hv0
    rw [section_zero, map_zero, LinearMap.zero_apply]
  · have h1 : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
        (conjOpenSubgroup H K 1).toSubgroup := by
      have := (fixedVectors (characterRepresentation θ)
        (conjOpenSubgroup H K 1).toSubgroup).smul_mem v⁻¹ hv
      rwa [smul_eq_mul, inv_mul_cancel₀ hv0] at this
    have hv1 : v • (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
        (conjOpenSubgroup H K 1).toSubgroup :=
      Submodule.smul_mem _ _ h1
    rw [section_congr H _ K hK hv hv1 (by rw [smul_eq_mul, mul_one]),
      section_smul H _ K hK v 1 h1 hv1, map_smul, LinearMap.smul_apply, step K hK h1, smul_zero]

/-- The linear map from invariant forms to equivariant functionals. -/
private def formsFunctional
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (hπ : IsSmooth π)
    {θ' : H →* ℂˣ} (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1) :
    InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
      (fun _ => (1 : ℂ)) →ₗ[ℂ] Whittaker.functionals H θ' π where
  toFun B := ⟨functional H θ π ν hinv hmass hG hσ hπ B,
    functional_mem H θ π ν hinv hmass hG hσ hπ hθ' B⟩
  map_add' B₁ B₂ := by
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    change functionalValue H θ π ν hG hσ hπ (B₁ + B₂).1 w =
      functionalValue H θ π ν hG hσ hπ B₁.1 w + functionalValue H θ π ν hG hσ hπ B₂.1 w
    simp only [functionalValue, normalizedValue, Submodule.coe_add, LinearMap.add_apply, mul_add]
  map_smul' a B := by
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    change functionalValue H θ π ν hG hσ hπ (a • B).1 w =
      a * functionalValue H θ π ν hG hσ hπ B.1 w
    simp only [functionalValue, normalizedValue, Submodule.coe_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring

end Bridge

section Standard

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

private theorem exists_eval_mul {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ H V} (f : CompactFunctions H σ) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x : G, eval H σ f.1 (x * k) = eval H σ f.1 x := by
  obtain ⟨K, hK⟩ := compactInduced_smooth H σ f
  exact ⟨K, fun k hk x =>
    congrArg (fun h : CompactFunctions H σ => eval H σ h.1 x) (hK ⟨k, hk⟩)⟩

private theorem eval_add_apply {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ H V} (f f' : CompactFunctions H σ) (x : G) :
    eval H σ (f + f').1 x = eval H σ f.1 x + eval H σ f'.1 x := rfl

private theorem eval_smul_apply {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ H V} (a : ℂ) (f : CompactFunctions H σ) (x : G) :
    eval H σ (a • f).1 x = a • eval H σ f.1 x := rfl

variable {θ θ' : H →* ℂˣ}

/-- The pointwise product of compactly induced functions for inverse characters,
as a smooth function with trivial covariance. -/
private def productSmooth (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (f₁ : CompactFunctions H (characterRepresentation θ))
    (f₂ : CompactFunctions H (characterRepresentation θ')) :
    SmoothFunctions H (Representation.trivial ℂ H ℂ) :=
  smoothFunctionOf H _
    (fun x => eval H _ f₁.1 x * eval H _ f₂.1 x)
    (fun p x => by
      rw [eval_covariant, eval_covariant, characterRepresentation_apply,
        characterRepresentation_apply, Representation.trivial_apply]
      linear_combination (eval H _ f₁.1 x * eval H _ f₂.1 x) * hθ' p)
    ((exists_eval_mul H f₁).choose ⊓ (exists_eval_mul H f₂).choose)
    (fun k x => by
      have hk := OpenSubgroup.mem_inf.mp k.property
      rw [(exists_eval_mul H f₁).choose_spec (k : G) hk.1 x,
        (exists_eval_mul H f₂).choose_spec (k : G) hk.2 x])

/-- The pointwise product as a compactly induced function. -/
private def product (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (f₁ : CompactFunctions H (characterRepresentation θ))
    (f₂ : CompactFunctions H (characterRepresentation θ')) :
    CompactFunctions H (Representation.trivial ℂ H ℂ) :=
  ⟨productSmooth H hθ' f₁ f₂, by
    refine IsCompact.of_isClosed_subset f₁.2 (isClosed_quotientSupport H _ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, left_ne_zero_of_mul hx, rfl⟩⟩

private theorem eval_product (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (f₁ : CompactFunctions H (characterRepresentation θ))
    (f₂ : CompactFunctions H (characterRepresentation θ')) (x : G) :
    eval H _ (product H hθ' f₁ f₂).1 x = eval H _ f₁.1 x * eval H _ f₂.1 x := rfl

/-- The scalar value of a coinvariant class of the trivial representation. -/
private def coinvariantValue :
    Representation.Coinvariants (Representation.trivial ℂ H ℂ) →ₗ[ℂ] ℂ :=
  Representation.Coinvariants.lift _ LinearMap.id fun _ => LinearMap.ext fun _ => rfl

variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]
variable (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- The standard pairing `(f₁, f₂) ↦ ∫_{H \ G} f₁ f₂ dν`. -/
private def standardForm (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1) :
    CompactFunctions H (characterRepresentation θ) →ₗ[ℂ]
      CompactFunctions H (characterRepresentation θ') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun f₁ f₂ => coinvariantValue H
      (compactCoinvariantIntegral H (Representation.trivial ℂ H ℂ) ν (product H hθ' f₁ f₂)))
    (fun f₁ f₁' f₂ => by
      have he : product H hθ' (f₁ + f₁') f₂ = product H hθ' f₁ f₂ + product H hθ' f₁' f₂ :=
        section_ext H _ fun x => by
          rw [eval_add_apply, eval_product, eval_product, eval_product, eval_add_apply, add_mul]
      rw [he, map_add, map_add])
    (fun a f₁ f₂ => by
      have he : product H hθ' (a • f₁) f₂ = a • product H hθ' f₁ f₂ :=
        section_ext H _ fun x => by
          rw [eval_smul_apply, eval_product, eval_product, eval_smul_apply, smul_eq_mul,
            smul_eq_mul, mul_assoc]
      rw [he, map_smul, map_smul, smul_eq_mul])
    (fun f₁ f₂ f₂' => by
      have he : product H hθ' f₁ (f₂ + f₂') = product H hθ' f₁ f₂ + product H hθ' f₁ f₂' :=
        section_ext H _ fun x => by
          rw [eval_add_apply, eval_product, eval_product, eval_product, eval_add_apply, mul_add]
      rw [he, map_add, map_add])
    (fun a f₁ f₂ => by
      have he : product H hθ' f₁ (a • f₂) = a • product H hθ' f₁ f₂ :=
        section_ext H _ fun x => by
          rw [eval_smul_apply, eval_product, eval_product, eval_smul_apply, smul_eq_mul,
            smul_eq_mul, mul_left_comm]
      rw [he, map_smul, map_smul, smul_eq_mul])

private theorem standardForm_apply (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (f₁ : CompactFunctions H (characterRepresentation θ))
    (f₂ : CompactFunctions H (characterRepresentation θ')) :
    standardForm H ν hθ' f₁ f₂ = coinvariantValue H
      (compactCoinvariantIntegral H (Representation.trivial ℂ H ℂ) ν (product H hθ' f₁ f₂)) :=
  rfl

/-- The standard pairing is invariant under right translation. -/
private theorem standardForm_mem
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1) :
    standardForm H ν hθ' ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ))
      (compactInduced H (characterRepresentation θ')) (fun _ => (1 : ℂ)) := by
  intro g f₁ f₂
  have he : product H hθ' (compactInduced H _ g f₁) (compactInduced H _ g f₂) =
      compactInduced H (Representation.trivial ℂ H ℂ) g (product H hθ' f₁ f₂) :=
    section_ext H _ fun x => rfl
  rw [standardForm_apply, standardForm_apply, he,
    compactCoinvariantIntegral_translate H _ ν hinv, one_mul]

/-- The standard pairing of the two unit sections of `K` is the mass of the orbit of `K`. -/
private theorem standardForm_section (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ) (conjOpenSubgroup H K 1).toSubgroup)
    (hv' : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ')
      (conjOpenSubgroup H K 1).toSubgroup) :
    standardForm H ν hθ' (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv)
        (compactDoubleCosetSection H (characterRepresentation θ') K hK 1 1 hv') =
      ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal : ℂ) := by
  have hm := (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet
  have he : quotientCoinvariantSimple H (Representation.trivial ℂ H ℂ)
      (product H hθ' (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv)
        (compactDoubleCosetSection H (characterRepresentation θ') K hK 1 1 hv')) =
      (SimpleFunc.const _ (Representation.Coinvariants.mk (Representation.trivial ℂ H ℂ)
        (1 : ℂ))).restrict (QuotientIntegration.compactOpenQuotientOrbit H K) := by
    ext q
    induction q using Quotient.inductionOn with
    | h y =>
      rw [SimpleFunc.restrict_apply _ hm, quotientCoinvariantSimple_apply]
      change Representation.Coinvariants.mk _ (eval H _ _ y * eval H _ _ y) =
        (QuotientIntegration.compactOpenQuotientOrbit H K).indicator _ (quotientMap H y)
      by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
      · rw [Set.indicator_of_mem hy, SimpleFunc.const_apply]
        obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
        rw [section_apply_mul, section_apply_mul, characterRepresentation_apply,
          characterRepresentation_apply, mul_one, mul_one]
        congr 1
        linear_combination hθ' h
      · rw [Set.indicator_of_notMem hy, section_apply_of_not_mem H _ K hK _ _ hy, zero_mul,
          map_zero]
  rw [standardForm_apply, compactCoinvariantIntegral_apply, he,
    HarmonicAnalysis.AlgebraicIntegral.integral_indicator_const _ hm, map_smul, coinvariantValue,
    Representation.Coinvariants.lift_mk, LinearMap.id_apply, smul_eq_mul, mul_one]

end Standard

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Invariant forms on `c-Ind_H^G θ × π` embed linearly into the `(H, θ')`-equivariant
functionals on `π`, where `θ'` is the inverse of `θ`. -/
theorem exists_injective_formsFunctional [T2Space G]
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (θ : H →* ℂˣ)
    (hσ : IsSmooth (characterRepresentation θ)) (π : Representation ℂ G W) (hπ : IsSmooth π)
    [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
    [BorelSpace (QuotientIntegration.LeftQuotient H)]
    (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (θ' : H →* ℂˣ) (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1) :
    ∃ L : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
        (fun _ => (1 : ℂ)) →ₗ[ℂ] Whittaker.functionals H θ' π,
      Function.Injective L := by
  refine ⟨formsFunctional H θ π ν hinv hmass hG hσ hπ hθ', ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro B hB
  refine eq_zero_of_functional_eq_zero H θ π ν hH hinv hmass hG hσ hπ B ?_
  exact congrArg Subtype.val hB

/-- For inverse characters, the standard pairing `(f₁, f₂) ↦ ∫_{H \ G} f₁ f₂ dν` is a
nonzero invariant form on `c-Ind_H^G θ × c-Ind_H^G θ'`. -/
theorem exists_standardForm
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (H : Subgroup G) (θ θ' : H →* ℂˣ) (hσ : IsSmooth (characterRepresentation θ))
    (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
    [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
    [BorelSpace (QuotientIntegration.LeftQuotient H)]
    (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤) :
    ∃ B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ))
        (compactInduced H (characterRepresentation θ')) (fun _ => (1 : ℂ)), B ≠ 0 := by
  obtain ⟨K, hK, hv, -⟩ := exists_admissible H θ (compactInduced H (characterRepresentation θ'))
    hG hσ (compactInduced_smooth H _) 0
  have hv' : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ')
      (conjOpenSubgroup H K 1).toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants] at hv ⊢
    intro p
    have h1 : (θ (p : H) : ℂ) * 1 = 1 := hv p
    have h2 := hθ' p
    rw [mul_one] at h1
    rw [h1, mul_one] at h2
    change (θ' (p : H) : ℂ) * 1 = 1
    rw [h2, mul_one]
  refine ⟨standardForm H ν hθ', standardForm_mem H ν hinv hθ', fun h0 => ?_⟩
  have hs := standardForm_section H ν hθ' K hK hv hv'
  rw [h0, LinearMap.zero_apply, LinearMap.zero_apply] at hs
  obtain ⟨hpos, hfin⟩ := hmass K hK
  have hne : (ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  exact hne (by exact_mod_cast hs.symm)

end Main

end FormsFunctional

end Langlands.Induction
