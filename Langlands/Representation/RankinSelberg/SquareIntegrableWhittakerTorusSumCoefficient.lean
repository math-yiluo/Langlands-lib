import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.PrincipalLevelDominance
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Twist.ContinuousCharacterProof
import Mathlib.MeasureTheory.Group.Integral

/-!
# Whittaker values on the antidominant torus cone as smooth matrix coefficients

For a smooth representation `π` of `GL_(m+1)(F)`, a Whittaker functional `ℓ` and a
vector `v`, there are a positive principal level `K(r)` fixing `v` and a smooth
functional `L`, fixed by `K(r)`, such that `L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every
antitone exponent vector `lam`. The functional is the average
`L w = ∫_{K(r)} ℓ (π(g⁻¹) w) dg` for the Haar measure of unit mass on `K(r)`; the Iwahori
factorization of `K(r)` shows that the integrand is constant on the antitone cone.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum

universe uG uV uF

/-! ### Averaging a functional over a compact open subgroup -/

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
/-- For a smooth vector `w`, the function `g ↦ ℓ (ρ g⁻¹ w)` is locally constant. -/
theorem isLocallyConstant_apply_inv (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    {w : V} (hw : IsSmoothVector ρ w) :
    IsLocallyConstant (fun g : G => ℓ (ρ g⁻¹ w)) := by
  obtain ⟨H, hH⟩ := hw
  have hfix : ∀ h ∈ H, ρ h w = w := fun h hh =>
    (Representation.mem_invariants _ w).1 hH ⟨h, hh⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen {y : G | y * g⁻¹ ∈ (H : Set G)} :=
    H.isOpen.preimage (continuous_id.mul continuous_const)
  have hg : g ∈ {y : G | y * g⁻¹ ∈ (H : Set G)} := by
    simp only [Set.mem_ofPred_eq, mul_inv_cancel, SetLike.mem_coe]
    exact H.one_mem
  filter_upwards [hopen.mem_nhds hg] with y hy
  have h1 : y⁻¹ = g⁻¹ * (y * g⁻¹)⁻¹ := by group
  change ℓ (ρ y⁻¹ w) = ℓ (ρ g⁻¹ w)
  rw [h1, map_mul, Module.End.mul_apply, hfix _ (inv_mem (show y * g⁻¹ ∈ H from hy))]

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
  (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V)

include hρ in
theorem integrableOn_apply_inv (w : V) :
    IntegrableOn (fun g : G => ℓ (ρ g⁻¹ w)) (K : Set G) (normalizedCompactOpenHaar K hK) :=
  (isLocallyConstant_apply_inv ρ ℓ (hρ w)).continuous.continuousOn.integrableOn_compact' hK
    K.isOpen.measurableSet

/-- The average `w ↦ ∫_K ℓ (ρ g⁻¹ w) dg` of a functional over a compact open subgroup,
for the Haar measure giving `K` unit mass. -/
def averagedFunctional : Module.Dual ℂ V where
  toFun w := ∫ g in (K : Set G), ℓ (ρ g⁻¹ w) ∂(normalizedCompactOpenHaar K hK)
  map_add' w w' := by
    simp only [map_add]
    exact integral_add (integrableOn_apply_inv ρ hρ K hK ℓ w)
      (integrableOn_apply_inv ρ hρ K hK ℓ w')
  map_smul' c w := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem averagedFunctional_apply (w : V) :
    averagedFunctional ρ hρ K hK ℓ w =
      ∫ g in (K : Set G), ℓ (ρ g⁻¹ w) ∂(normalizedCompactOpenHaar K hK) :=
  rfl

/-- The averaged functional is invariant under `K`: `L (ρ k w) = L w`. -/
theorem averagedFunctional_apply_mul (k : G) (hk : k ∈ K) (w : V) :
    averagedFunctional ρ hρ K hK ℓ (ρ k w) = averagedFunctional ρ hρ K hK ℓ w := by
  rw [averagedFunctional_apply, averagedFunctional_apply,
    ← integral_indicator K.isOpen.measurableSet, ← integral_indicator K.isOpen.measurableSet]
  let f : G → ℂ := (K : Set G).indicator (fun g => ℓ (ρ g⁻¹ w))
  have hf : ((K : Set G).indicator fun g => ℓ (ρ g⁻¹ (ρ k w))) = fun g => f (k⁻¹ * g) := by
    funext g
    have hmem : g ∈ (K : Set G) ↔ k⁻¹ * g ∈ (K : Set G) := by
      simp only [SetLike.mem_coe]
      constructor
      · exact fun hg => K.mul_mem (K.inv_mem hk) hg
      · intro hg
        simpa using K.mul_mem hk hg
    show _ = (K : Set G).indicator (fun g => ℓ (ρ g⁻¹ w)) (k⁻¹ * g)
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.mp hg)]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.mpr h))]
  rw [hf]
  exact integral_mul_left_eq_self f k⁻¹

/-- The averaged functional lies in the `K`-fixed vectors of the full dual. -/
theorem averagedFunctional_mem_fixedVectors :
    averagedFunctional ρ hρ K hK ℓ ∈ fixedVectors ρ.dual K.toSubgroup := by
  rw [fixedVectors, Representation.mem_invariants]
  rintro ⟨k, hk⟩
  apply LinearMap.ext
  intro w
  change (ρ.dual k (averagedFunctional ρ hρ K hK ℓ)) w = averagedFunctional ρ hρ K hK ℓ w
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  exact averagedFunctional_apply_mul ρ hρ K hK ℓ k⁻¹ (K.inv_mem hk) w

/-- The averaged functional is smooth. -/
theorem averagedFunctional_mem_smoothVectors :
    averagedFunctional ρ hρ K hK ℓ ∈ smoothVectors ρ.dual :=
  ⟨K, averagedFunctional_mem_fixedVectors ρ hρ K hK ℓ⟩

/-- On vectors where the integrand is constant, the average is the original value. -/
theorem averagedFunctional_apply_of_forall {w : V} (hw : ∀ g ∈ K, ℓ (ρ g⁻¹ w) = ℓ w) :
    averagedFunctional ρ hρ K hK ℓ w = ℓ w := by
  rw [averagedFunctional_apply,
    setIntegral_congr_fun K.isOpen.measurableSet (fun g hg => hw g hg), setIntegral_const]
  simp [Measure.real, normalizedCompactOpenHaar_self]

end Averaging

/-! ### Principal levels and the antitone torus cone

The conjugation steps reuse the public `GeneralLinear.principal_upper_conj` and
`GeneralLinear.principal_lower_inv_conj` from
`Langlands.Group.GL.PrincipalLevelDominance`. -/

section Conjugation

open GeneralLinear

variable {k : Type uF} [Field k] [ValuativeRel k] {m r : ℕ} {ϖ : kˣ}

/-- Conjugation by an antitone torus element maps upper-unipotent elements of a principal
level into that level. -/
theorem torus_conj_upper_mem (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {lam : Fin (m + 1) → ℤ} (hlam : Antitone lam) {u : GeneralLinear (m + 1) k}
    (hu : u ∈ upperUnipotent (m + 1) k) (hK : u ∈ Conductor.principalLevelSubgroup k m r) :
    Iwasawa.torus ϖ lam * u * (Iwasawa.torus ϖ lam)⁻¹ ∈
      Conductor.principalLevelSubgroup k m r := by
  rw [torus_eq_blockScalar]
  refine principal_upper_conj (BlockShape.singletons (m + 1)) _ _ _
    (ratio_mem_integer hϖ hlam) ?_ hK
  rw [BlockShape.singletons_unipotentSubgroup]
  exact hu

/-- Inverse conjugation by an antitone torus element maps opposite-unipotent elements of a
principal level into that level. -/
theorem torus_inv_conj_lower_mem (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {lam : Fin (m + 1) → ℤ} (hlam : Antitone lam) {l : GeneralLinear (m + 1) k}
    (hl : l ∈ (BlockShape.singletons (m + 1)).oppositeUnipotentSubgroup k)
    (hK : l ∈ Conductor.principalLevelSubgroup k m r) :
    (Iwasawa.torus ϖ lam)⁻¹ * l * Iwasawa.torus ϖ lam ∈
      Conductor.principalLevelSubgroup k m r := by
  rw [torus_eq_blockScalar]
  exact principal_lower_inv_conj (BlockShape.singletons (m + 1)) _ _ _
    (ratio_mem_integer hϖ hlam) hl hK

omit [ValuativeRel k] in
/-- Torus elements commute with the singleton Levi subgroup. -/
theorem torus_commute_levi (lam : Fin (m + 1) → ℤ) {d : GeneralLinear (m + 1) k}
    (hd : d ∈ (BlockShape.singletons (m + 1)).leviSubgroup k) :
    Iwasawa.torus ϖ lam * d = d * Iwasawa.torus ϖ lam := by
  set S := BlockShape.singletons (m + 1)
  rw [torus_eq_blockScalar]
  obtain ⟨m₀, rfl⟩ := hd
  change S.leviEmbedding k (S.blockScalarLevi k _) * _ =
    _ * S.leviEmbedding k (S.blockScalarLevi k _)
  rw [← map_mul, ← map_mul, S.blockScalarLevi_commute]

/-- **The antitone cone.** If upper-unipotent elements of a positive principal level act
trivially through `ℓ` and the level fixes `v`, then for every element `g` of the level and
every antitone torus element `a`, `ℓ (π(g⁻¹) π(a) v) = ℓ (π(a) v)`. -/
theorem apply_inv_torus_eq {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (m + 1) k) V} {ℓ : Module.Dual ℂ V} (hr : 0 < r)
    (hℓ : ∀ u ∈ upperUnipotent (m + 1) k, u ∈ Conductor.principalLevelSubgroup k m r →
      ∀ w, ℓ (π u w) = ℓ w)
    {v : V} (hv : ∀ g ∈ Conductor.principalLevelSubgroup k m r, π g v = v)
    (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) {lam : Fin (m + 1) → ℤ} (hlam : Antitone lam)
    {g : GeneralLinear (m + 1) k} (hg : g ∈ Conductor.principalLevelSubgroup k m r) :
    ℓ (π g⁻¹ (π (Iwasawa.torus ϖ lam) v)) = ℓ (π (Iwasawa.torus ϖ lam) v) := by
  set S := BlockShape.singletons (m + 1)
  set P := Conductor.principalLevelSubgroup k m r
  set a := Iwasawa.torus ϖ lam
  obtain ⟨⟨l, d, u⟩, hldu⟩ :=
    BlockShape.principalLevelSubgroup_iwahoriProduct_surjective k m S r hr ⟨g, hg⟩
  have hval := congrArg Subtype.val hldu
  rw [BlockShape.iwahoriProduct_val] at hval
  have hval' : l.val * d.val * u.val = g := hval
  obtain ⟨hlP, hlS⟩ := Subgroup.mem_inf.mp l.property
  obtain ⟨hdP, hdS⟩ := Subgroup.mem_inf.mp d.property
  obtain ⟨huP, huS⟩ := Subgroup.mem_inf.mp u.property
  have hginv : g⁻¹ * a = u.val⁻¹ * a * (d.val⁻¹ * (a⁻¹ * l.val⁻¹ * a)) := by
    have hcomm : a * d.val⁻¹ = d.val⁻¹ * a :=
      torus_commute_levi lam ((S.leviSubgroup k).inv_mem hdS)
    calc g⁻¹ * a = u.val⁻¹ * (d.val⁻¹ * a) * (a⁻¹ * l.val⁻¹ * a) := by
          rw [← hval']
          group
      _ = u.val⁻¹ * (a * d.val⁻¹) * (a⁻¹ * l.val⁻¹ * a) := by rw [hcomm]
      _ = _ := by group
  have hy : d.val⁻¹ * (a⁻¹ * l.val⁻¹ * a) ∈ P :=
    mul_mem (inv_mem hdP) (torus_inv_conj_lower_mem hϖ hlam
      ((S.oppositeUnipotentSubgroup k).inv_mem hlS) (inv_mem hlP))
  have huN : u.val⁻¹ ∈ upperUnipotent (m + 1) k := by
    have := (S.unipotentSubgroup k).inv_mem huS
    rwa [BlockShape.singletons_unipotentSubgroup] at this
  rw [← Module.End.mul_apply, ← map_mul, hginv, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, hv _ hy]
  exact hℓ _ huN (inv_mem huP) _

end Conjugation

/-! ### Smooth functionals agreeing with a Whittaker functional on the antitone cone -/

section Coefficient

open GeneralLinear Whittaker HarmonicAnalysis

/-- For a smooth representation of `GL_(m+1)(F)`, a standard Whittaker functional `ℓ`, a
vector `v` and an element `ϖ` of valuation at most one, there are a positive principal level
`K(r)` fixing `v` and a smooth functional `L`, invariant under `K(r)`, with
`L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every antitone exponent vector `lam`. -/
theorem exists_smooth_eq_on_antitone {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V),
      IsSmooth π → ∀ (ℓ : glFunctionals ψ m π) (v : V) (ϖ : F.Carrierˣ),
      ValuativeRel.valuation F.Carrier (ϖ : F.Carrier) ≤ 1 →
      ∃ r : ℕ, 0 < r ∧
        (∀ g ∈ Conductor.principalLevelSubgroup F.Carrier m r, π g v = v) ∧
        ∃ L : Module.Dual ℂ V, L ∈ smoothVectors π.dual ∧
          (∀ g ∈ Conductor.principalLevelSubgroup F.Carrier m r, ∀ w, L (π g w) = L w) ∧
          ∀ lam : Fin (m + 1) → ℤ, Antitone lam →
            L (π (Iwasawa.torus ϖ lam) v) = ℓ.val (π (Iwasawa.torus ϖ lam) v) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1)
  intro ψ V _ _ π hπ ℓ v ϖ hϖ
  let := borel (Langlands.GeneralLinear (m + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
  -- A level fixing `v`.
  obtain ⟨Kv, hKv⟩ := hπ v
  have hfix : ∀ g ∈ Kv, π g v = v := fun g hg =>
    (Representation.mem_invariants _ v).1 hKv ⟨g, hg⟩
  obtain ⟨r₁, hr₁, hK₁⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier m
    (Kv.isOpen.mem_nhds Kv.one_mem)
  -- A level inside the kernel of the standard character.
  have hker : IsOpen ((standardCharacter ψ m).ker : Set (upperUnipotent (m + 1) F.Carrier)) := by
    let := T.upperUnipotentNonarchimedean (m + 1)
    exact isOpen_ker_of_continuous_complex_character _
      (standardCharacterContinuous ψ m).continuous
  have hN := hker.mem_nhds (standardCharacter ψ m).ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨O, hO, hOK⟩ := hN
  obtain ⟨r₂, -, hK₂⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier m hO
  set r := max r₁ r₂
  have hr : 0 < r := lt_max_of_lt_left hr₁
  have hv : ∀ g ∈ Conductor.principalLevelSubgroup F.Carrier m r, π g v = v := fun g hg =>
    hfix g (hK₁ (Conductor.principalLevelSubgroup_antitone F.Carrier m (le_max_left _ _) hg))
  have hℓ : ∀ u ∈ upperUnipotent (m + 1) F.Carrier,
      u ∈ Conductor.principalLevelSubgroup F.Carrier m r → ∀ w, ℓ.val (π u w) = ℓ.val w := by
    intro u hu hK w
    have h₁ : u ∈ O :=
      hK₂ (Conductor.principalLevelSubgroup_antitone F.Carrier m (le_max_right _ _) hK)
    have h₂ : (⟨u, hu⟩ : upperUnipotent (m + 1) F.Carrier) ∈ Subtype.val ⁻¹' O := h₁
    have hθ := MonoidHom.mem_ker.mp (hOK h₂)
    have h := ℓ.property ⟨u, hu⟩ w
    rw [hθ, Units.val_one, one_mul] at h
    exact h
  let K := Conductor.principalLevelOpenSubgroup F.Carrier m r
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    Conductor.isCompact_principalLevelOpenSubgroup F.Carrier m r
  refine ⟨r, hr, hv, averagedFunctional π hπ K hK ℓ.val,
    averagedFunctional_mem_smoothVectors π hπ K hK ℓ.val,
    fun g hg w => averagedFunctional_apply_mul π hπ K hK ℓ.val g hg w, ?_⟩
  intro lam hlam
  exact averagedFunctional_apply_of_forall π hπ K hK ℓ.val
    (fun g hg => apply_inv_torus_eq hr hℓ hv hϖ hlam hg)

end Coefficient

end Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum
