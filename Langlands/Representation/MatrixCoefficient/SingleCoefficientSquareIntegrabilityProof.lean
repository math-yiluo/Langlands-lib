import Langlands.Representation.MatrixCoefficient.SingleCoefficientSquareIntegrabilityStatement
import Langlands.Representation.MatrixCoefficient.SquareIntegrableCoefficientCriterionProof
import Langlands.Representation.MatrixCoefficient.HeckeOperator
import Langlands.Analysis.TracialFiniteness
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Plancherel.CompactIntertwiningCompression

/-! # One square-integrable coefficient suffices, without assumed admissibility

Renard IV.3.2, Remark. Let `π` be an irreducible smooth representation of a t.d. group `G`
with a unitary central character, and suppose that one nonzero smooth matrix coefficient
`g ↦ ℓ(π(g) x)` is square-integrable modulo the centre. Then every smooth matrix coefficient
is square-integrable modulo the centre.

The proof shows that `π` is admissible and then applies the admissible form
`squareIntegrableCoefficientCriterion`. For a small compact open subgroup `K`, the map
`y ↦ (g ↦ ℓ(π(g) y))` embeds the `K`-fixed vectors into the twisted `ℓ²` space of
`G ⧸ K Z(G)`. The Hecke operators act transitively on the image and commute with the left
translations, and the commutant of the left translations has a faithful tracial vector.
`Langlands.Analysis.finiteDimensional_of_tracial'` then makes the image finite dimensional.
-/

noncomputable section

universe u v

open MeasureTheory
open scoped ENNReal

namespace Langlands.Renard.CompactRepresentation

namespace SingleCoefficient

section CenterMul

variable {G : Type*} [Group G] (K : Subgroup G)

/-- The subgroup `K · Z(G)`. -/
def centerMul : Subgroup G where
  carrier := {g | ∃ k ∈ K, ∃ z ∈ Subgroup.center G, g = k * z}
  one_mem' := ⟨1, K.one_mem, 1, (Subgroup.center G).one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨k, hk, z, hz, rfl⟩ ⟨k', hk', z', hz', rfl⟩
    refine ⟨k * k', K.mul_mem hk hk', z * z', (Subgroup.center G).mul_mem hz hz', ?_⟩
    have hc : k' * z = z * k' := Subgroup.mem_center_iff.mp hz k'
    calc k * z * (k' * z') = k * (z * k') * z' := by simp only [mul_assoc]
      _ = k * (k' * z) * z' := by rw [hc]
      _ = k * k' * (z * z') := by simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨k, hk, z, hz, rfl⟩
    refine ⟨k⁻¹, K.inv_mem hk, z⁻¹, (Subgroup.center G).inv_mem hz, ?_⟩
    have hc : k⁻¹ * z⁻¹ = z⁻¹ * k⁻¹ :=
      Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz) k⁻¹
    rw [mul_inv_rev, hc]

theorem mem_centerMul_iff {g : G} :
    g ∈ centerMul K ↔ ∃ k ∈ K, ∃ z ∈ Subgroup.center G, g = k * z :=
  Iff.rfl

theorem center_le_centerMul : Subgroup.center G ≤ centerMul K :=
  fun z hz => ⟨1, K.one_mem, z, hz, (one_mul z).symm⟩

theorem le_centerMul : K ≤ centerMul K :=
  fun k hk => ⟨k, hk, 1, (Subgroup.center G).one_mem, (mul_one k).symm⟩

/-- The central factor chosen for an element of `K · Z(G)`. -/
def centerPart (j : centerMul K) : Subgroup.center G :=
  ⟨j.2.choose_spec.2.choose, j.2.choose_spec.2.choose_spec.1⟩

theorem exists_eq_mul_centerPart (j : centerMul K) :
    ∃ k ∈ K, (j : G) = k * (centerPart K j : G) :=
  ⟨j.2.choose, j.2.choose_spec.1, j.2.choose_spec.2.choose_spec.2⟩

variable {K} (χ : Subgroup.center G →* ℂˣ)
  (hKχ : ∀ (z : G) (hz : z ∈ Subgroup.center G), z ∈ K → χ ⟨z, hz⟩ = 1)

include hKχ in
/-- `χ` of the central factor does not depend on the decomposition `j = k * z`. -/
theorem char_centerPart (j : centerMul K) {k z : G} (hk : k ∈ K)
    (hz : z ∈ Subgroup.center G) (h : (j : G) = k * z) :
    χ (centerPart K j) = χ ⟨z, hz⟩ := by
  obtain ⟨k', hk', h'⟩ := exists_eq_mul_centerPart K j
  have e : k' * (centerPart K j : G) = k * z := h'.symm.trans h
  have hmem : (centerPart K j : G) * z⁻¹ ∈ K := by
    have heq : (centerPart K j : G) * z⁻¹ = k'⁻¹ * k :=
      calc (centerPart K j : G) * z⁻¹ = k'⁻¹ * (k' * (centerPart K j : G)) * z⁻¹ := by
            group
        _ = k'⁻¹ * (k * z) * z⁻¹ := by rw [e]
        _ = k'⁻¹ * k := by group
    rw [heq]
    exact K.mul_mem (K.inv_mem hk') hk
  have hzc : (centerPart K j : G) * z⁻¹ ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem (centerPart K j).2 ((Subgroup.center G).inv_mem hz)
  have hsplit : centerPart K j = ⟨_, hzc⟩ * ⟨z, hz⟩ := by
    apply Subtype.ext
    simp
  rw [hsplit, map_mul, hKχ _ hzc hmem, one_mul]

/-- The character `k z ↦ χ z` of `K · Z(G)`, well defined since `χ` is trivial on
`K ∩ Z(G)`. -/
def centerChar : centerMul K →* ℂ where
  toFun j := (χ (centerPart K j) : ℂ)
  map_one' := by
    have h := char_centerPart χ hKχ (1 : centerMul K) K.one_mem (Subgroup.center G).one_mem
      (mul_one (1 : G)).symm
    show ((χ (centerPart K 1) : ℂˣ) : ℂ) = 1
    rw [h]
    show ((χ 1 : ℂˣ) : ℂ) = 1
    rw [map_one, Units.val_one]
  map_mul' a b := by
    obtain ⟨k, hk, ha⟩ := exists_eq_mul_centerPart K a
    obtain ⟨k', hk', hb⟩ := exists_eq_mul_centerPart K b
    have hc : k' * (centerPart K a : G) = (centerPart K a : G) * k' :=
      Subgroup.mem_center_iff.mp (centerPart K a).2 k'
    have hab : ((a * b : centerMul K) : G) =
        (k * k') * ((centerPart K a : G) * (centerPart K b : G)) := by
      rw [Subgroup.coe_mul, ha, hb]
      calc k * (centerPart K a : G) * (k' * (centerPart K b : G))
          = k * ((centerPart K a : G) * k') * (centerPart K b : G) := by
            simp only [mul_assoc]
        _ = k * (k' * (centerPart K a : G)) * (centerPart K b : G) := by rw [hc]
        _ = (k * k') * ((centerPart K a : G) * (centerPart K b : G)) := by
            simp only [mul_assoc]
    show ((χ (centerPart K (a * b)) : ℂˣ) : ℂ) =
      ((χ (centerPart K a) : ℂˣ) : ℂ) * ((χ (centerPart K b) : ℂˣ) : ℂ)
    rw [char_centerPart χ hKχ (a * b) (K.mul_mem hk hk')
      ((Subgroup.center G).mul_mem (centerPart K a).2 (centerPart K b).2) hab]
    show ((χ (centerPart K a * centerPart K b) : ℂˣ) : ℂ) =
      ((χ (centerPart K a) : ℂˣ) : ℂ) * ((χ (centerPart K b) : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul]

theorem centerChar_apply (j : centerMul K) :
    centerChar χ hKχ j = (χ (centerPart K j) : ℂ) :=
  rfl

theorem centerChar_eq (j : centerMul K) {k z : G} (hk : k ∈ K)
    (hz : z ∈ Subgroup.center G) (h : (j : G) = k * z) :
    centerChar χ hKχ j = (χ ⟨z, hz⟩ : ℂ) := by
  rw [centerChar_apply, char_centerPart χ hKχ j hk hz h]

theorem centerChar_of_mem (k : G) (hk : k ∈ K) :
    centerChar χ hKχ ⟨k, le_centerMul K hk⟩ = 1 := by
  rw [centerChar_eq χ hKχ ⟨k, le_centerMul K hk⟩ hk (Subgroup.center G).one_mem
    (mul_one k).symm]
  show ((χ 1 : ℂˣ) : ℂ) = 1
  rw [map_one, Units.val_one]

end CenterMul

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_centerMul (K : OpenSubgroup G) : IsOpen (centerMul (K : Subgroup G) : Set G) :=
  Subgroup.isOpen_mono (le_centerMul (K : Subgroup G)) K.isOpen

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The image of `K · Z(G)` in `G ⧸ Z(G)` is the image of `K`. -/
theorem centralImage_centerMul_subset (K : Subgroup G) :
    CentralCoset.centralImage (centerMul K) ⊆ QuotientGroup.mk '' (K : Set G) := by
  intro q hq
  obtain ⟨k, hk, z, hz, hkz⟩ := (hq : q.out ∈ centerMul K)
  refine ⟨k, hk, ?_⟩
  rw [← QuotientGroup.out_eq' q, hkz]
  apply QuotientGroup.eq.mpr
  simpa using hz

omit [IsTopologicalGroup G] in
theorem centralImage_centerMul_ne_top [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)] (μ : Measure (G ⧸ Subgroup.center G))
    [μ.IsHaarMeasure] (K : Subgroup G) (hKc : IsCompact (K : Set G)) :
    μ (CentralCoset.centralImage (centerMul K)) ≠ ∞ :=
  ((measure_mono (centralImage_centerMul_subset K)).trans_lt
    (hKc.image QuotientGroup.continuous_mk).measure_lt_top).ne

/-- The Hecke subgroups of a compact open subgroup have finite index. -/
theorem finite_quotient_heckeSub (K : OpenSubgroup G) (hKc : IsCompact (K : Set G)) (g : G) :
    Finite (K ⧸ TwistedCoset.heckeSub K g) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  have hopen : IsOpen (TwistedCoset.heckeSub K g : Set K) := by
    have hset : (TwistedCoset.heckeSub K g : Set K) =
        (fun k : K => g⁻¹ * (k : G) * g) ⁻¹' (K : Set G) := rfl
    rw [hset]
    exact IsOpen.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
      K.isOpen
  exact Subgroup.quotient_finite_of_isOpen _ hopen

/-- A compact open subgroup inside `K₀` on whose central elements `χ` is trivial. -/
theorem exists_compact_le_ker [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (χ : Subgroup.center G →* ℂˣ) (hχ : IsOpen (χ.ker : Set (Subgroup.center G)))
    (K₀ : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ K₀ ∧
      ∀ (z : G) (hz : z ∈ Subgroup.center G), z ∈ (K : Subgroup G) → χ ⟨z, hz⟩ = 1 := by
  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp hχ
  have h1 : (1 : G) ∈ t := by
    have h : (1 : Subgroup.center G) ∈ (χ.ker : Set (Subgroup.center G)) := χ.ker.one_mem
    rw [← hteq] at h
    exact h
  have hW : t ∩ (K₀ : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem (ht.mem_nhds h1) K₀.mem_nhds_one
  obtain ⟨K, hKc, hKW⟩ :=
    ((Topology.LocallyProfiniteProof.vanDantzig G).mp Topology.isLocallyProfinite_of_mathlib).2
      _ hW
  refine ⟨K, hKc, fun k hk => (hKW hk).2, fun z hz hzK => ?_⟩
  have hzt : z ∈ t := (hKW hzK).1
  have hker : (⟨z, hz⟩ : Subgroup.center G) ∈ (χ.ker : Set (Subgroup.center G)) := by
    rw [← hteq]
    exact hzt
  exact MonoidHom.mem_ker.mp hker

end Topology

section IntegrableVectors

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (c : UnitaryCentralCharacter ρ)
  (μ : Measure (G ⧸ Subgroup.center G))

/-- Vectors whose coefficient for a fixed functional is square-integrable modulo the
centre. -/
def integrableVectors (ℓ : Module.Dual ℂ V) : Submodule ℂ V where
  carrier := {x | MemLp (c.coefficientNorm ℓ x) 2 μ}
  zero_mem' := by
    have hz : c.coefficientNorm ℓ 0 = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    change MemLp _ 2 μ
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro x y hx hy
    refine (hx.add hy).mono' (c.aestronglyMeasurable_coefficientNorm ℓ (x + y)
      (hρ (x + y)) μ) ?_
    filter_upwards with q
    rw [Real.norm_of_nonneg (c.coefficientNorm_nonneg ℓ (x + y) q)]
    induction q using Quotient.inductionOn with
    | h g =>
      change ‖ℓ (ρ g (x + y))‖ ≤ ‖ℓ (ρ g x)‖ + ‖ℓ (ρ g y)‖
      simpa only [map_add] using norm_add_le (ℓ (ρ g x)) (ℓ (ρ g y))
  smul_mem' := by
    intro a x hx
    have hs : c.coefficientNorm ℓ (a • x) = ‖a‖ • c.coefficientNorm ℓ x := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    change MemLp _ 2 μ
    rw [hs]
    exact hx.const_smul ‖a‖

/-- Right translation preserves square-integrability of a coefficient. -/
theorem memLp_coefficientNorm_rho [μ.IsMulRightInvariant]
    (ℓ : Module.Dual ℂ V) (x : V) (hx : MemLp (c.coefficientNorm ℓ x) 2 μ) (g : G) :
    MemLp (c.coefficientNorm ℓ (ρ g x)) 2 μ := by
  have hp : MeasurePreserving
      (fun q : G ⧸ Subgroup.center G => q * QuotientGroup.mk g) μ μ :=
    ⟨(continuous_id.mul_const _).measurable, map_mul_right_eq_self μ _⟩
  have heq : c.coefficientNorm ℓ (ρ g x) =
      c.coefficientNorm ℓ x ∘ (fun q => q * QuotientGroup.mk g) := by
    funext q
    induction q using Quotient.inductionOn with
    | h k =>
      change ‖ℓ (ρ k (ρ g x))‖ = ‖ℓ (ρ (k * g) x)‖
      rw [map_mul, Module.End.mul_apply]
  rw [heq]
  exact hx.comp_measurePreserving hp

include hρ in
/-- For an irreducible representation, one nonzero square-integrable coefficient vector
for `ℓ` makes the coefficient of every vector for `ℓ` square-integrable. -/
theorem memLp_coefficientNorm_of_irreducible [μ.IsMulRightInvariant] (hirr : ρ.IsIrreducible)
    (ℓ : Module.Dual ℂ V) {x : V} (hx0 : x ≠ 0) (hx : MemLp (c.coefficientNorm ℓ x) 2 μ)
    (y : V) : MemLp (c.coefficientNorm ℓ y) 2 μ := by
  have hspan : Submodule.span ℂ (Set.range fun g : G => ρ g x) ≤
      integrableVectors hρ c μ ℓ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact memLp_coefficientNorm_rho c μ ℓ x hx g
  rw [span_range_orbit_eq_top hirr hx0] at hspan
  exact hspan Submodule.mem_top

end IntegrableVectors

section Coefficient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (c : UnitaryCentralCharacter ρ) (K : OpenSubgroup G)
  (hKχ : ∀ (z : G) (hz : z ∈ Subgroup.center G), z ∈ (K : Subgroup G) →
    c.character ⟨z, hz⟩ = 1)
  (ℓ : Module.Dual ℂ V)

omit [IsTopologicalGroup G] [MeasurableSpace (G ⧸ Subgroup.center G)]
  [BorelSpace (G ⧸ Subgroup.center G)] in
theorem norm_centerChar (j : centerMul (K : Subgroup G)) :
    ‖centerChar c.character hKχ j‖ = 1 :=
  c.norm_eq_one _

omit [IsTopologicalGroup G] [MeasurableSpace (G ⧸ Subgroup.center G)]
  [BorelSpace (G ⧸ Subgroup.center G)] in
/-- A coefficient of a `K`-fixed vector is `ψ`-equivariant on the right. -/
theorem coefficient_mul (y : V) (hy : y ∈ fixedVectors ρ K.toSubgroup) (g j : G)
    (hj : j ∈ centerMul (K : Subgroup G)) :
    ℓ (ρ (g * j) y) = ℓ (ρ g y) * centerChar c.character hKχ ⟨j, hj⟩ := by
  obtain ⟨k, hk, z, hz, hjkz⟩ := id hj
  rw [centerChar_eq c.character hKχ ⟨j, hj⟩ hk hz hjkz, hjkz, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply]
  have hzy : ρ z y = (c.character ⟨z, hz⟩ : ℂ) • y := c.acts ⟨z, hz⟩ y
  have hky : ρ k y = y := hy ⟨k, hk⟩
  rw [hzy, map_smul, hky, map_smul, map_smul, smul_eq_mul, mul_comm]

include hKχ in
/-- The coefficient of a `K`-fixed vector with square-integrable coefficient is square
summable over `G ⧸ K Z(G)`. -/
theorem tsum_coefficient_ne_top (y : V) (hy : y ∈ fixedVectors ρ K.toSubgroup)
    (hL2 : MemLp (c.coefficientNorm ℓ y) 2 μ) :
    ∑' α : G ⧸ centerMul (K : Subgroup G), ‖ℓ (ρ α.out y)‖ₑ ^ 2 ≠ ∞ := by
  let Φ : G → ℝ≥0∞ := fun g => ‖ℓ (ρ g y)‖ₑ ^ 2
  have hΦ : ∀ g, ∀ j ∈ centerMul (K : Subgroup G), Φ (g * j) = Φ g := by
    intro g j hj
    simp only [Φ]
    rw [coefficient_mul c K hKχ ℓ y hy g j hj, enorm_mul,
      TwistedCoset.enorm_eq_one_of_norm_eq_one (norm_centerChar c K hKχ _), mul_one]
  have h := CentralCoset.lintegral_out_eq_mul_tsum (centerMul (K : Subgroup G))
    (center_le_centerMul _) (isOpen_centerMul K) μ Φ hΦ
  have hlt : ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ < ∞ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hL2.eLpNorm_lt_top
    refine lt_of_eq_of_lt (lintegral_congr fun q => ?_) h2
    simp only [Φ]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [UnitaryCentralCharacter.coefficientNorm_mk, enorm_norm, ENNReal.toReal_ofNat,
      ENNReal.rpow_two]
    rfl
  intro htop
  rw [htop, ENNReal.mul_top (CentralCoset.centralImage_measure_ne_zero _
    (center_le_centerMul _) (isOpen_centerMul K) μ)] at h
  rw [h] at hlt
  exact lt_irrefl _ hlt

variable (hall : ∀ y : V, MemLp (c.coefficientNorm ℓ y) 2 μ)

include hKχ hall in
/-- The coefficient map `y ↦ (α ↦ ℓ(π(α.out) y))` from the `K`-fixed vectors to the twisted
`ℓ²` space of `G ⧸ K Z(G)`. -/
def coeffMap :
    fixedVectors ρ K.toSubgroup →ₗ[ℂ] TwistedCoset.L2 (centerMul (K : Subgroup G)) where
  toFun y := ⟨fun α => ℓ (ρ α.out y),
    Langlands.Analysis.memℓp_two_of_tsum_enorm_ne_top _
      (tsum_coefficient_ne_top μ c K hKχ ℓ y y.2 (hall y))⟩
  map_add' y y' := by
    ext α
    change ℓ (ρ α.out ((y + y' : fixedVectors ρ K.toSubgroup) : V)) =
      ℓ (ρ α.out y) + ℓ (ρ α.out y')
    rw [Submodule.coe_add, map_add, map_add]
  map_smul' a y := by
    ext α
    change ℓ (ρ α.out ((a • y : fixedVectors ρ K.toSubgroup) : V)) = a * ℓ (ρ α.out y)
    rw [Submodule.coe_smul, map_smul, map_smul, smul_eq_mul]

theorem coeffMap_apply (y : fixedVectors ρ K.toSubgroup) (α : G ⧸ centerMul (K : Subgroup G)) :
    coeffMap μ c K hKχ ℓ hall y α = ℓ (ρ α.out y) :=
  rfl

/-- The lift of `coeffMap y` is the full coefficient `g ↦ ℓ(π(g) y)`. -/
theorem lift_coeffMap (y : fixedVectors ρ K.toSubgroup) :
    TwistedCoset.lift (centerMul (K : Subgroup G)) (centerChar c.character hKχ)
      (coeffMap μ c K hKχ ℓ hall y) = fun g => ℓ (ρ g y) :=
  TwistedCoset.lift_restrict _ _ (fun g => ℓ (ρ g y))
    (fun g j hj => coefficient_mul c K hKχ ℓ y y.2 g j hj)

/-- For an irreducible representation and `ℓ ≠ 0`, the coefficient map is injective. -/
theorem coeffMap_injective (hirr : ρ.IsIrreducible) (hℓ : ℓ ≠ 0) :
    Function.Injective (coeffMap μ c K hKχ ℓ hall) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  by_contra hne
  have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
  have hg : ∀ g : G, ℓ (ρ g y) = 0 := by
    intro g
    have h1 : ℓ (ρ g y) = TwistedCoset.lift (centerMul (K : Subgroup G))
        (centerChar c.character hKχ) (coeffMap μ c K hKχ ℓ hall y) g :=
      (congrFun (lift_coeffMap μ c K hKχ ℓ hall y) g).symm
    rw [h1, hy]
    simp [TwistedCoset.lift]
  apply hℓ
  have hle : Submodule.span ℂ (Set.range fun g : G => ρ g y) ≤ LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hg g
  rw [span_range_orbit_eq_top hirr hy0] at hle
  ext v
  exact hle Submodule.mem_top

end Coefficient

section Hecke

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
  (c : UnitaryCentralCharacter ρ) (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
  (hKχ : ∀ (z : G) (hz : z ∈ Subgroup.center G), z ∈ (K : Subgroup G) →
    c.character ⟨z, hz⟩ = 1)
  (ℓ : Module.Dual ℂ V) (hall : ∀ y : V, MemLp (c.coefficientNorm ℓ y) 2 μ)

/-- The average over `K`, as a map onto the `K`-fixed vectors. -/
def averageFixed : V →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
  LinearMap.codRestrict (fixedVectors ρ K.toSubgroup) (Compact.averageMap ρ hρ K hKc)
    (Compact.averageMap_mem_fixedVectors ρ hρ K hKc)

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coe_averageFixed (v : V) :
    (averageFixed hρ K hKc v : V) = Compact.averageMap ρ hρ K hKc v :=
  rfl

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem averageFixed_of_mem (y : fixedVectors ρ K.toSubgroup) :
    averageFixed hρ K hKc (y : V) = y :=
  Subtype.ext (Compact.averageMap_id ρ hρ K hKc y y.2)

/-- The Hecke operator `hecke g` sends the coefficient of `y` to the coefficient of the
`K`-average of `π(g) y`. -/
theorem hecke_coeffMap (g : G) [Fintype (K ⧸ TwistedCoset.heckeSub K g)]
    (hb : ∀ F : TwistedCoset.L2 (centerMul (K : Subgroup G)),
      ∑' α : G ⧸ centerMul (K : Subgroup G),
        ‖TwistedCoset.heckeFun K (centerMul (K : Subgroup G)) (centerChar c.character hKχ) g
          F α.out‖ₑ ^ 2 ≤ ‖F‖ₑ ^ 2)
    (y : fixedVectors ρ K.toSubgroup) :
    TwistedCoset.hecke g hb (coeffMap μ c K hKχ ℓ hall y) =
      coeffMap μ c K hKχ ℓ hall (averageFixed hρ K hKc (ρ g y)) := by
  have hL : ∀ l : TwistedCoset.heckeSub K g, ρ ((l : K) : G) (ρ g y) = ρ g y := by
    intro l
    have hl : g⁻¹ * ((l : K) : G) * g ∈ K := l.2
    have hfix : ρ (g⁻¹ * ((l : K) : G) * g) y = y := y.2 ⟨_, hl⟩
    have h1 : ((l : K) : G) * g = g * (g⁻¹ * ((l : K) : G) * g) := by group
    calc ρ ((l : K) : G) (ρ g y) = ρ (((l : K) : G) * g) y := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * (g⁻¹ * ((l : K) : G) * g)) y := by rw [h1]
      _ = ρ g (ρ (g⁻¹ * ((l : K) : G) * g) y) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ g y := by rw [hfix]
  ext α
  rw [TwistedCoset.hecke_apply, coeffMap_apply, coe_averageFixed,
    Plancherel.averageMap_eq_finiteMean_cosets ρ hρ K hKc (TwistedCoset.heckeSub K g)
      (ρ g y) hL]
  unfold TwistedCoset.heckeFun Compact.finiteMean
  rw [map_smul, map_sum, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lift_coeffMap]
  simp only [map_mul, Module.End.mul_apply]

end Hecke

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
  (hirr : ρ.IsIrreducible) (c : UnitaryCentralCharacter ρ)

include hρ hirr in
/-- If some nonzero functional has square-integrable coefficients for all vectors, then the
vectors fixed by a small compact open subgroup form a finite-dimensional space. -/
theorem finiteDimensional_fixedVectors (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    (hKχ : ∀ (z : G) (hz : z ∈ Subgroup.center G), z ∈ (K : Subgroup G) →
      c.character ⟨z, hz⟩ = 1)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) (hall : ∀ y : V, MemLp (c.coefficientNorm ℓ y) 2 μ) :
    FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := by
  classical
  have hψ : ∀ j, ‖centerChar c.character hKχ j‖ = 1 := norm_centerChar c K hKχ
  have hKJ : ∀ k ∈ K, k ∈ centerMul (K : Subgroup G) := fun k hk => le_centerMul _ hk
  have hψK : ∀ (k : G) (hk : k ∈ K), centerChar c.character hKχ ⟨k, hKJ k hk⟩ = 1 :=
    fun k hk => centerChar_of_mem c.character hKχ k hk
  have hZJ : Subgroup.center G ≤ centerMul (K : Subgroup G) := center_le_centerMul _
  have hJ : IsOpen (centerMul (K : Subgroup G) : Set G) := isOpen_centerMul K
  have hJKZ : ∀ j ∈ centerMul (K : Subgroup G), ∃ k ∈ K, ∃ z ∈ Subgroup.center G,
      j = k * z := fun j hj => hj
  have hfin : μ (CentralCoset.centralImage (centerMul (K : Subgroup G))) ≠ ∞ :=
    centralImage_centerMul_ne_top μ _ hKc
  let A := coeffMap μ c K hKχ ℓ hall
  let C := StarSubalgebra.centralizer ℂ (TwistedCoset.translates hψ)
  have key : ∀ y : fixedVectors ρ K.toSubgroup, ∀ v ∈ Submodule.span ℂ
      (Set.range fun g : G => ρ g y), ∃ b ∈ C,
        (∀ w ∈ LinearMap.range A, b w ∈ LinearMap.range A) ∧
          b (A y) = A (averageFixed hρ K hKc v) := by
    intro y v hv
    induction hv using Submodule.span_induction with
    | mem v hv' =>
      obtain ⟨g, rfl⟩ := hv'
      have := finite_quotient_heckeSub K hKc g
      let : Fintype (K ⧸ TwistedCoset.heckeSub K g) := Fintype.ofFinite _
      have hb := TwistedCoset.tsum_enorm_heckeFun_le hψ hKJ hZJ hJ hJKZ μ hfin g
      refine ⟨TwistedCoset.hecke g hb,
        TwistedCoset.hecke_mem_centralizer g hb hψ hKJ hψK hZJ hJKZ, ?_,
        hecke_coeffMap μ hρ c K hKc hKχ ℓ hall g hb y⟩
      rintro _ ⟨y', rfl⟩
      exact ⟨averageFixed hρ K hKc (ρ g y'),
        (hecke_coeffMap μ hρ c K hKc hKχ ℓ hall g hb y').symm⟩
    | zero =>
      refine ⟨0, zero_mem C, fun w _ => ?_, ?_⟩
      · rw [zero_apply]
        exact zero_mem _
      · rw [zero_apply, map_zero, map_zero]
    | add v w _ _ hv hw =>
      obtain ⟨b, hbC, hbV, hbe⟩ := hv
      obtain ⟨b', hbC', hbV', hbe'⟩ := hw
      refine ⟨b + b', add_mem hbC hbC', fun u hu => ?_, ?_⟩
      · rw [add_apply]
        exact add_mem (hbV u hu) (hbV' u hu)
      · rw [add_apply, hbe, hbe', map_add, map_add]
    | smul a v _ hv =>
      obtain ⟨b, hbC, hbV, hbe⟩ := hv
      refine ⟨a • b, SMulMemClass.smul_mem a hbC, fun u hu => ?_, ?_⟩
      · rw [smul_apply]
        exact Submodule.smul_mem _ a (hbV u hu)
      · rw [smul_apply, hbe, map_smul, map_smul]
  have htrans : ∀ u w : LinearMap.range A, u ≠ 0 →
      ∃ b ∈ C, (∀ v ∈ LinearMap.range A, b v ∈ LinearMap.range A) ∧ b u = w := by
    rintro ⟨_, y, rfl⟩ ⟨_, y', rfl⟩ hu
    have hy0 : (y : V) ≠ 0 := by
      intro h
      apply hu
      have hy : y = 0 := Subtype.ext h
      apply Subtype.ext
      change A y = 0
      rw [hy, map_zero]
    have hv : (y' : V) ∈ Submodule.span ℂ (Set.range fun g : G => ρ g y) := by
      rw [span_range_orbit_eq_top hirr hy0]
      exact Submodule.mem_top
    obtain ⟨b, hbC, hbV, hbe⟩ := key y y' hv
    refine ⟨b, hbC, hbV, ?_⟩
    change b (A y) = A y'
    rw [hbe, averageFixed_of_mem]
  have hfd : FiniteDimensional ℂ (LinearMap.range A) :=
    Langlands.Analysis.finiteDimensional_of_tracial' (TwistedCoset.translates hψ)
      (TwistedCoset.xi (ψ := centerChar c.character hKχ))
      (fun x hx => TwistedCoset.norm_apply_xi_eq_norm_star_apply_xi hψ hZJ hJ μ hfin x hx)
      (fun x hx h0 => TwistedCoset.eq_zero_of_apply_xi hψ x hx h0) (LinearMap.range A) htrans
  exact LinearEquiv.finiteDimensional
    (LinearEquiv.ofInjective A (coeffMap_injective μ c K hKχ ℓ hall hirr hℓ)).symm

end Main

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- An irreducible smooth representation with a unitary central character and one nonzero
square-integrable matrix coefficient is admissible. -/
theorem isAdmissible_of_memLp (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible)
    (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V) (x : V)
    (hnonzero : matrixCoefficient ρ ℓ x ≠ 0) (hL2 : MemLp (c.coefficientNorm ℓ x) 2 μ) :
    IsAdmissible ρ := by
  have hx : x ≠ 0 := by
    rintro rfl
    apply hnonzero
    simp
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    apply hnonzero
    simp
  have hall : ∀ y : V, MemLp (c.coefficientNorm ℓ y) 2 μ :=
    memLp_coefficientNorm_of_irreducible hρ c μ hirr ℓ hx hL2
  refine ⟨hρ, fun K₀ => ?_⟩
  obtain ⟨K, hKc, hKK₀, hKχ⟩ := exists_compact_le_ker c.character c.isOpen_ker K₀
  have hfd : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) :=
    finiteDimensional_fixedVectors μ hρ hirr c K hKc hKχ ℓ hℓ hall
  have hle : fixedVectors ρ K₀.toSubgroup ≤ fixedVectors ρ K.toSubgroup :=
    fun v hv k => hv ⟨k, hKK₀ k.2⟩
  exact Submodule.finiteDimensional_of_le hle

end Admissible

end SingleCoefficient

open SingleCoefficient in
/-- Renard IV.3.2, Remark: for an irreducible smooth representation with a unitary central
character, one nonzero square-integrable smooth matrix coefficient makes every smooth matrix
coefficient square-integrable. Admissibility is not assumed; it is proved first. -/
theorem singleCoefficientSquareIntegrability :
    SingleCoefficientSquareIntegrabilityStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ π hirr c hex m y
  obtain ⟨ℓ, x, hnonzero, hL2⟩ := hex
  have hadm : π.IsAdmissible :=
    isAdmissible_of_memLp μ π.isSmooth hirr c ℓ.val x hnonzero hL2
  obtain ⟨_, c', hc'⟩ :=
    squareIntegrableCoefficientCriterion G μ π hirr hadm c ⟨ℓ, x, hnonzero, hL2⟩
  rw [c.coefficientNorm_eq c']
  exact hc' m y

end Langlands.Renard.CompactRepresentation
