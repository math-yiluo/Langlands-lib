import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusPrincipalRelationsStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusNormalFormProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictRelativeSeriesPropertiesProof
import Langlands.Geometry.Analytic.BilateralRecurrenceVanishingProof
import Langlands.Geometry.Analytic.ClosedIdealsBanach

/-! # Proof of the closed principal-relation comparison for the unit annulus -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

open GeneralizedTateAlgebra Filter
open scoped ZeroAtInfty Topology

namespace PrincipalRelations

/-- Zero-at-infinity functions on the discrete integers decay along the cofinite filter. -/
theorem tendsto_cofinite {E : Type*} [NormedAddCommGroup E] (φ : C₀(ℤ, E)) :
    Tendsto φ cofinite (𝓝 0) := by
  have h := φ.zero_at_infty'
  rwa [cocompact_eq_cofinite] at h

variable (K : Type u) [NormedField K] [IsUltrametricDist K] (A : PresentedAffinoidAlgebra K)

local notation "𝕊" => GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A

/-! ### One-variable series and their coefficients -/

/-- A one-variable series whose coefficients all vanish is zero. -/
theorem eq_zero_of_coeff (r : 𝕊)
    (h : ∀ k : ℕ, MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) k) (series _ A r) = 0) :
    r = 0 := by
  apply Subtype.ext
  ext d
  have hd : d = Finsupp.single 0 (d 0) := Finsupp.ext fun i => by fin_cases i; simp
  have h0 := h (d 0)
  rw [← hd] at h0
  exact h0

/-- The one-variable series with the supplied cofinitely decaying coefficients. -/
def seriesOf (g : (Fin 1 →₀ ℕ) → A) (hg : Tendsto g cofinite (𝓝 0)) : 𝕊 :=
  ⟨g, by
    show Tendsto (fun d => ‖MvPowerSeries.coeff d g‖ *
      (PositivePolyradius.unit (Fin 1)).weight d) cofinite (𝓝 0)
    simp only [PositivePolyradius.unit_weight, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp hg⟩

theorem coeff_seriesOf (g : (Fin 1 →₀ ℕ) → A) (hg : Tendsto g cofinite (𝓝 0))
    (d : Fin 1 →₀ ℕ) : MvPowerSeries.coeff d (series _ A (seriesOf K A g hg)) = g d := rfl

theorem injective_upperIndex : Function.Injective fun d : Fin 1 →₀ ℕ => (d 0 : ℤ) := by
  intro d d' h
  have h' : (d 0 : ℤ) = d' 0 := h
  exact Finsupp.ext fun i => by rw [Subsingleton.elim i 0]; exact_mod_cast h'

theorem injective_lowerIndex :
    Function.Injective fun d : Fin 1 →₀ ℕ => -(d 0 : ℤ) - 1 := by
  intro d d' h
  have h' : -(d 0 : ℤ) - 1 = -(d' 0 : ℤ) - 1 := h
  exact Finsupp.ext fun i => by rw [Subsingleton.elim i 0]; omega

/-- The nonnegative part of an integer-indexed coefficient function, as a series. -/
def upperSeries (c : C₀(ℤ, A)) : 𝕊 :=
  seriesOf K A (fun d => c (d 0 : ℤ))
    ((tendsto_cofinite c).comp (injective_upperIndex.tendsto_cofinite))

/-- The strictly negative part, shifted by one: `T^k` receives the coefficient at `-k-1`. -/
def lowerSeries (c : C₀(ℤ, A)) : 𝕊 :=
  seriesOf K A (fun d => c (-(d 0 : ℤ) - 1))
    ((tendsto_cofinite c).comp (injective_lowerIndex.tendsto_cofinite))

theorem coeff_upperSeries (c : C₀(ℤ, A)) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) k) (series _ A (upperSeries K A c)) =
      c k := by
  rw [upperSeries, coeff_seriesOf, Finsupp.single_eq_same]

theorem coeff_lowerSeries (c : C₀(ℤ, A)) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) k) (series _ A (lowerSeries K A c)) =
      c (-(k : ℤ) - 1) := by
  rw [lowerSeries, coeff_seriesOf, Finsupp.single_eq_same]

/-! ### The two principal relations under the one-variable maps -/

section Annulus

variable [CompleteSpace K]

theorem positive_add (a b : 𝕊) : positive K A (a + b) = positive K A a + positive K A b :=
  map_add (positive K A).toAlgHom a b

theorem negative_add (a b : 𝕊) : negative K A (a + b) = negative K A a + negative K A b :=
  map_add (negative K A).toAlgHom a b

theorem positive_sub (a b : 𝕊) : positive K A (a - b) = positive K A a - positive K A b :=
  map_sub (positive K A).toAlgHom a b

theorem negative_sub (a b : 𝕊) : negative K A (a - b) = negative K A a - negative K A b :=
  map_sub (negative K A).toAlgHom a b

theorem positive_mul (a b : 𝕊) : positive K A (a * b) = positive K A a * positive K A b :=
  map_mul (positive K A).toAlgHom a b

theorem negative_mul (a b : 𝕊) : negative K A (a * b) = negative K A a * negative K A b :=
  map_mul (negative K A).toAlgHom a b

theorem negative_one : negative K A 1 = 1 := map_one (negative K A).toAlgHom

theorem positive_smul (c : K) (a : 𝕊) : positive K A (c • a) = c • positive K A a :=
  map_smul (positive K A).toAlgHom c a

theorem negative_smul (c : K) (a : 𝕊) : negative K A (c • a) = c • negative K A a :=
  map_smul (negative K A).toAlgHom c a

variable (f : A)

/-- The positive map sends a multiple of `T - C f` to a multiple of `x - b f`. -/
theorem positive_mul_upper (r : 𝕊) :
    positive K A (r * (X (PositivePolyradius.unit (Fin 1)) A 0 -
      constantAlgHom (PositivePolyradius.unit (Fin 1)) K A f)) =
      positive K A r * (annulusX K A - baseMap K A f) := by
  rw [positive_mul, positive_sub, positive_X, positive_constant]

/-- The negative map sends a multiple of `C f * T - 1` to a multiple of `x - b f`,
using `x * y = 1`. -/
theorem negative_mul_lower (s : 𝕊) :
    negative K A (s * (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A f *
      X (PositivePolyradius.unit (Fin 1)) A 0 - 1)) =
      -(annulusY K A * negative K A s) * (annulusX K A - baseMap K A f) := by
  rw [negative_mul, negative_sub, negative_mul, negative_constant, negative_X, negative_one]
  linear_combination (negative K A s) * annulusX_mul_annulusY K A

/-! ### Consequences of the Laurent normal form -/

/-- The nonnegative and strictly negative parts determine the series. -/
theorem eq_zero_of_positive_add_eq_zero (hNF : NormalFormStatement.{u}) (r s : 𝕊)
    (h : positive K A r + annulusY K A * negative K A s = 0) : r = 0 ∧ s = 0 := by
  obtain ⟨e, -, -, hY, -, hpos, hneg⟩ := hNF K A
  have hc : ∀ n : ℤ, e (positive K A r) n + e (negative K A s) (n + 1) = 0 := by
    intro n
    have h1 := congrArg (fun z => e z n) h
    simp only [map_add, ZeroAtInftyContinuousMap.add_apply, hY, map_zero,
      ZeroAtInftyContinuousMap.zero_apply] at h1
    exact h1
  constructor
  · apply eq_zero_of_coeff
    intro k
    have h1 := hc k
    rw [hpos, hneg, ite_eq_left (by omega), ite_eq_right (by omega), add_zero,
      show (k : ℤ).toNat = k by omega] at h1
    exact h1
  · apply eq_zero_of_coeff
    intro k
    have h1 := hc (-(k : ℤ) - 1)
    rw [hpos, hneg, ite_eq_right (by omega), ite_eq_left (by omega), zero_add,
      show (-(-(k : ℤ) - 1 + 1)).toNat = k by omega] at h1
    exact h1

/-- Every annulus element splits into a nonnegative and a strictly negative part. -/
theorem exists_positive_add (hNF : NormalFormStatement.{u}) (z : Algebra K A) :
    ∃ r s : 𝕊, z = positive K A r + annulusY K A * negative K A s := by
  obtain ⟨e, -, -, hY, -, hpos, hneg⟩ := hNF K A
  refine ⟨upperSeries K A (e z), lowerSeries K A (e z),
    e.injective (ZeroAtInftyContinuousMap.ext fun n => ?_)⟩
  rw [map_add, ZeroAtInftyContinuousMap.add_apply, hY, hpos, hneg]
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn, ite_eq_right (by omega), add_zero, coeff_upperSeries,
      Int.toNat_of_nonneg hn]
  · rw [ite_eq_right hn, ite_eq_left (by omega), zero_add, coeff_lowerSeries]
    congr 1
    omega

/-- Multiplication by `x - b f` is injective on the annulus over a Noetherian base. -/
theorem eq_zero_of_mul_eq_zero (hK : ∃ c : K, 1 < ‖c‖) [IsNoetherianRing A]
    (hNF : NormalFormStatement.{u}) (z : Algebra K A)
    (h : z * (annulusX K A - baseMap K A f) = 0) : z = 0 := by
  obtain ⟨e, -, hX, -, hb, -, -⟩ := hNF K A
  have hrec : ∀ n : ℤ, e z (n - 1) = f * e z n := by
    intro n
    rw [mul_comm, sub_mul] at h
    have h1 := congrArg (fun w => e w n) h
    simp only [map_sub, ZeroAtInftyContinuousMap.sub_apply, hX, hb,
      map_zero, ZeroAtInftyContinuousMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := hK }
  have hzero := bilateral_recurrence_eq_zero K f (fun n => e z n) (tendsto_cofinite (e z)) hrec
  apply e.injective
  ext n
  rw [map_zero, ZeroAtInftyContinuousMap.zero_apply]
  exact hzero n

/-- The comparison of principal relations over a Noetherian base. -/
theorem exists_beta (hK : ∃ c : K, 1 < ‖c‖) [IsNoetherianRing A]
    (hNF : NormalFormStatement.{u}) :
    let S := GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A
    let U := Algebra K A
    let C := GeneralizedTateAlgebra.constantAlgHom (PositivePolyradius.unit (Fin 1)) K A
    let T := GeneralizedTateAlgebra.X (PositivePolyradius.unit (Fin 1)) A 0
    let Jpos : Ideal S := Ideal.span ({T - C f} : Set S)
    let Jneg : Ideal S := Ideal.span ({C f * T - 1} : Set S)
    let J : Ideal U := Ideal.span ({annulusX K A - baseMap K A f} : Set U)
    ∃ β : (Jpos × Jneg) ≃ₗ[K] J,
      ∀ (p : Jpos) (q : Jneg),
        (β (p, q) : U) = positive K A (p : S) - negative K A (q : S) := by
  intro S U C T Jpos Jneg J
  have hup : ∀ r : S, positive K A (r * (T - C f)) =
      positive K A r * (annulusX K A - baseMap K A f) :=
    positive_mul_upper K A f
  have hlow : ∀ s : S, negative K A (s * (C f * T - 1)) =
      -(annulusY K A * negative K A s) * (annulusX K A - baseMap K A f) :=
    negative_mul_lower K A f
  have hJ : ∀ w : U, w * (annulusX K A - baseMap K A f) ∈ J := fun w =>
    Ideal.mul_mem_left J w (Ideal.subset_span (Set.mem_singleton _))
  have hmem : ∀ (p : Jpos) (q : Jneg),
      positive K A (p : S) - negative K A (q : S) ∈ J := by
    intro p q
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp p.2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp q.2
    rw [← hr, ← hs, hup, hlow, ← sub_mul]
    exact hJ _
  let L : (Jpos × Jneg) →ₗ[K] J :=
    { toFun := fun pq => ⟨positive K A (pq.1 : S) - negative K A (pq.2 : S), hmem pq.1 pq.2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
        abel
      map_smul' := fun c a => by
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower, map_smul,
          RingHom.id_apply, smul_sub] }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr ?_
    rintro ⟨p, q⟩ hpq
    have h0 : positive K A (p : S) - negative K A (q : S) = 0 := congrArg Subtype.val hpq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp p.2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp q.2
    rw [← hr, ← hs, hup, hlow, ← sub_mul] at h0
    have h1 := eq_zero_of_mul_eq_zero K A f hK hNF _ h0
    rw [sub_neg_eq_add] at h1
    obtain ⟨hr0, hs0⟩ := eq_zero_of_positive_add_eq_zero K A hNF r s h1
    have hp : p = 0 := Subtype.ext (by rw [← hr, hr0, zero_mul]; rfl)
    have hq : q = 0 := Subtype.ext (by rw [← hs, hs0, zero_mul]; rfl)
    rw [hp, hq]
    rfl
  have hsurj : Function.Surjective L := by
    rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨r, s, rfl⟩ := exists_positive_add K A hNF w
    refine ⟨(⟨r * (T - C f), Ideal.mul_mem_left _ r (Ideal.subset_span (Set.mem_singleton _))⟩,
      ⟨s * (C f * T - 1), Ideal.mul_mem_left _ s (Ideal.subset_span (Set.mem_singleton _))⟩),
      Subtype.ext ?_⟩
    show positive K A (r * (T - C f)) - negative K A (s * (C f * T - 1)) = _
    rw [hup, hlow]
    ring
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun p q => rfl⟩

end Annulus

/-! ### Closedness over strict bases -/

variable [CompleteSpace K]

/-- The strict base is Noetherian, through its comparison with the strict presentation. -/
theorem isNoetherianRing_ofStrict (P : PresentedStrictAffinoidAlgebra K) :
    IsNoetherianRing (ofStrict K P) :=
  isNoetherianRing_of_ringEquiv P (strictAlgEquiv K P).symm.toRingEquiv

/-- Every ideal of the annulus over a strict base is closed. -/
theorem isClosed_annulus_ideal (hK : ∃ c : K, 1 < ‖c‖) (P : PresentedStrictAffinoidAlgebra K)
    (I : Ideal (Algebra K (ofStrict K P))) : IsClosed (I : Set (Algebra K (ofStrict K P))) := by
  have := strict_relative_series_noetherian K P 2
  have : IsNoetherianRing (Algebra K (ofStrict K P)) :=
    isNoetherianRing_of_surjective _ _ (quotientMap K (ofStrict K P)).toAlgHom.toRingHom
      (quotientMap_surjective K (ofStrict K P))
  let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := hK }
  exact isClosed_ideal_of_noetherian_banach (K := K) I

end PrincipalRelations

open PrincipalRelations in
/-- The statement follows from the Laurent normal form. -/
theorem principal_relations_of_normalForm (hNF : NormalFormStatement.{u}) :
    PrincipalRelationsStatement.{u} := by
  intro K _ _ _ hK P f
  have := isNoetherianRing_ofStrict K P
  exact ⟨strict_relative_series_closed K hK P 1 _, strict_relative_series_closed K hK P 1 _,
    isClosed_annulus_ideal K hK P _, exists_beta K (ofStrict K P) f hK hNF⟩

/-- Closed principal-relation comparison for the relative unit annulus over a strict base. -/
theorem principal_relations : PrincipalRelationsStatement.{u} :=
  principal_relations_of_normalForm normal_form

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
