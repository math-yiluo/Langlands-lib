import Langlands.Shimura.Unitary.KottwitzFrobeniusPlaces
import Langlands.Weil.Local.AssemblyProof
import Langlands.LocalField.Normalization.Proof
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction

/-!
# Frobenius orbits on embeddings are the places above an unramified `p`

For a number field `K` unramified at `p` and `θ : ℂ →+* Q̄_p`, the orbits of the geometric
Frobenius permutation `frobeniusPerm K p θ` on the complex embeddings of `K` are exactly
the fibres of the place map `harrisPlace p θ`, and the orbit of `i` has `f_w` elements,
`f_w` the inertia degree of its place: `frobeniusOrbitsArePlaces_of_isUnramifiedAt`.
The proof reduces modulo the place (inverse Frobenius is the `p`-power map on residues),
shows `f_w ∣` every period, and concludes by counting with `∑ e_w f_w = [K : ℚ]`.
See the paired Markdown.
-/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing

namespace Langlands.Shimura.KottwitzDual

universe u v

section Residue

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance frobOrbitTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance frobOrbitValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance frobOrbitLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance frobOrbitCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance frobOrbitNormedField : NontriviallyNormedField F.Carrier :=
  LocalGalois.localNormedField F.Carrier
local instance frobOrbitUltrametric : IsUltrametricDist F.Carrier :=
  LocalGalois.localNormedField_ultrametric F.Carrier
local instance frobOrbitComplete : CompleteSpace F.Carrier :=
  LocalGalois.localNormedField_complete F.Carrier

/-- The inverse of the chosen geometric Frobenius acts on the residue field of the
integral closure by the power `y ↦ y ^ q`, `q` the residue cardinality. -/
theorem residueHom_inv_localGeometricFrobenius
    (y : ResidueField (LocalGalois.closureIntegers F.Carrier)) :
    LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier)
        (localProjection F (localGeometricFrobenius F))⁻¹ y =
      y ^ F.canonicalTopologicalData.residueCardinality := by
  set σ := localProjection F (localGeometricFrobenius F)
  let e := LocalGalois.localResidueClosureEquiv F.Carrier
  apply e.injective
  have h1 : e (LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier) σ⁻¹ y) =
      AlgEquiv.toAlgHom (localResidueMap F σ⁻¹) (e y) := by
    change _ = e (LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier) σ⁻¹
      (e.symm (e y)))
    rw [e.symm_apply_apply]
  rw [h1, map_inv, localGeometricFrobenius_residue, map_pow]
  rw [show (Galois.FiniteField.geometricFrobenius (localResidueField F))⁻¹ =
    Galois.FiniteField.arithmeticFrobenius (localResidueField F) from inv_inv _]
  simp [Galois.FiniteField.arithmeticFrobenius, Galois.FiniteField.arithmetic,
    ← Nat.card_eq_fintype_card, ← localResidueCardinality_eq F]


/-- Iterating: `(Frob⁻¹)^r` acts on residues by `y ↦ y ^ (q ^ r)`. -/
theorem residueHom_inv_pow_localGeometricFrobenius (r : ℕ)
    (y : ResidueField (LocalGalois.closureIntegers F.Carrier)) :
    LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier)
        (((localProjection F (localGeometricFrobenius F))⁻¹ :
          Gal(AlgebraicClosure F.Carrier/F.Carrier)) ^ r) y =
      y ^ (F.canonicalTopologicalData.residueCardinality ^ r) := by
  induction r generalizing y with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, map_mul, AlgEquiv.mul_apply, residueHom_inv_localGeometricFrobenius, ih,
      ← pow_mul, pow_succ, mul_comm]

/-- The same statement on integral elements, before reduction. -/
theorem residue_integerAut_inv_pow (r : ℕ) (y : LocalGalois.closureIntegers F.Carrier) :
    residue _ (LocalGalois.integerAut F.Carrier (AlgebraicClosure F.Carrier)
        (((localProjection F (localGeometricFrobenius F))⁻¹ :
          Gal(AlgebraicClosure F.Carrier/F.Carrier)) ^ r) y) =
      residue _ y ^ (F.canonicalTopologicalData.residueCardinality ^ r) := by
  rw [← LocalGalois.residueHom_apply, residueHom_inv_pow_localGeometricFrobenius]

/-- For `ℚ_p` with its canonical data, the valuation ring is the closed unit ball. -/
theorem rational_mem_integer_iff (x : ℚ_[p]) :
    (show (PadicField.rational p).Carrier from x) ∈
        (ValuativeRel.valuation (PadicField.rational p).Carrier).integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff,
    PadicField.canonicalTopologicalData_vle]
  have h1 := PadicField.canonicalNorm_algebraMap (PadicField.rational p) x
  have h2 := PadicField.canonicalNorm_algebraMap (PadicField.rational p) 1
  rw [map_one, norm_one] at h2
  exact h1 ▸ h2 ▸ Iff.rfl


/-- Elements of `Q̄_p` of norm at most one lie in the integral closure used by the
canonical local Galois theory of `ℚ_p`. -/
theorem mem_closureIntegers_of_norm_le_one (y : PadicAlgCl p) (hy : ‖y‖ ≤ 1) :
    (show AlgebraicClosure (PadicField.rational p).Carrier from y) ∈
      LocalGalois.closureIntegers (PadicField.rational p).Carrier := by
  have hI : IsIntegral (LocalGalois.baseIntegers ℚ_[p]) y :=
    (LocalGalois.integral_iff_mem_spectralIntegers ℚ_[p] (PadicAlgCl p) y).mpr hy
  let φ : LocalGalois.baseIntegers ℚ_[p] →+*
      (ValuativeRel.valuation (PadicField.rational p).Carrier).integer :=
    { toFun := fun x => ⟨(x : ℚ_[p]), (rational_mem_integer_iff (x : ℚ_[p])).mpr <| by
        have hx := x.2
        rw [Valuation.mem_valuationSubring_iff] at hx
        exact_mod_cast hx⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ψ : PadicAlgCl p →+* AlgebraicClosure (PadicField.rational p).Carrier :=
    RingHom.id (PadicAlgCl p)
  have hI' := IsIntegral.map_of_comp_eq (U := AlgebraicClosure (PadicField.rational p).Carrier)
    φ ψ (by ext; rfl) hI
  exact (LocalGalois.closureIntegers_integral _ _).mp hI'


/-- The residue field of `ℚ_p` with its canonical data has `p` elements. -/
theorem rational_residueCardinality :
    (PadicField.rational p).canonicalTopologicalData.residueCardinality = p :=
  PadicField.TopologicalData.residueCardinality_eq_prime_of_degree_one _
    (Module.finrank_self (Padic p))

/-- The key congruence: for `y ∈ Q̄_p` with `‖y‖ ≤ 1`,
`‖Frob⁻ʳ y - y ^ (p ^ r)‖ < 1`, `Frob` the chosen geometric Frobenius. -/
theorem norm_geometricFrobenius_inv_pow_sub_lt (r : ℕ) (y : PadicAlgCl p) (hy : ‖y‖ ≤ 1) :
    ‖((geometricFrobenius p)⁻¹ ^ r) y - y ^ (p ^ r)‖ < 1 := by
  let K := (PadicField.rational p).Carrier
  let Y : LocalGalois.closureIntegers K := ⟨y, mem_closureIntegers_of_norm_le_one y hy⟩
  let τ : Gal(AlgebraicClosure K/K) :=
    ((localProjection (PadicField.rational p)
      (localGeometricFrobenius (PadicField.rational p)))⁻¹ : Gal(AlgebraicClosure K/K)) ^ r
  let z : LocalGalois.closureIntegers K :=
    LocalGalois.integerAut K (AlgebraicClosure K) τ Y - Y ^ (p ^ r)
  have hz : residue _ z = 0 := by
    have h := residue_integerAut_inv_pow (PadicField.rational p) r Y
    rw [rational_residueCardinality] at h
    simp only [z, map_sub, map_pow]
    rw [h, sub_self]
  have hzn : ¬ IsUnit z := by
    rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff]
    exact hz
  set w : PadicAlgCl p := ((geometricFrobenius p)⁻¹ ^ r) y - y ^ (p ^ r) with hw
  have hcoe : ((z : AlgebraicClosure K) : PadicAlgCl p) = w := rfl
  by_contra hlt
  push Not at hlt
  apply hzn
  have hz0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlt
    norm_num at hlt
  have hinv := mem_closureIntegers_of_norm_le_one w⁻¹
    (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hlt)
  refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : LocalGalois.closureIntegers K) (Subtype.ext ?_)
  change w * w⁻¹ = 1
  exact mul_inv_cancel₀ hz0

end Residue


section Places

open KottwitzUnramified Langlands.Global.AdelicFunctoriality

variable {K : Type v} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

theorem theta_frobeniusPerm_pow_apply (r : ℕ) (i : K →+* ℂ) (x : K) :
    θ ((frobeniusPerm K p θ ^ r) i x) = (geometricFrobenius p ^ r) (θ (i x)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, theta_frobeniusPerm_apply, ih, pow_succ',
      AlgEquiv.mul_apply]

omit [NumberField K] in
/-- Algebraic integers have norm at most one under `θ ∘ i`. -/
theorem norm_theta_algebraMap_le_one (i : K →+* ℂ) (x : 𝓞 K) :
    ‖θ (i (algebraMap (𝓞 K) K x))‖ ≤ 1 := by
  have h := valuation_embedding_le_one (harrisValuation p θ) i x
  rw [harrisValuation_apply, PadicAlgCl.valuation_def] at h
  exact_mod_cast h

/-- If `Frob^r` fixes the embedding `i`, then `x ^ (p ^ r) ≡ x` modulo the prime of `i`
for every algebraic integer `x`. -/
theorem pow_sub_mem_harrisPrime_of_frobeniusPerm_pow (r : ℕ) (i : K →+* ℂ)
    (h : (frobeniusPerm K p θ ^ r) i = i) (x : 𝓞 K) :
    x ^ (p ^ r) - x ∈ (harrisPrime p θ i).asIdeal := by
  set y := θ (i (algebraMap (𝓞 K) K x)) with hy_def
  have hy : ‖y‖ ≤ 1 := norm_theta_algebraMap_le_one p θ i x
  have hfix : (geometricFrobenius p ^ r) y = y := by
    rw [hy_def, ← theta_frobeniusPerm_pow_apply, h]
  have hfix' : ((geometricFrobenius p)⁻¹ ^ r) y = y := by
    rw [inv_pow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hfix]
  have hlt := norm_geometricFrobenius_inv_pow_sub_lt r y hy
  rw [hfix'] at hlt
  rw [harrisPrime_asIdeal, mem_embeddingIdeal, harrisValuation_apply, PadicAlgCl.valuation_def]
  simp only [map_sub, map_pow]
  rw [← hy_def, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one, norm_sub_rev]
  exact hlt

/-- The residue field of `ℚ` at `p` has `p` elements. -/
theorem card_quot_rationalPrimePlace :
    Nat.card (𝓞 ℚ ⧸ (rationalPrimePlace p).asIdeal) = p := by
  let e : ℤ ⧸ Ideal.span {(p : ℤ)} ≃+* 𝓞 ℚ ⧸ (rationalPrimePlace p).asIdeal :=
    Ideal.quotientEquiv _ _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm rfl
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv,
    Nat.card_zmod]

/-- The residue field of the place of `i` has `p ^ f_w` elements. -/
theorem card_quot_harrisPrime (i : K →+* ℂ) :
    Nat.card (𝓞 K ⧸ (harrisPrime p θ i).asIdeal) =
      p ^ inertiaDegree (harrisPlace p θ i) := by
  have := (harrisPlace p θ i).2
  have h := Ideal.cardQuot_pow_inertiaDeg (R := 𝓞 ℚ) (rationalPrimePlace p).asIdeal
    (harrisPlace p θ i).1.asIdeal
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, card_quot_rationalPrimePlace] at h
  exact h.symm

/-- If `Frob^r` fixes the embedding `i`, then the inertia degree `f_w` of its place divides
`r`. -/
theorem inertiaDegree_dvd_of_frobeniusPerm_pow_apply_eq (r : ℕ) (i : K →+* ℂ)
    (h : (frobeniusPerm K p θ ^ r) i = i) :
    inertiaDegree (harrisPlace p θ i) ∣ r := by
  have hcard := card_quot_harrisPrime p θ i
  set f := inertiaDegree (harrisPlace p θ i)
  set P := (harrisPrime p θ i).asIdeal
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hr1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hunits : ∀ u : (𝓞 K ⧸ P)ˣ, u ^ (p ^ r - 1) = 1 := by
    intro u
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ P)
    have hmem := pow_sub_mem_harrisPrime_of_frobeniusPerm_pow p θ r i h x
    have hq : (u : 𝓞 K ⧸ P) ^ (p ^ r) = u := by
      rw [← hx, ← map_pow, Ideal.Quotient.eq]
      exact hmem
    apply Units.ext
    have h2 : (u : 𝓞 K ⧸ P) ^ (p ^ r - 1) * u = 1 * u := by
      rw [← pow_succ, Nat.sub_add_cancel hr1, hq, one_mul]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ u.ne_zero h2
  have hdvd := (FiniteField.forall_pow_eq_one_iff (𝓞 K ⧸ P) (p ^ r - 1)).mp hunits
  rw [← Nat.card_eq_fintype_card, hcard] at hdvd
  have hg := Nat.gcd_eq_left hdvd
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have hpow : p ^ Nat.gcd f r = p ^ f := by
    have h1 : 1 ≤ p ^ Nat.gcd f r := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
    omega
  have hgf := Nat.pow_right_injective hp2 hpow
  exact hgf ▸ Nat.gcd_dvd_right f r


/-- Every embedding is periodic under the Frobenius permutation. -/
theorem minimalPeriod_frobeniusPerm_pos (i : K →+* ℂ) :
    0 < Function.minimalPeriod (frobeniusPerm K p θ) i := by
  refine Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos (frobeniusPerm K p θ)) ?_
  change (frobeniusPerm K p θ ^ orderOf (frobeniusPerm K p θ)) i = i
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]

/-- The inertia degree `f_w` of the place of `i` divides the Frobenius period of `i`. -/
theorem inertiaDegree_dvd_minimalPeriod (i : K →+* ℂ) :
    inertiaDegree (harrisPlace p θ i) ∣ Function.minimalPeriod (frobeniusPerm K p θ) i := by
  apply inertiaDegree_dvd_of_frobeniusPerm_pow_apply_eq
  rw [← Equiv.Perm.iterate_eq_pow]
  exact Function.iterate_minimalPeriod

variable (K) in
/-- The Frobenius orbit of a complex embedding `i` of `K`: the embeddings `Frob^r ∘ i` for
`0 ≤ r <` the minimal period of `i` under `frobeniusPerm K p θ`. -/
def frobeniusOrbit (i : K →+* ℂ) : Finset (K →+* ℂ) :=
  open scoped Classical in
  (Finset.range (Function.minimalPeriod (frobeniusPerm K p θ) i)).image
    fun r => (frobeniusPerm K p θ ^ r) i

theorem mem_frobeniusOrbit (i j : K →+* ℂ) :
    j ∈ frobeniusOrbit K p θ i ↔ ∃ r : ℕ, (frobeniusPerm K p θ ^ r) i = j := by
  classical
  constructor
  · intro hj
    rw [frobeniusOrbit, Finset.mem_image] at hj
    obtain ⟨r, -, hr⟩ := hj
    exact ⟨r, hr⟩
  · rintro ⟨r, rfl⟩
    rw [frobeniusOrbit, Finset.mem_image]
    refine ⟨r % Function.minimalPeriod (frobeniusPerm K p θ) i,
      Finset.mem_range.mpr (Nat.mod_lt _ (minimalPeriod_frobeniusPerm_pos p θ i)), ?_⟩
    rw [← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow]
    exact Function.iterate_mod_minimalPeriod_eq

/-- The Frobenius orbit of `i` has as many elements as the minimal period of `i`. -/
theorem card_frobeniusOrbit (i : K →+* ℂ) :
    (frobeniusOrbit K p θ i).card = Function.minimalPeriod (frobeniusPerm K p θ) i := by
  classical
  rw [frobeniusOrbit, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  rw [Finset.coe_range] at ha hb
  exact Function.iterate_injOn_Iio_minimalPeriod ha hb hab

/-- The Frobenius orbit of `i` lies in the fibre of the place map through `i`. -/
theorem frobeniusOrbit_subset_harrisPlaceFibre (i : K →+* ℂ) :
    frobeniusOrbit K p θ i ⊆ harrisPlaceFibre p θ (harrisPlace p θ i) := by
  intro j hj
  obtain ⟨r, rfl⟩ := (mem_frobeniusOrbit p θ i j).mp hj
  rw [mem_harrisPlaceFibre, harrisPlace_frobeniusPerm_pow]

/-- Every fibre of the place map has at least `f_w` elements. -/
theorem inertiaDegree_le_card_harrisPlaceFibre
    (w : FinitePlacesAbove K (rationalPrimePlace p)) :
    inertiaDegree w ≤ (harrisPlaceFibre p θ w).card := by
  obtain ⟨i, rfl⟩ := harrisPlace_surjective p θ w
  calc inertiaDegree (harrisPlace p θ i)
      ≤ Function.minimalPeriod (frobeniusPerm K p θ) i :=
        Nat.le_of_dvd (minimalPeriod_frobeniusPerm_pos p θ i)
          (inertiaDegree_dvd_minimalPeriod p θ i)
    _ = (frobeniusOrbit K p θ i).card := (card_frobeniusOrbit p θ i).symm
    _ ≤ _ := Finset.card_le_card (frobeniusOrbit_subset_harrisPlaceFibre p θ i)

/-- **Frobenius orbits are places.** If `K` is unramified at `p`, the Frobenius orbits on
the complex embeddings of `K` are the fibres of the place map, and the orbit of `i` has
exactly `f_w` elements. -/
theorem frobeniusOrbitsArePlaces_of_isUnramifiedAt (h : IsUnramifiedAt (rationalPrimePlace p) K) :
    FrobeniusOrbitsArePlaces K p θ := by
  classical
  have hsum : ∑ w : FinitePlacesAbove K (rationalPrimePlace p), inertiaDegree w =
      ∑ w : FinitePlacesAbove K (rationalPrimePlace p), (harrisPlaceFibre p θ w).card := by
    rw [sum_card_harrisPlaceFibre,
      ← finitePlacesAbove_sum_ramification_inertia (L := K) (rationalPrimePlace p)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [h w, one_mul]
  have heq : ∀ w, inertiaDegree w = (harrisPlaceFibre p θ w).card := fun w =>
    (Finset.sum_eq_sum_iff_of_le fun w _ => inertiaDegree_le_card_harrisPlaceFibre p θ w).mp
      hsum w (Finset.mem_univ _)
  intro i
  have hcard : (harrisPlaceFibre p θ (harrisPlace p θ i)).card ≤
      (frobeniusOrbit K p θ i).card := by
    rw [card_frobeniusOrbit, ← heq]
    exact Nat.le_of_dvd (minimalPeriod_frobeniusPerm_pos p θ i)
      (inertiaDegree_dvd_minimalPeriod p θ i)
  have horb : frobeniusOrbit K p θ i = harrisPlaceFibre p θ (harrisPlace p θ i) :=
    Finset.eq_of_subset_of_card_le (frobeniusOrbit_subset_harrisPlaceFibre p θ i) hcard
  refine ⟨?_, fun j => ?_⟩
  · rw [← card_frobeniusOrbit, horb, ← heq]
  · rw [← mem_harrisPlaceFibre, ← horb, mem_frobeniusOrbit]

end Places


section Conjugation

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

/-- If `K` is unramified at `p`, every Frobenius-invariant cocharacter in embedding
coordinates is `ℚ_p`-rational. -/
theorem frobeniusInvariantsRational_of_isUnramifiedAt {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (hΦ : IsCMSection E K Φ) (n : ℕ)
    (h : KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p) K) :
    FrobeniusInvariantsRational E K n p θ hΦ :=
  frobeniusInvariantsRational_of_frobeniusOrbitsArePlaces p θ hΦ n
    (frobeniusOrbitsArePlaces_of_isUnramifiedAt p θ h)

end Conjugation

end Langlands.Shimura.KottwitzDual
