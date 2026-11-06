import Langlands.Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation
import Langlands.HarmonicAnalysis.TorusFourierInversion
import Langlands.Topology.CompactNormCharacter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates

/-! # The lattice map of Laurent torus coordinates

Worker 200's `HasLaurentUnitaryCoordinates ν e` says that for every `m` the evaluation
`z ↦ χ_z(m)` of the unitary unramified character `χ_z = e⁻¹(z)` is a Laurent monomial
`torusCharacter n z = ∏ⱼ zⱼ^{nⱼ}`. The exponent `n` is unique (`torusCharacter_injective`), so it
defines a map `laurentExponent : H → J → ℤ`, which is a homomorphism (`laurentExponent_mul`),
vanishes on the common kernel of the norm characters `ν`, hence on every compact subgroup when
the `ν i` are continuous, and is locally constant and measurable when that kernel is open.

These are the hypotheses `hn`, `hK₀`, `hnm` and `hne` on the lattice map `n` in
`fourierOrbitSection_mem_smooth` (Waldspurger, Proposition VII.1.3) and in the twisted
coefficient families of `TwistedCoefficientSmoothness`. The growth bound
`‖n(m)‖ ≤ C (1 + σ(m))` is not addressed here. For the canonical rational coordinates the lattice
map is `rationalValuationCoordinates`, the coordinate vector of the valuation image
(`laurentExponent_rationalCanonical`).
-/

noncomputable section

open Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uH uI uJ

section Torus

variable {J : Type uJ} [Fintype J]

/-- A torus character identically equal to `1` has exponent `0`. -/
theorem eq_zero_of_forall_torusCharacter_eq_one {k : J → ℤ}
    (hk : ∀ z, torusCharacter k z = 1) : k = 0 := by
  classical
  funext j
  by_contra hj
  have hkj : ((k j : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hj
  have h := hk (finiteTorusExp (Pi.single j (Real.pi / k j)))
  rw [torusCharacter_finiteTorusExp_single] at h
  have harg : ((k j : ℝ) * (Real.pi / k j) : ℝ) = Real.pi := by field_simp
  rw [harg, Complex.exp_pi_mul_I] at h
  norm_num at h

/-- The exponent of a torus character is determined by the character. -/
theorem torusCharacter_injective : Function.Injective (torusCharacter (J := J)) := by
  intro n n' h
  have hk : ∀ z, torusCharacter (n - n') z = 1 := fun z => by
    have hz : torusCharacter n' z ≠ 0 := fun h0 => by
      have h1 := norm_torusCharacter n' z
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hadd := torusCharacter_add (n - n') n' z
    rw [sub_add_cancel, congrFun h z] at hadd
    exact mul_right_cancel₀ hz (by rw [one_mul]; exact hadd.symm)
  exact sub_eq_zero.mp (eq_zero_of_forall_torusCharacter_eq_one hk)

end Torus

section Laurent

variable {H : Type uH} [Group H] [TopologicalSpace H] {I : Type uI}
  (ν : I → (H →* ℝ≥0ˣ)) {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (he : HasLaurentUnitaryCoordinates ν e)

/-- **The lattice map** of Laurent torus coordinates: the unique `n(m) : J → ℤ` with
`χ_z(m) = ∏ⱼ zⱼ^{n(m)ⱼ}` for every unitary unramified character `χ_z = e⁻¹(z)`. -/
def laurentExponent (m : H) : J → ℤ :=
  Classical.choose (he m)

theorem torusCharacter_laurentExponent (m : H) (z : J → Circle) :
    torusCharacter (laurentExponent ν e he m) z = ((e.symm z).val m : ℂ) :=
  (Classical.choose_spec (he m) z).symm

/-- Uniqueness of the Laurent exponent. -/
theorem laurentExponent_eq_of_forall {m : H} {n : J → ℤ}
    (hn : ∀ z, ((e.symm z).val m : ℂ) = torusCharacter n z) :
    laurentExponent ν e he m = n :=
  torusCharacter_injective (funext fun z =>
    (torusCharacter_laurentExponent ν e he m z).trans (hn z))

/-- The lattice map is a homomorphism. -/
theorem laurentExponent_mul (g h : H) :
    laurentExponent ν e he (g * h) = laurentExponent ν e he g + laurentExponent ν e he h :=
  laurentExponent_eq_of_forall ν e he fun z => by
    rw [torusCharacter_add, torusCharacter_laurentExponent, torusCharacter_laurentExponent,
      map_mul, Units.val_mul]

/-- The lattice map vanishes on the common kernel of the norm characters. -/
theorem laurentExponent_eq_zero_of_mem {m : H} (hm : m ∈ commonNormKernel ν) :
    laurentExponent ν e he m = 0 :=
  laurentExponent_eq_of_forall ν e he fun z => by
    have h1 : (e.symm z).val m = 1 := (e.symm z).property.1 hm
    rw [torusCharacter_zero, h1, Units.val_one]

/-- For continuous norm characters the lattice map vanishes on every compact subgroup. -/
theorem laurentExponent_eq_zero_of_isCompact (hν : ∀ i, Continuous (ν i)) {K₀ : Subgroup H}
    (hK₀ : IsCompact (K₀ : Set H)) {k : H} (hk : k ∈ K₀) : laurentExponent ν e he k = 0 :=
  laurentExponent_eq_zero_of_mem ν e he ((mem_commonNormKernel ν k).mpr fun i =>
    RankinSelberg.LastRowReduction.eq_one_of_isCompact (ν i) (hν i) K₀ hK₀ hk)

/-- The lattice map is constant on the cosets of the common norm kernel. -/
theorem laurentExponent_mul_of_mem (m : H) {k : H} (hk : k ∈ commonNormKernel ν) :
    laurentExponent ν e he (m * k) = laurentExponent ν e he m := by
  rw [laurentExponent_mul, laurentExponent_eq_zero_of_mem ν e he hk, add_zero]

/-- If the common norm kernel is open, the lattice map is locally constant. -/
theorem isLocallyConstant_laurentExponent [ContinuousMul H]
    (hopen : IsOpen (commonNormKernel ν : Set H)) :
    IsLocallyConstant (laurentExponent ν e he) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun m => ?_
  have hO : IsOpen ((fun k => m * k) '' (commonNormKernel ν : Set H)) :=
    isOpenMap_mul_left m _ hopen
  have hm : m ∈ (fun k => m * k) '' (commonNormKernel ν : Set H) :=
    ⟨1, (commonNormKernel ν).one_mem, mul_one m⟩
  filter_upwards [hO.mem_nhds hm] with y hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact laurentExponent_mul_of_mem ν e he m hk

/-- If the common norm kernel is open, the lattice map is measurable. -/
theorem measurable_laurentExponent [ContinuousMul H] [MeasurableSpace H]
    [OpensMeasurableSpace H] (hopen : IsOpen (commonNormKernel ν : Set H)) :
    Measurable (laurentExponent ν e he) :=
  measurable_to_countable' fun n =>
    ((isLocallyConstant_laurentExponent ν e he hopen).isOpen_fiber n).measurableSet

end Laurent

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type uH} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance laurentExponentPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

omit [IsAffine G.X.left] in
/-- For Worker 200's canonical rational coordinates the lattice map is the coordinate vector
`rationalValuationCoordinates` of the valuation image in the basis
`rationalReductiveValuationBasis`. -/
theorem laurentExponent_rationalCanonical (hG : GroupScheme.IsConnectedReductive G)
    (g : GroupScheme.rationalPoints G) :
    laurentExponent (fun ψ => (rationalNormCharacters G ψ).toMul)
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).toMulEquiv
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent G hG) g =
      rationalValuationCoordinates G hG g := by
  have : IsAffine G.X.left := by
    have := hG.isAffineHom
    exact isAffine_of_isAffineHom G.X.hom
  exact laurentExponent_eq_of_forall _ _ _ fun z => rationalUnitaryUnramifiedCharacter_apply G hG z g

end Rational

end Langlands.HarishChandraSchwartz
