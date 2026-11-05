import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralFourierInversion
import Langlands.Representation.Plancherel.RationalCharacterHaar

/-! # Fourier inversion over the split center in the proof of Proposition VII.2.1

Waldspurger, proof of Proposition VII.2.1, case `M = G` (printed pp. 317–318), applies Fourier
inversion over `A_G` to `a ↦ χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω`. This module proves that
step for the actual rational points, with `A_G` the image of a central `s : T → G`, the orbit
`O` replaced by `Im X(G)` with its I.1 measure, and unitary characters `c = χ_{ω₀}`, `η = χ_{ω'}`
of `A_G`: for `f` on `Im X(G)`, `∫_{A_G} η(a⁻¹) ∫_{Im X(G)} f(χ) χ(a) c(a) dχ da` vanishes if `c`
and `η` differ on `A_G ∩ G¹`, and otherwise equals `mes(A_G ∩ G¹) ∑_{χ ; χ c = η on A_G} f(χ)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped CategoryTheory.MonObj ComplexConjugate

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J]

/-- A character `ψ` of `ℤ^J` is the torus character evaluation at the point `(ψ(e_j))_j`. -/
theorem exists_torusCharacter_eq (ψ : Multiplicative (J → ℤ) →* Circle) :
    ∃ z : J → Circle, ∀ k, torusCharacter k z = ψ (Multiplicative.ofAdd k) := by
  classical
  refine ⟨fun j => ψ (Multiplicative.ofAdd (Pi.single j 1)), fun k => ?_⟩
  have hdecomp : k = ∑ j, k j • (Pi.single j 1 : J → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hdecomp]
  rw [ofAdd_sum, map_prod, torusCharacter]
  refine (Finset.prod_congr rfl fun j _ => ?_).trans (map_prod Circle.coeHom _ _).symm
  rw [ofAdd_zsmul, map_zpow]
  rfl

/-- **Characters factoring through a homomorphism to `ℤ^J` are torus characters**: if
`N : H →* ℤ^J` and `ρ : H →* Circle` with `ker N ≤ ker ρ`, then `ρ(a) = χ_{N(a)}(z)` for some
point `z` of the torus. The character of `N(H)` induced by `ρ` extends to `ℤ^J` because
`Circle` is divisible. -/
theorem exists_torusCharacter_eq_of_ker_le {H : Type*} [Group H]
    (N : H →* Multiplicative (J → ℤ)) (ρ : H →* Circle) (hker : N.ker ≤ ρ.ker) :
    ∃ z : J → Circle, ∀ a, torusCharacter (Multiplicative.toAdd (N a)) z = ρ a := by
  let ρ' : N.range →* Circle :=
    (QuotientGroup.lift N.ker ρ hker).comp (QuotientGroup.quotientKerEquivRange N).symm.toMonoidHom
  have hρ' : ∀ a, ρ' ⟨N a, a, rfl⟩ = ρ a := by
    intro a
    have h : (QuotientGroup.quotientKerEquivRange N).symm ⟨N a, a, rfl⟩ = (a : H ⧸ N.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  obtain ⟨ψ, hψ⟩ := exists_circle_character_extension N.range.subtype Subtype.val_injective ρ'
  obtain ⟨z, hz⟩ := exists_torusCharacter_eq ψ
  refine ⟨z, fun a => ?_⟩
  rw [hz, ofAdd_toAdd, ← hρ' a, ← hψ]
  rfl

variable (mu : Measure (J → Circle)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
  (K : Subgroup (J → Circle)) [Fintype K]

/-- The Fourier coefficients of `∑_{w ∈ K} f(· w)` are `|K| f̂(n)` if `χₙ` is trivial on `K`
and `0` otherwise. -/
theorem torusFourierCoeff_sum_mul_right [DecidablePred (IsTrivialOn K)]
    {f : (J → Circle) → ℂ} (hf : Continuous f) (n : J → ℤ) :
    torusFourierCoeff mu (fun x => ∑ w : K, f (x * w)) n =
      (if IsTrivialOn K n then (Fintype.card K : ℂ) else 0) * torusFourierCoeff mu f n := by
  unfold torusFourierCoeff
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun w _ => by
    simpa using integrable_mul_torusCharacter mu (hf.comp (continuous_id.mul continuous_const)) n]
  simp_rw [integral_mul_right_mul_torusCharacter mu f n, ← Finset.mul_sum, ← map_sum,
    sum_torusCharacter_subgroup K n]
  unfold torusFourierCoeff
  split_ifs <;> simp [mul_comm]

/-- **Partial Fourier series over a finite-index sublattice, summability on the lattice only**:
for `f` continuous and `∑_{n ∈ Λ} |f̂(n)| < ∞`,
`∑_{n ∈ Λ} f̂(n) conj(χₙ(z)) = μ(T) |Λ^⊥|⁻¹ ∑_{w ∈ Λ^⊥} f(z w)`. -/
theorem hasSum_torusFourierCoeff_mul_conj_lattice (Λ : AddSubgroup (J → ℤ)) [Λ.FiniteIndex]
    [Fintype (latticeAnnihilator Λ)] {f : (J → Circle) → ℂ} (hf : Continuous f)
    (hs : Summable fun m : Λ => ‖torusFourierCoeff mu f m‖) (z : J → Circle) :
    HasSum (fun m : Λ => torusFourierCoeff mu f m * conj (torusCharacter m z))
      ((mu.real univ : ℂ) / Fintype.card (latticeAnnihilator Λ) *
        ∑ w : latticeAnnihilator Λ, f (z * w)) := by
  classical
  set Fs : (J → Circle) → ℂ := fun x => ∑ w : (latticeAnnihilator Λ), f (x * w)
  have hF : Continuous Fs :=
    continuous_finsetSum _ fun w _ => hf.comp (continuous_id.mul continuous_const)
  have hcoeff : ∀ n, torusFourierCoeff mu Fs n =
      (Λ : Set (J → ℤ)).indicator
        (fun n => (Fintype.card (latticeAnnihilator Λ) : ℂ) * torusFourierCoeff mu f n) n := by
    intro n
    rw [torusFourierCoeff_sum_mul_right mu (latticeAnnihilator Λ) hf n]
    by_cases hn : n ∈ Λ
    · rw [ite_eq_left ((isTrivialOn_latticeAnnihilator_iff Λ).mpr hn),
        Set.indicator_of_mem (show n ∈ (Λ : Set (J → ℤ)) from hn)]
    · rw [ite_eq_right (fun h => hn ((isTrivialOn_latticeAnnihilator_iff Λ).mp h)),
        Set.indicator_of_notMem (show n ∉ (Λ : Set (J → ℤ)) from hn), zero_mul]
  have hFs : Summable fun n => ‖torusFourierCoeff mu Fs n‖ := by
    have h1 : Summable ((Λ : Set (J → ℤ)).indicator
        fun n => (Fintype.card (latticeAnnihilator Λ) : ℝ) * ‖torusFourierCoeff mu f n‖) :=
      (summable_subtype_iff_indicator (s := (Λ : Set (J → ℤ)))).mp
        (hs.mul_left (Fintype.card (latticeAnnihilator Λ) : ℝ))
    refine h1.congr fun n => ?_
    rw [hcoeff]
    by_cases hn : n ∈ (Λ : Set (J → ℤ))
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, norm_mul]
      simp
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, norm_zero]
  have hinv := hasSum_torusFourierCoeff_mul_conj mu hF hFs z
  have hind : (fun n => torusFourierCoeff mu Fs n * conj (torusCharacter n z)) =
      (Λ : Set (J → ℤ)).indicator
        (fun n => (Fintype.card (latticeAnnihilator Λ) : ℂ) *
          (torusFourierCoeff mu f n * conj (torusCharacter n z))) := by
    funext n
    rw [hcoeff]
    by_cases hn : n ∈ (Λ : Set (J → ℤ))
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, mul_assoc]
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, zero_mul]
  rw [hind, ← hasSum_subtype_iff_indicator] at hinv
  have hcard : (Fintype.card (latticeAnnihilator Λ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h2 := hinv.mul_left (Fintype.card (latticeAnnihilator Λ) : ℂ)⁻¹
  convert h2 using 1
  · funext m
    simp only [Function.comp_apply]
    field_simp
  · simp only [Fs]
    field_simp

end Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalSplitCenterFourierInversion1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalSplitCenterFourierInversion2 :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (hG : GroupScheme.IsConnectedReductive G)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- `n(g) = 0` exactly on `G¹`. -/
theorem rationalValuationCoordinates_eq_zero_iff (g : GroupScheme.rationalPoints G) :
    rationalValuationCoordinates G hG g = 0 ↔ g ∈ rationalCommonNormKernel G := by
  rw [← rationalValuationImageProjection_ker, MonoidHom.mem_ker, rationalValuationCoordinates,
    AddEquiv.map_eq_zero_iff]
  exact ofMul_eq_zero

omit [LocallyOfFiniteType G.X.hom] in
/-- Unitary unramified characters are trivial on `G¹` (membership in `unramifiedCharacters`). -/
theorem unitaryUnramifiedCharacter_apply_of_mem
    (χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    {g : GroupScheme.rationalPoints G} (hg : g ∈ rationalCommonNormKernel G) :
    ((χ.val g : ℂˣ) : ℂ) = 1 := by
  have h1 : χ.val g = 1 := χ.2.1 hg
  rw [h1, Units.val_one]

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- Waldspurger's integrand `a ↦ η(a⁻¹) ∫_{Im X(G)} f(χ) χ(a) c(a) dχ` on `A_G = s(T(F))`, for
unitary characters `c`, `η` of `A_G` and the I.1 measure on `Im X(G)`
(`rationalUnitaryUnramifiedCharacterHaar`). In the proof of Proposition VII.2.1, `c = χ_{ω₀}`,
`η = χ_{ω'}` and `f(χ) = (E^G_G ψ_{ω₀ ⊗ χ})(g)`. -/
def rationalSplitCenterInversionIntegrand
    (c eta : (GroupScheme.rationalPoints.map s).range →* Circle)
    (f : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) → ℂ)
    (a : (GroupScheme.rationalPoints.map s).range) : ℂ :=
  ((eta a⁻¹ : Circle) : ℂ) *
    ∫ χ, f χ * (((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ))
      ∂rationalUnitaryUnramifiedCharacterHaar s hs hindex

/-- **Vanishing for different restrictions to `A_G ∩ G¹`**: if `η ≠ c` at a point of
`A_G ∩ G¹`, the integral over `A_G` of the inversion integrand vanishes, for every left invariant
measure on `A_G`. -/
theorem integral_rationalSplitCenterInversionIntegrand_eq_zero
    [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
    [BorelSpace (GroupScheme.rationalPoints.map s).range]
    (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
    (c eta : (GroupScheme.rationalPoints.map s).range →* Circle)
    (f : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) → ℂ)
    (h : ∃ b : (GroupScheme.rationalPoints.map s).range,
      (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G ∧ eta b ≠ c b) :
    ∫ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f a ∂ν = 0 := by
  obtain ⟨b, hb, hne⟩ := h
  set I := ∫ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f a ∂ν
  have hshift : ∀ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f (b * a) =
      (((eta b)⁻¹ * c b : Circle) : ℂ) *
        rationalSplitCenterInversionIntegrand s hs hindex c eta f a := by
    intro a
    have hpt : ∀ χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul),
        f χ * (((χ.val ((b * a : (GroupScheme.rationalPoints.map s).range) :
          GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c (b * a) : ℂ)) =
        (c b : ℂ) *
          (f χ * (((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ))) := by
      intro χ
      rw [Subgroup.coe_mul, map_mul, Units.val_mul, unitaryUnramifiedCharacter_apply_of_mem χ hb,
        map_mul, Circle.coe_mul]
      ring
    simp only [rationalSplitCenterInversionIntegrand]
    simp_rw [hpt]
    rw [integral_const_mul]
    simp only [mul_inv_rev, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
    ring
  have hI : I = (((eta b)⁻¹ * c b : Circle) : ℂ) * I := by
    calc I = ∫ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f (b * a) ∂ν :=
          (integral_mul_left_eq_self _ b).symm
      _ = _ := by simp_rw [hshift]; exact integral_const_mul _ _
  have hne' : (((eta b)⁻¹ * c b : Circle) : ℂ) ≠ 1 := by
    intro h1
    apply hne
    have h2 : (eta b)⁻¹ * c b = 1 := Circle.coe_injective (by simpa using h1)
    exact (inv_mul_eq_one.mp h2)
  have h3 : (1 - (((eta b)⁻¹ * c b : Circle) : ℂ)) * I = 0 := by
    linear_combination hI
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne'.symm)

include hG in
/-- **Fourier inversion over `A_G` for equal restrictions to `A_G ∩ G¹`**: if `η = c` on
`A_G ∩ G¹`, `f` is continuous on `Im X(G)` and the inversion integrand is integrable for a left
invariant measure `ν` on `A_G`, then its integral is
`ν(A_G ∩ G¹) ∑_{χ ∈ Im X(G) ; χ c = η on A_G} f(χ)`, the sum being over a coset of the finite
kernel of the restriction `Im X(G) → Im X(T)`. -/
theorem integral_rationalSplitCenterInversionIntegrand
    [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
    [BorelSpace (GroupScheme.rationalPoints.map s).range]
    (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
    (c eta : (GroupScheme.rationalPoints.map s).range →* Circle)
    {f : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) → ℂ}
    (hf : Continuous f)
    (h : ∀ b : (GroupScheme.rationalPoints.map s).range,
      (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G → eta b = c b)
    (hint : Integrable (rationalSplitCenterInversionIntegrand s hs hindex c eta f) ν) :
    ∫ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f a ∂ν =
      ((ν (Subtype.val ⁻¹'
        (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal
          : ℂ) *
        ∑ᶠ χ ∈ {χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) |
          ∀ a : (GroupScheme.rationalPoints.map s).range,
            ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) = (eta a : ℂ)},
          f χ := by
  classical
  set K := rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG
  set Λ := rationalSplitLattice hG s
  set I := ∫ a, rationalSplitCenterInversionIntegrand s hs hindex c eta f a ∂ν
  have : Λ.FiniteIndex := finiteIndex_rationalSplitLattice hG s hindex
  have : Finite (latticeAnnihilator Λ) := finite_latticeAnnihilator Λ
  let : Fintype (latticeAnnihilator Λ) := Fintype.ofFinite _
  have := compactSpace_rationalUnitaryUnramifiedCharacters G
  let n : GroupScheme.rationalPoints G → Fin (rationalImageRank G) → ℤ :=
    rationalValuationCoordinates G hG
  -- `a ↦ n(a)` as a homomorphism on `A_G`; its kernel is `A_G ∩ G¹`
  let N : (GroupScheme.rationalPoints.map s).range →*
      Multiplicative (Fin (rationalImageRank G) → ℤ) :=
    { toFun := fun a => Multiplicative.ofAdd (n a)
      map_one' := by
        show Multiplicative.ofAdd (rationalValuationCoordinates G hG 1) = 1
        rw [rationalValuationCoordinates_one, ofAdd_zero]
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (rationalValuationCoordinates G hG (a * b)) = _
        rw [rationalValuationCoordinates_mul, ofAdd_add] }
  have hNker : ∀ a : (GroupScheme.rationalPoints.map s).range,
      N a = 1 ↔ (a : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G :=
    fun a => ofAdd_eq_one.trans (rationalValuationCoordinates_eq_zero_iff hG a)
  have hnΛ : ∀ a : (GroupScheme.rationalPoints.map s).range, n a ∈ Λ := fun a => by
    obtain ⟨t, ht⟩ := a.2
    exact (mem_rationalSplitLattice hG s).mpr ⟨t, by rw [ht]⟩
  -- the character `η c⁻¹` of `A_G` is `a ↦ χ_{n(a)}(z')` for a torus point `z'`
  obtain ⟨z', hz'⟩ := exists_torusCharacter_eq_of_ker_le N (eta * c⁻¹) (by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h a ((hNker a).mp ha), mul_inv_cancel])
  have hz'' : ∀ a : (GroupScheme.rationalPoints.map s).range,
      torusCharacter (n a) z' = ((eta a * (c a)⁻¹ : Circle) : ℂ) := fun a =>
    hz' a
  -- the measure on the torus transported by the coordinates
  let mu : Measure (Fin (rationalImageRank G) → Circle) :=
    Measure.map K (rationalUnitaryUnramifiedCharacterHaar s hs hindex)
  have : mu.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ K
  have : IsFiniteMeasure (rationalUnitaryUnramifiedCharacterHaar s hs hindex) := inferInstance
  have : IsFiniteMeasure mu := Measure.isFiniteMeasure_map _ _
  let Fz : (Fin (rationalImageRank G) → Circle) → ℂ := fun z => f (K.symm z)
  have hFz : Continuous Fz := hf.comp K.symm.continuous
  have hchar : ∀ (χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
      (g : GroupScheme.rationalPoints G), ((χ.val g : ℂˣ) : ℂ) = torusCharacter (n g) (K χ) := by
    intro χ g
    have h1 := rationalUnitaryUnramifiedCharacter_apply G hG (K χ) g
    rwa [ContinuousMulEquiv.symm_apply_apply] at h1
  have hcoeff : ∀ g : GroupScheme.rationalPoints G,
      ∫ χ, f χ * ((χ.val g : ℂˣ) : ℂ) ∂rationalUnitaryUnramifiedCharacterHaar s hs hindex =
        torusFourierCoeff mu Fz (n g) := by
    intro g
    have hmap : mu = Measure.map K.toHomeomorph.toMeasurableEquiv
        (rationalUnitaryUnramifiedCharacterHaar s hs hindex) := rfl
    rw [torusFourierCoeff, hmap, integral_map_equiv]
    congr 1
    funext χ
    rw [hchar χ g]
    show f χ * torusCharacter (n g) (K χ) = f (K.symm (K χ)) * torusCharacter (n g) (K χ)
    rw [ContinuousMulEquiv.symm_apply_apply]
  -- closed form of the integrand
  let Φ : (Fin (rationalImageRank G) → ℤ) → ℂ := fun m =>
    torusFourierCoeff mu Fz m * conj (torusCharacter m z')
  have hform : ∀ a : (GroupScheme.rationalPoints.map s).range,
      rationalSplitCenterInversionIntegrand s hs hindex c eta f a = Φ (n a) := by
    intro a
    have h1 : ∀ χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul),
        f χ * (((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ)) =
          f χ * ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) :=
      fun χ => by ring
    simp only [rationalSplitCenterInversionIntegrand, h1]
    rw [integral_mul_const, hcoeff]
    simp only [Φ]
    rw [hz'' a, ← Circle.coe_inv_eq_conj]
    simp only [map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv, inv_inv]
    ring
  have hF : ∀ a, ∀ b ∈ N.ker, rationalSplitCenterInversionIntegrand s hs hindex c eta f (a * b) =
      rationalSplitCenterInversionIntegrand s hs hindex c eta f a := by
    intro a b hb
    have hb0 : n b = 0 := (rationalValuationCoordinates_eq_zero_iff hG b).mpr
      ((hNker b).mp (MonoidHom.mem_ker.mp hb))
    rw [hform, hform]
    congr 1
    show rationalValuationCoordinates G hG (a * b) = _
    rw [rationalValuationCoordinates_mul, show rationalValuationCoordinates G hG b = 0 from hb0,
      add_zero]
  have hker_set : (N.ker : Set (GroupScheme.rationalPoints.map s).range) =
      Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)) := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
    exact hNker a
  have hopen : IsOpen (N.ker : Set (GroupScheme.rationalPoints.map s).range) := by
    rw [hker_set]
    exact (isOpen_rationalCommonNormKernel G).preimage continuous_subtype_val
  have : Countable ((GroupScheme.rationalPoints.map s).range ⧸ N.ker) :=
    (Multiplicative.toAdd.injective.comp (QuotientGroup.kerLift_injective N)).countable
  -- the quotient `A_G / (A_G ∩ G¹)` is the lattice `Λ_s`
  have hΛ : ∀ q : (GroupScheme.rationalPoints.map s).range ⧸ N.ker,
      Multiplicative.toAdd (QuotientGroup.kerLift N q) ∈ Λ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => rw [QuotientGroup.kerLift_mk]; exact hnΛ a
  let e : (GroupScheme.rationalPoints.map s).range ⧸ N.ker ≃ Λ :=
    Equiv.ofBijective (fun q => ⟨_, hΛ q⟩) ⟨fun q q' hqq' =>
      QuotientGroup.kerLift_injective N
        (Multiplicative.toAdd.injective (congrArg Subtype.val hqq')),
    fun m => by
      obtain ⟨t, ht⟩ := (mem_rationalSplitLattice hG s).mp m.2
      refine ⟨QuotientGroup.mk ⟨GroupScheme.rationalPoints.map s t, t, rfl⟩, Subtype.ext ?_⟩
      simp only [QuotientGroup.kerLift_mk]
      exact ht⟩
  have he : ∀ q : (GroupScheme.rationalPoints.map s).range ⧸ N.ker,
      ((e q : Λ) : Fin (rationalImageRank G) → ℤ) =
        n (q.out : (GroupScheme.rationalPoints.map s).range) := by
    intro q
    show Multiplicative.toAdd (QuotientGroup.kerLift N q) = _
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.kerLift_mk]
    rfl
  have hval : ∀ q : (GroupScheme.rationalPoints.map s).range ⧸ N.ker,
      cosetValues N.ker (rationalSplitCenterInversionIntegrand s hs hindex c eta f) q =
        Φ (e q) := by
    intro q
    rw [cosetValues, hform, he]
  have hsum := hasSum_integral_quotient hopen hF hint
  simp only [hval] at hsum
  rw [hker_set] at hsum
  set r :=
    (ν (Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal
  by_cases hr : r = 0
  · have hI : I = 0 := by
      simp only [hr, zero_smul] at hsum
      exact hsum.unique hasSum_zero
    rw [hI, hr, Complex.ofReal_zero, zero_mul]
  -- summability of the Fourier coefficients on `Λ_s`
  have hnorm := hasSum_integral_quotient hopen (F := fun a =>
      ‖rationalSplitCenterInversionIntegrand s hs hindex c eta f a‖)
    (fun a b hb => by simp only [hF a b hb]) hint.norm
  have hsumm : Summable fun m : Λ => ‖torusFourierCoeff mu Fz m‖ := by
    rw [hker_set] at hnorm
    have h1 : Summable fun q : (GroupScheme.rationalPoints.map s).range ⧸ N.ker =>
        r * ‖torusFourierCoeff mu Fz (e q)‖ := by
      refine hnorm.summable.congr fun q => ?_
      simp only [cosetValues, smul_eq_mul, r]
      rw [hform, ← he, norm_mul, Complex.norm_conj, norm_torusCharacter, mul_one]
    exact (e.summable_iff (f := fun m : Λ => ‖torusFourierCoeff mu Fz m‖)).mp
      ((summable_mul_left_iff hr).mp h1)
  have hlat := hasSum_torusFourierCoeff_mul_conj_lattice mu Λ hFz hsumm z'
  have hlat' := ((e.hasSum_iff (f := fun m : Λ => torusFourierCoeff mu Fz m *
    conj (torusCharacter m z'))).mpr hlat).mul_left (r : ℂ)
  have hI : I = (r : ℂ) * ((mu.real univ : ℂ) / Fintype.card (latticeAnnihilator Λ) *
      ∑ w : latticeAnnihilator Λ, Fz (z' * w)) := by
    refine hsum.unique (hlat'.congr_fun fun q => ?_)
    simp only [Function.comp_apply, Complex.real_smul, Φ]
  -- total mass of the character measure against the size of the annihilator
  have hcard : Nat.card (latticeAnnihilator Λ) =
      Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker :=
    Nat.card_congr (K.symm.toEquiv.subtypeEquiv fun z =>
      (coordinates_symm_mem_restrict_ker_iff hG s z).symm)
  have hmass :
      mu.real univ = Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker := by
    rw [measureReal_def, Measure.map_apply (map_continuous K).measurable MeasurableSet.univ,
      Set.preimage_univ, rationalUnitaryUnramifiedCharacterHaar_univ, ENNReal.toReal_natCast]
  have hratio : (mu.real univ : ℂ) / Fintype.card (latticeAnnihilator Λ) = 1 := by
    rw [Fintype.card_eq_nat_card, hcard, hmass, Complex.ofReal_natCast]
    refine div_self ?_
    rw [← hcard, Nat.cast_ne_zero, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  -- the fibre `{χ | χ c = η on A_G}` is `K⁻¹(z' Λ^⊥)`
  have hS : {χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) |
      ∀ a : (GroupScheme.rationalPoints.map s).range,
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) = (eta a : ℂ)} =
      Set.range fun w : latticeAnnihilator Λ => K.symm (z' * w) := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · intro hχ
      refine ⟨⟨z'⁻¹ * K χ, fun m hm => ?_⟩, ?_⟩
      · obtain ⟨t, rfl⟩ := (mem_rationalSplitLattice hG s).mp hm
        set a : (GroupScheme.rationalPoints.map s).range :=
          ⟨GroupScheme.rationalPoints.map s t, t, rfl⟩
        have hχa : torusCharacter (n a) (K χ) = ((eta a * (c a)⁻¹ : Circle) : ℂ) := by
          rw [← hchar, Circle.coe_mul, Circle.coe_inv]
          exact (eq_mul_inv_iff_mul_eq₀ (Circle.coe_ne_zero _)).mpr (hχ a)
        show torusCharacter (n a) (z'⁻¹ * K χ) = 1
        rw [torusCharacter_mul, torusCharacter_inv, hz'' a, hχa, ← Circle.coe_inv_eq_conj,
          ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
      · simp only [mul_inv_cancel_left, ContinuousMulEquiv.symm_apply_apply]
    · rintro ⟨w, rfl⟩ a
      rw [hchar, ContinuousMulEquiv.apply_symm_apply, torusCharacter_mul, hz'' a,
        w.2 _ (hnΛ a), mul_one, ← Circle.coe_mul, inv_mul_cancel_right]
  have hinj : Function.Injective fun w : latticeAnnihilator Λ => K.symm (z' * w) :=
    fun w w' hww' => Subtype.ext (mul_left_cancel (K.symm.injective hww'))
  rw [hI, hratio, one_mul, hS, finsum_mem_range hinj, finsum_eq_sum_of_fintype]

end Langlands.HarishChandraSchwartz
