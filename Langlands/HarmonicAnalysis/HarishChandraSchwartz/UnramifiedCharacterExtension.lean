import Langlands.Representation.Plancherel.RationalRestrictionSurjectivity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Extension of unitary characters to unramified characters

Waldspurger, VIII.5 (printed pp. 331–332), proof of Theorem VIII.1.2, uses that every unitary
character of `A_G` trivial on `A_G ∩ G¹` is the restriction of an element of `Im X(G)`. For an
abstract family `ν` of positive characters with open common norm kernel `G¹` this holds for every
subgroup `A`: the character factors through the image of `A` under the joint norm map
`commonNormMap ν : G →* (I → ℝ≥0ˣ)`, whose kernel is `G¹`; the circle group is divisible, hence
an injective `ℤ`-module, so the character extends to the commutative group `I → ℝ≥0ˣ`; and the
composite with `commonNormMap ν` is continuous because its kernel contains the open subgroup `G¹`.

* The imported `Langlands.Plancherel.exists_circle_character_extension`: circle-valued characters extend along injective
  homomorphisms of commutative groups;
* `exists_unitaryUnramifiedCharacter_restrict_eq`: the extension statement above;
* `finite_discreteSeriesFixedOrbits_of_finite_central` and
  `finite_discreteSeriesFixedOrbits_of_finiteDimensional`: the two finiteness theorems of
  `DiscreteSeriesOrbitFiniteness` without their extension hypothesis, which follows here from the
  openness of `G¹` (it contains the open subgroup `H`).
-/

noncomputable section

open scoped NNReal

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe uG uV uI

section NormMap

variable {G : Type uG} [Group G] {I : Type uI}

/-- The joint norm map `g ↦ (ν i g)ᵢ`. Its kernel is the common norm kernel `G¹`. -/
def commonNormMap (ν : I → (G →* ℝ≥0ˣ)) : G →* (I → ℝ≥0ˣ) :=
  MonoidHom.pi ν

@[simp]
theorem commonNormMap_apply (ν : I → (G →* ℝ≥0ˣ)) (g : G) (i : I) :
    commonNormMap ν g i = ν i g :=
  rfl

theorem ker_commonNormMap (ν : I → (G →* ℝ≥0ˣ)) :
    (commonNormMap ν).ker = commonNormKernel ν := by
  ext g
  rw [MonoidHom.mem_ker, mem_commonNormKernel, funext_iff]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Extension of unitary characters to `Im X(G)`.** If the common norm kernel `G¹` is open,
then for every subgroup `A`, every unitary character of `A` trivial on `A ∩ G¹` is the
restriction of an element of `unitaryUnramifiedCharacters ν` (Waldspurger's `Im X(G)`). -/
theorem exists_unitaryUnramifiedCharacter_restrict_eq (ν : I → (G →* ℝ≥0ˣ))
    (hG1 : IsOpen (commonNormKernel ν : Set G)) (A : Subgroup G) (χ : A →* ℂˣ)
    (hχn : ∀ a, ‖(χ a : ℂ)‖ = 1) (hχ1 : ∀ a : A, (a : G) ∈ commonNormKernel ν → χ a = 1) :
    ∃ η ∈ unitaryUnramifiedCharacters ν, ∀ a : A, η a = χ a := by
  -- `χ` as a circle-valued character
  let χc : A →* Circle :=
    { toFun := fun a => ⟨(χ a : ℂ), mem_sphere_zero_iff_norm.2 (hχn a)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Circle.ext
        change ((χ (a * b) : ℂˣ) : ℂ) = (χ a : ℂ) * (χ b : ℂ)
        rw [map_mul, Units.val_mul] }
  -- `χ` factors through the image of `A` under the joint norm map
  let φ : A →* (I → ℝ≥0ˣ) := (commonNormMap ν).comp A.subtype
  have hker : φ.ker ≤ χc.ker := by
    intro a ha
    have ha1 : (a : G) ∈ commonNormKernel ν := by
      rw [← ker_commonNormMap]
      exact ha
    rw [MonoidHom.mem_ker]
    apply Circle.ext
    change ((χ a : ℂˣ) : ℂ) = ((1 : Circle) : ℂ)
    rw [hχ1 a ha1]
    rfl
  let χr : φ.range →* Circle :=
    (QuotientGroup.lift φ.ker χc hker).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hχr : ∀ a : A, χr ⟨φ a, ⟨a, rfl⟩⟩ = χc a := by
    intro a
    have hmk : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ a, ⟨a, rfl⟩⟩ =
        (a : A ⧸ φ.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift φ.ker χc hker
      ((QuotientGroup.quotientKerEquivRange φ).symm ⟨φ a, ⟨a, rfl⟩⟩) = χc a
    rw [hmk, QuotientGroup.lift_mk]
  -- extend from the image to `I → ℝ≥0ˣ` and pull back to `G`
  obtain ⟨ψ, hψ⟩ := exists_circle_character_extension φ.range.subtype
    Subtype.val_injective χr
  let η₀ : G →* ℂˣ := Circle.toUnits.comp (ψ.comp (commonNormMap ν))
  have hη₀ker : commonNormKernel ν ≤ η₀.ker := by
    intro g hg
    rw [← ker_commonNormMap, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    change Circle.toUnits (ψ (commonNormMap ν g)) = 1
    rw [hg, map_one, map_one]
  let η : G →ₜ* ℂˣ :=
    ⟨η₀, Langlands.Weil.continuous_of_open_kernel η₀ (Subgroup.isOpen_mono hη₀ker hG1)⟩
  refine ⟨η, ⟨hη₀ker, fun g => ?_⟩, fun a => ?_⟩
  · change ‖((Circle.toUnits (ψ (commonNormMap ν g)) : ℂˣ) : ℂ)‖ = 1
    simp
  · have h1 : ψ (φ a) = χc a := by
      rw [← hχr a]
      exact DFunLike.congr_fun hψ ⟨φ a, ⟨a, rfl⟩⟩
    apply Units.ext
    change ((Circle.toUnits (ψ (φ a)) : ℂˣ) : ℂ) = (χ a : ℂ)
    rw [h1]
    rfl

end NormMap

section Orbits

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
variable {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- **Theorem VIII.1.2 from the finiteness of the `E₂(G)^H_χ`** (Waldspurger, VIII.5, printed
pp. 331–332). Let `H` be an open subgroup contained in the common norm kernel `G¹` and let
`A ∩ G¹` be compact. If `E₂(G)^H_χ` is finite for every continuous unitary character `χ` of `A`
trivial on `A ∩ H`, then `Θ^H_G` is finite. -/
theorem finite_discreteSeriesFixedOrbits_of_finite_central (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hH1 : H ≤ commonNormKernel ν)
    (hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G))
    (hfin : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ H → χ a = 1) →
      (discreteSeriesCentralFixed.{uG, uV} A hA μ χ H).Finite) :
    (discreteSeriesFixedOrbits.{uG, uV} A hA μ ν H).Finite :=
  finite_discreteSeriesFixedOrbits A hA μ ν H hHo hH1 hA1
    (fun χ _ hχn hχ1 => exists_unitaryUnramifiedCharacter_restrict_eq ν
      (Subgroup.isOpen_mono hH1 hHo) A χ hχn hχ1) hfin

/-- **Theorem VIII.1.2 from Proposition VIII.4.1 and Theorem VIII.4.2** (Waldspurger, VIII.5,
printed pp. 331–332). Let `H` be a compact open subgroup contained in the common norm kernel `G¹`
and let `A ∩ G¹` be compact. If for every continuous unitary character `χ` of `A` trivial on
`A ∩ H` the `H`-bi-invariant coefficients of all `ω ∈ E₂(G)^H_χ` lie in one finite-dimensional
space (Waldspurger's `p_χ(°C_H)`), then `Θ^H_G` is finite. -/
theorem finite_discreteSeriesFixedOrbits_of_finiteDimensional (H : OpenSubgroup G)
    (hH : IsCompact (H : Set G)) (hH1 : H.toSubgroup ≤ commonNormKernel ν)
    (hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G))
    (hF : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ H → χ a = 1) →
      ∃ F : Submodule ℂ (G → ℂ), FiniteDimensional ℂ F ∧
        ∀ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA μ χ H.toSubgroup,
          ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f → f ∈ F) :
    (discreteSeriesFixedOrbits.{uG, uV} A hA μ ν H.toSubgroup).Finite :=
  finite_discreteSeriesFixedOrbits_of_coefficient_mem A hA μ ν H hH hH1 hA1
    (fun χ _ hχn hχ1 => exists_unitaryUnramifiedCharacter_restrict_eq ν
      (Subgroup.isOpen_mono hH1 H.isOpen) A χ hχn hχ1) hF

end Orbits

end Langlands.HarishChandraSchwartz
