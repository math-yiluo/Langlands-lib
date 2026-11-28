import Langlands.Global.AdelicNormOneRetraction
import Langlands.Automorphic.GroupSchemeNormOneWords
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction

/-! # Continuous rational extensions of functions on the norm-one group

For a connected reductive group, `normOneRetraction hG` is a chosen continuous map
`G(𝔸) → G(𝔸)¹` that fixes `G(𝔸)¹` and commutes with left and right multiplication by `G(𝔸)¹`.
A continuous left `G(F)`-invariant function `ψ` on `G(𝔸)¹` extends to the continuous left
`G(F)`-invariant function `normOneExtension hG ψ = ψ ∘ normOneRetraction hG` on `G(𝔸)`, an element
of `ContinuousRationalFunctions`. Right invariance under a compact finite level and joint
measurability of families pass to the extension. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "G¹" => normOneSubgroup F G

/-- A chosen continuous retraction of `G(𝔸)` onto `G(𝔸)¹`, equivariant for left and right
multiplication by `G(𝔸)¹`. -/
def normOneRetraction (hG : IsConnectedReductive G) : A → G¹ :=
  (exists_normOneRetraction F G hG).choose

theorem continuous_normOneRetraction (hG : IsConnectedReductive G) :
    Continuous (normOneRetraction hG) :=
  (exists_normOneRetraction F G hG).choose_spec.1

@[simp] theorem normOneRetraction_coe (hG : IsConnectedReductive G) (n : G¹) :
    normOneRetraction hG (n : A) = n :=
  (exists_normOneRetraction F G hG).choose_spec.2.1 n

theorem normOneRetraction_mul_left (hG : IsConnectedReductive G) (g : G¹) (x : A) :
    normOneRetraction hG ((g : A) * x) = g * normOneRetraction hG x :=
  (exists_normOneRetraction F G hG).choose_spec.2.2.1 g x

theorem normOneRetraction_mul_right (hG : IsConnectedReductive G) (x : A) (g : G¹) :
    normOneRetraction hG (x * (g : A)) = normOneRetraction hG x * g :=
  (exists_normOneRetraction F G hG).choose_spec.2.2.2 x g

/-- The extension of a function on `G(𝔸)¹` along the retraction. -/
def normOneExtension (hG : IsConnectedReductive G) (ψ : G¹ → ℂ) (x : A) : ℂ :=
  ψ (normOneRetraction hG x)

@[simp] theorem normOneExtension_coe (hG : IsConnectedReductive G) (ψ : G¹ → ℂ) (n : G¹) :
    normOneExtension hG ψ (n : A) = ψ n := by
  simp [normOneExtension]

theorem continuous_normOneExtension (hG : IsConnectedReductive G) {ψ : G¹ → ℂ}
    (hψ : Continuous ψ) : Continuous (normOneExtension hG ψ) :=
  hψ.comp (continuous_normOneRetraction hG)

/-- Left invariance under the rational points. -/
theorem normOneExtension_rational_mul (hG : IsConnectedReductive G) {ψ : G¹ → ℂ}
    (hinv : ∀ (g : rationalNormOneSubgroup F G) x, ψ ((g : G¹) * x) = ψ x)
    (q : RationalGroupPoints F G) (x : A) :
    normOneExtension hG ψ (rational F G q * x) = normOneExtension hG ψ x := by
  have h := normOneRetraction_mul_left hG (rationalNormOne F G q) x
  simp only [rationalNormOne_val] at h
  simp only [normOneExtension, h]
  exact hinv ⟨rationalNormOne F G q, ⟨q, rfl⟩⟩ _

/-- The extension as a continuous left `G(F)`-invariant function. -/
def normOneExtensionCRF (hG : IsConnectedReductive G) (ψ : G¹ → ℂ) (hψ : Continuous ψ)
    (hinv : ∀ (g : rationalNormOneSubgroup F G) x, ψ ((g : G¹) * x) = ψ x) :
    ContinuousRationalFunctions F G :=
  continuousQuotientLinearEquiv F G
    ⟨LeftCosetSpace.lift (rationalSubgroup F G) (normOneExtension hG ψ) (fun r x => by
        obtain ⟨q, hq⟩ := r.property
        change normOneExtension hG ψ (r.val * x) = _
        rw [← hq]
        exact normOneExtension_rational_mul hG hinv q x),
      (LeftCosetSpace.continuous_iff (rationalSubgroup F G)).mpr
        (continuous_normOneExtension hG hψ)⟩

@[simp] theorem evaluate_normOneExtensionCRF (hG : IsConnectedReductive G) (ψ : G¹ → ℂ)
    (hψ : Continuous ψ)
    (hinv : ∀ (g : rationalNormOneSubgroup F G) x, ψ ((g : G¹) * x) = ψ x) :
    evaluate F G (normOneExtensionCRF hG ψ hψ hinv) = normOneExtension hG ψ :=
  rfl

/-- Right invariance under a compact finite level. -/
theorem normOneExtension_mul_ofFinite (hG : IsConnectedReductive G)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))) {ψ : G¹ → ℂ}
    (hψ : ∀ (k : K₀) x, ψ (x * finiteLevelInclusion F G K₀ hK₀ k) = ψ x)
    (l : FiniteAdelicGroupPoints F G) (hl : l ∈ K₀) (x : A) :
    normOneExtension hG ψ (x * ofFinite F G l) = normOneExtension hG ψ x := by
  have h := normOneRetraction_mul_right hG x (finiteLevelInclusion F G K₀ hK₀ ⟨l, hl⟩)
  simp only [normOneExtension]
  rw [show x * ofFinite F G l = x * ((finiteLevelInclusion F G K₀ hK₀ ⟨l, hl⟩ : G¹) : A) from rfl,
    h, hψ]

/-- Joint measurability of the extensions of a family. -/
theorem measurable_normOneExtension_family (hG : IsConnectedReductive G) {Ω : Type w}
    [MeasurableSpace Ω] {ψ : Ω → G¹ → ℂ} (hψ : Measurable (fun p : Ω × G¹ => ψ p.1 p.2)) :
    Measurable (fun p : Ω × A => normOneExtension hG (ψ p.1) p.2) :=
  hψ.comp (measurable_fst.prodMk
    ((continuous_normOneRetraction hG).measurable.comp measurable_snd))

end Langlands.Global
