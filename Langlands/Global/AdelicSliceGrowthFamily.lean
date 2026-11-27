import Langlands.Global.AdelicSliceDerivativeCalculus
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicParabolicQuotient

/-! # A class of functions with uniformly bounded slice derivatives, stable under twisted
differentiation

`HasUniformSliceGrowth hsmooth Γ H e ψ` says that `ψ` has smooth infinite slices, is left
invariant under `Γ`, and that every iterated invariant derivative of its slices is bounded by a
constant times `H ^ e`, with the same exponent `e` for all derivatives. When the Iwasawa height
pairings are smooth and `K` is maximal compact, the twisted derivative
`IsIwasawaCompact.parameterDirectionalSection` preserves this class for subgroups `Γ` of the
image of the parabolic: it is the untwisted slice derivative plus the product with the
derivative of the height pairing, whose iterated derivatives are bounded. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]

section Class

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Adeles" => AdelicGroupPoints F G

/-- Smooth infinite slices, left invariance under `Γ`, and one exponent `e` with
`‖D_v ψ(a, b)‖ ≤ C_v H(a, b) ^ e` for every iterated invariant derivative `D_v` of the slices. -/
def HasUniformSliceGrowth (Γ : Subgroup Adeles) (H : Adeles → ℝ) (e : ℝ) (ψ : Adeles → ℂ) :
    Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  (∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => ψ (pair F G a b))) ∧ IsLeftInvariantUnder F G Γ ψ ∧
    ∀ v : List (smoothModel F d), ∃ C : ℝ, ∀ b a,
      ‖listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) v
        (fun z => ψ (pair F G z b)) a‖ ≤ C * H (pair F G a b) ^ e

end Class

section Twisted

variable {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Adeles" => AdelicGroupPoints F G

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- At the parameter `0` the twisted derivative is the untwisted slice derivative. -/
theorem IsIwasawaCompact.parameterDirectionalSection_zero (X : smoothModel F d)
    (ψ : Adeles → ℂ) :
    hK.parameterDirectionalSection hsmooth 0 X ψ = sliceDerivative hsmooth X ψ := by
  have h1 (g : Adeles) : hK.heightPower 0 g = 1 := by
    simp [IsIwasawaCompact.heightPower]
  have htw : hK.parameterTwist ψ 0 = ψ := by
    funext g
    simp [IsIwasawaCompact.parameterTwist, h1]
  funext g
  simp only [IsIwasawaCompact.parameterDirectionalSection, htw]
  change _ / hK.heightPower 0 g = _
  rw [h1, div_one]
  rfl

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The twisted derivative is the slice derivative plus the product with the derivative of the
height pairing. -/
theorem IsIwasawaCompact.parameterDirectionalSection_eq_sliceDerivative
    (hH : hK.HasSmoothHeightPairings hsmooth) (X : smoothModel F d) (ψ : Adeles → ℂ)
    (hψ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => ψ (pair F G a b)))
    (lam : ComplexCharacterParameter F P) :
    hK.parameterDirectionalSection hsmooth lam X ψ =
      sliceDerivative hsmooth X ψ +
        ψ * sliceDerivative hsmooth X (fun g => complexParameterPairing F P lam (hK.height g)) := by
  rw [hK.parameterDirectionalSection_eq_add hsmooth hH X ψ hψ lam,
    hK.parameterDirectionalSection_zero hsmooth]
  rfl

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem parabolicQuotientSubgroup_le_range {U M : GroupScheme (Spec (CommRingCat.of F))}
    (iU : U ⟶ P) (l : M ⟶ P) :
    parabolicQuotientSubgroup F p iU l ≤ (map F P G p).toMonoidHom.range := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    exact ⟨map F U P iU x, (map_comp_apply_of_hom iU x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨map F M P l (rational F M x), (map_comp_apply_of_hom l (rational F M x)).symm⟩

/-- The twisted derivative preserves uniform slice growth for subgroups of the image of the
parabolic, when the height pairings are smooth and `K` contains the infinite components of its
elements. -/
theorem IsIwasawaCompact.hasUniformSliceGrowth_parameterDirectionalSection
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    {Γ : Subgroup Adeles} (hΓ : Γ ≤ (map F P G p).toMonoidHom.range)
    {H : Adeles → ℝ} {e : ℝ}
    (lam : ComplexCharacterParameter F P) (X : smoothModel F d) {ψ : Adeles → ℂ}
    (hψ : HasUniformSliceGrowth hsmooth Γ H e ψ) :
    HasUniformSliceGrowth hsmooth Γ H e (hK.parameterDirectionalSection hsmooth lam X ψ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  obtain ⟨hs, hinv, hb⟩ := hψ
  let Pr : Adeles → ℂ := fun g => complexParameterPairing F P lam (hK.height g)
  have hPrs : ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => Pr (pair F G a b)) := hH lam
  rw [hK.parameterDirectionalSection_eq_sliceDerivative hsmooth hH X ψ hs lam]
  have hslice (b : FiniteAdelicGroupPoints F G) :
      (fun a => (sliceDerivative hsmooth X ψ + ψ * sliceDerivative hsmooth X Pr) (pair F G a b)) =
        groupDirectionalValue 𝓘∞ X (fun a => ψ (pair F G a b)) +
          (fun a => ψ (pair F G a b)) * groupDirectionalValue 𝓘∞ X (fun a => Pr (pair F G a b)) := by
    funext a
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [← congrFun (sliceDerivative_pair hsmooth X ψ b) a,
      ← congrFun (sliceDerivative_pair hsmooth X Pr b) a]
  have hds (b : FiniteAdelicGroupPoints F G) :=
    contMDiff_groupDirectionalValue 𝓘∞ X (hs b)
  have hdPr (b : FiniteAdelicGroupPoints F G) :=
    contMDiff_groupDirectionalValue 𝓘∞ X (hPrs b)
  refine ⟨fun b => ?_, ?_, fun v => ?_⟩
  · rw [hslice b]
    exact (hds b).add (contMDiff_mul_complex (hs b) (hdPr b))
  · intro x hx g
    obtain ⟨q, rfl⟩ := hΓ hx
    have hx' : map F P G p q ∈ Γ := hx
    change (sliceDerivative hsmooth X ψ + ψ * sliceDerivative hsmooth X Pr) (map F P G p q * g) =
      (sliceDerivative hsmooth X ψ + ψ * sliceDerivative hsmooth X Pr) g
    have h1 : sliceDerivative hsmooth X ψ (map F P G p q * g) = sliceDerivative hsmooth X ψ g :=
      sliceDerivative_mul_of_add_const hsmooth X hs _ 0
        (fun g => by rw [hinv _ hx', add_zero]) g
    have h2 : sliceDerivative hsmooth X Pr (map F P G p q * g) = sliceDerivative hsmooth X Pr g :=
      sliceDerivative_mul_of_add_const hsmooth X hPrs _
        (complexParameterPairing F P lam (characterLog F P q))
        (fun g => by
          change complexParameterPairing F P lam (hK.height (map F P G p q * g)) =
            complexParameterPairing F P lam (hK.height g) + _
          rw [hK.height_map_mul, map_add, add_comm]) g
    simp only [Pi.add_apply, Pi.mul_apply, h1, h2, hinv _ hx']
  · have hderPr (w : List (smoothModel F d)) : ∃ M : ℝ, ∀ b a,
        ‖listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) w
          (groupDirectionalValue 𝓘∞ X (fun z => Pr (pair F G z b))) a‖ ≤ M :=
      hK.exists_bound_heightPairing_derivative hsmooth hH hInf lam (w := X :: w) (by simp)
    obtain ⟨C₁, hC₁⟩ := hb (X :: v)
    obtain ⟨C₂, hC₂⟩ := exists_bound_listDirectionalDerivative_mul
      (fun b a => H (pair F G a b) ^ e) v (fun b => fun z => ψ (pair F G z b))
      (fun b => groupDirectionalValue 𝓘∞ X (fun z => Pr (pair F G z b))) hs hdPr hb hderPr
    refine ⟨C₁ + C₂, fun b a => ?_⟩
    rw [hslice b, listDirectionalDerivative_add v (hds b) (contMDiff_mul_complex (hs b) (hdPr b)),
      Pi.add_apply]
    calc _ ≤ ‖listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) v
            (groupDirectionalValue 𝓘∞ X (fun z => ψ (pair F G z b))) a‖ +
          ‖listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) v
            ((fun z => ψ (pair F G z b)) *
              groupDirectionalValue 𝓘∞ X (fun z => Pr (pair F G z b))) a‖ := norm_add_le _ _
      _ ≤ C₁ * H (pair F G a b) ^ e + C₂ * H (pair F G a b) ^ e :=
          add_le_add (hC₁ b a) (hC₂ b a)
      _ = (C₁ + C₂) * H (pair F G a b) ^ e := by ring

end Twisted

end Langlands.Global.AdelicGroupPoints
