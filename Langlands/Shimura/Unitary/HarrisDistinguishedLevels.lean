import Langlands.Shimura.Unitary.HarrisDivisionLevels

/-!
# Harris's level `K_p` with a varying factor at the distinguished place

Harris's level (4.1) is `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`: an open compact subgroup `C_v` at
the distinguished place, allowed to vary, and fixed open compact subgroups `C^(j)` at the other
places above the chosen place of the imaginary quadratic field. The level `K(N)_p` is the case
where `C_v` is the congruence level and the `C^(j)` are the maximal compact subgroups. As `C_v`
varies, these levels form a functor on the level category, an arrow given by `h` going to the
arrow given by the point with component `h` at the distinguished place.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global AdelicFunctoriality

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  [Module.Finite ℚ A]
variable [Algebra E A] [IsScalarTower E K A] [IsScalarTower ℚ E A]
variable [Algebra.IsQuadraticExtension ℚ F]

variable (ι : F →+* K) (v : Global.FinitePlace ℚ) (𝔭 : FinitePlacesAbove F v)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v 𝔭.1))

open Classical in
/-- Harris's level `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ` of (4.1): the local level `C₀` at the
distinguished place `w₀` and the fixed local levels `C w` at the other places. -/
def SecondKindInvolution.distinguishedLevel (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    (C₀ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))) :
    CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :=
  σ.splitPlaceLevel ι v 𝔭 h𝔭 (Function.update C w₀ C₀)

omit [IsScalarTower E K A] in
/-- A point lies in `K_p` exactly when its component at `w₀` lies in `C₀`, its other
components lie in the fixed levels and its multiplier lies in `ℤ_vˣ`. -/
theorem SecondKindInvolution.mem_distinguishedLevel (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    (C₀ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K)))
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    g ∈ (σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀).subgroup ↔
      (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w₀ ∈ C₀.subgroup ∧
        (∀ w, w ≠ w₀ → (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w ∈ (C w).subgroup) ∧
        AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g ∈
          (integerUnitsLevel v).subgroup := by
  classical
  rw [SecondKindInvolution.distinguishedLevel, SecondKindInvolution.mem_splitPlaceLevel]
  constructor
  · rintro ⟨hC, hm⟩
    refine ⟨?_, fun w hw => ?_, hm⟩
    · simpa using hC w₀
    · simpa [Function.update_of_ne hw] using hC w
  · rintro ⟨h0, hrest, hm⟩
    refine ⟨fun w => ?_, hm⟩
    by_cases hw : w = w₀
    · subst hw
      simpa using h0
    · simpa [Function.update_of_ne hw] using hrest w hw

omit [IsScalarTower E K A] in
/-- Shrinking `C₀` shrinks `K_p`. -/
theorem SecondKindInvolution.distinguishedLevel_mono (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    {C₀ C₁ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))}
    (h : C₀.subgroup ≤ C₁.subgroup) :
    (σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀).subgroup ≤
      (σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₁).subgroup := by
  intro g hg
  rw [SecondKindInvolution.mem_distinguishedLevel] at hg ⊢
  exact ⟨h hg.1, hg.2⟩

open Classical in
omit [IsTotallyComplex K] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
  [IsScalarTower E K A] in
/-- Harris's local levels for `K(N)_p` are the maximal compact levels updated by the
congruence level at `w₀`. -/
theorem harrisLocalLevels_eq_update
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    haveI := moduleFinite_of_rat (K := K) (A := A)
    harrisLocalLevels A ι v 𝔭 hdiv w₀ r hr0 hr =
      Function.update (fun w => placeMaximalCompactLevel A w.1 (hdiv w)) w₀
        (placeCongruenceLevel A w₀.1 (hdiv w₀) r hr0 hr) := by
  funext w
  by_cases hw : w = w₀
  · subst hw
    simp [harrisLocalLevels]
  · simp [harrisLocalLevels, hw]

omit [IsScalarTower E K A] in
/-- Harris's `K(N)_p` is the level `K_p` of (4.1) with `C_v` the congruence level and
`C^(j)` the maximal compact levels. -/
theorem SecondKindInvolution.harrisLevel_eq_distinguishedLevel (σ : SecondKindInvolution E K A)
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    haveI := moduleFinite_of_rat (K := K) (A := A)
    σ.harrisLevel ι v 𝔭 h𝔭 hdiv w₀ r hr0 hr =
      σ.distinguishedLevel ι v 𝔭 h𝔭 (fun w => placeMaximalCompactLevel A w.1 (hdiv w)) w₀
        (placeCongruenceLevel A w₀.1 (hdiv w₀) r hr0 hr) := by
  rw [SecondKindInvolution.harrisLevel, SecondKindInvolution.distinguishedLevel,
    harrisLocalLevels_eq_update]

open Classical in
/-- The point of `GG(ℚ_v)` with component `h` at `w₀`, component `1` at the other places and
multiplier `1`. -/
def SecondKindInvolution.distinguishedPoint (σ : SecondKindInvolution E K A)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K) →*
      σ.rationalInvolution.Points (FiniteCompletion ℚ v) :=
  letI := ι.toAlgebra
  (σ.splitPlacePoints ι v 𝔭 h𝔭).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp
      (MonoidHom.mulSingle (fun w : FinitePlacesAbove K 𝔭.1 => (w.1.adicCompletion K ⊗[K] A)ˣ)
        w₀))

open Classical in
omit [IsScalarTower E K A] [Module.Finite ℚ A] [IsScalarTower ℚ K A] in
theorem SecondKindInvolution.splitPlacePoints_distinguishedPoint
    (σ : SecondKindInvolution E K A) (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    (h : ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K)) :
    σ.splitPlacePoints ι v 𝔭 h𝔭 (σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ h) =
      (Pi.mulSingle w₀ h, 1) := by
  simp [SecondKindInvolution.distinguishedPoint]
  rfl

open Classical in
omit [IsScalarTower E K A] in
/-- Conjugating by the point of `h` conjugates the component at `w₀` by `h` and leaves the
other components and the multiplier unchanged; hence it maps `K_p` for `C₀` into `K_p` for
`C₁` whenever `h⁻¹ C₀ h ⊆ C₁`. -/
theorem SecondKindInvolution.distinguishedPoint_conj_mem (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    {C₀ C₁ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))}
    (h : ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))
    (hh : ∀ k, k ∈ C₀.subgroup → h⁻¹ * k * h ∈ C₁.subgroup)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v))
    (hg : g ∈ (σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀).subgroup) :
    (σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ h)⁻¹ * g * σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ h ∈
      (σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₁).subgroup := by
  rw [SecondKindInvolution.mem_distinguishedLevel] at hg ⊢
  obtain ⟨h0, hrest, hm⟩ := hg
  have key : σ.splitPlacePoints ι v 𝔭 h𝔭
      ((σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ h)⁻¹ * g * σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ h) =
        (Pi.mulSingle w₀ h, 1)⁻¹ * σ.splitPlacePoints ι v 𝔭 h𝔭 g * (Pi.mulSingle w₀ h, 1) := by
    rw [map_mul, map_mul, map_inv, SecondKindInvolution.splitPlacePoints_distinguishedPoint]
  have e₀ := Pi.mulSingle_eq_same
    (M := fun w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) =>
      (w.1.adicCompletion K ⊗[K] A)ˣ) w₀ h
  refine ⟨?_, fun w hw => ?_, ?_⟩
  · rw [key]
    simp only [Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, e₀]
    exact hh _ h0
  · have e := Pi.mulSingle_eq_of_ne
      (M := fun w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) =>
        (w.1.adicCompletion K ⊗[K] A)ˣ) hw h
    rw [key]
    simp only [Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, e, inv_one, one_mul,
      mul_one]
    exact hrest w hw
  · rw [← σ.splitPlacePoints_snd ι v 𝔭 h𝔭, key]
    simp only [Prod.snd_mul, Prod.snd_inv, inv_one, one_mul, mul_one]
    rw [σ.splitPlacePoints_snd ι v 𝔭 h𝔭]
    exact hm

/-- Harris's `K_p` as `C_v` varies, with the fixed levels `C w` at the other places: a functor
from the levels of `(K_{w₀} ⊗[K] A)ˣ` to the levels of `GG(ℚ_v)`. An arrow given by `h`
(with `h⁻¹ C₀ h ⊆ C₁`) goes to the arrow given by the point with component `h` at `w₀`. -/
def SecondKindInvolution.distinguishedLevelFunctor (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K)) ⥤
      CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ v)) where
  obj C₀ := σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀
  map f :=
    ⟨σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ f.element, fun g hg =>
      σ.distinguishedPoint_conj_mem ι v 𝔭 h𝔭 C w₀ f.element f.respects g hg⟩
  map_id _ := CompactOpenLevel.Arrow.ext (map_one _)
  map_comp _ _ := CompactOpenLevel.Arrow.ext (map_mul _ _ _)

omit [IsScalarTower E K A] in
@[simp]
theorem SecondKindInvolution.distinguishedLevelFunctor_obj (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    (C₀ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))) :
    (σ.distinguishedLevelFunctor ι v 𝔭 h𝔭 C w₀).obj C₀ =
      σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀ := rfl

omit [IsScalarTower E K A] in
@[simp]
theorem SecondKindInvolution.distinguishedLevelFunctor_map_element
    (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)
    {C₀ C₁ : CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w₀.1.adicCompletion K))}
    (f : C₀ ⟶ C₁) :
    ((σ.distinguishedLevelFunctor ι v 𝔭 h𝔭 C w₀).map f).element =
      σ.distinguishedPoint ι v 𝔭 h𝔭 w₀ f.element := rfl

end Harris

end Langlands.Shimura
