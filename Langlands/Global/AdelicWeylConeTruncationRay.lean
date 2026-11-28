import Langlands.Global.AdelicRelativeConeFourierBoundary
import Langlands.Global.AdelicWeylConeCorootChart

/-! # The tested Weyl cone sum along a positive truncation ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Set
open scoped CategoryTheory.MonObj Classical ContDiff NNReal Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Langlands.Analysis ImaginaryAxis
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν)
  {n : ℕ} {Coord L : Type*} [Fintype Coord] [Fintype L]

local notation "Param" J:max => RealCharacterParameter F (fam.P J)
local notation "W" => relativeWeylGroup fam.i

variable (full : (Fin n → ℝ) ≃ₗ[ℝ] (RealCharacterParameter F (fam.P P)))
  (relative : (Coord → ℝ) ≃ₗ[ℝ] ↥(relativeParameterSpace (F := F) (fam.p P)))
  (spectral : Measure (Coord → ℝ))
  (Q : L → StandardIndex F G fam.i fam.ν) (a : L → normalizerPoints fam.i)
  (c : ∀ l, fam.M (Q l) ⟶ fam.M P) (π : ∀ l, fam.P (Q l) ⟶ fam.M (Q l))

local notation "Roots" l:max => fam.relativeSimpleRoots (Q l)
local notation "classOf" l:max => (QuotientGroup.mk (a l) : W)

/-- On a dense part of the full imaginary parameter space, the truncation functions
agree with the finite Weyl sum. The representatives and weights are holomorphic on
a neighborhood of that imaginary space for each sufficiently large ray index. -/
def IsWeylConeRayRepresentative
    (T₀ T : V fam.T) (freq : ∀ l, Param (Q l)) (p : ∀ l, MvPolynomial (Roots l) ℂ)
    (weight : L → (Fin n → ℂ) → ℂ) (representative : ℕ → (Fin n → ℂ) → ℂ) : Prop :=
  let z (l : L) : (Fin n → ℂ) → (Roots l → ℂ) :=
    fam.weylConeCorootValue P (Q l) full (c l) (π l) (freq l)
  let b (k : ℕ) (l : L) : Roots l → ℝ := fam.weightCoordinate (Q l) (T₀ + (k : ℝ) • T)
  ∀ᶠ k : ℕ in atTop, ∃ (U : Set (Fin n → ℂ)) (S : Set (Fin n → ℝ)),
    IsOpen U ∧ range imaginarySlice ⊆ U ∧ Dense S ∧
    DifferentiableOn ℂ (representative k) U ∧ (∀ l, DifferentiableOn ℂ (weight l) U) ∧
    ∀ x ∈ S, (∀ l α, z l (imaginarySlice x) α ≠ 0) ∧
      representative k (imaginarySlice x) =
        ∑ l, weight l (imaginarySlice x) * regularizedOrthantTerm (b k l) (p l)
          (z l (imaginarySlice x))

/-- The Weyl cone test limit in given relative spectral charts and Haar normalizations. -/
def HasWeylConeTruncationRayLimit
    (e : ∀ l, (Coord → ℝ) ≃L[ℝ] (Roots l → ℝ)) (C : L → ℝ≥0) : Prop :=
  ∀ (T₀ T : V fam.T) (freq : ∀ l, Param (Q l)) (p : ∀ l, MvPolynomial (Roots l) ℂ)
      (weight : L → (Fin n → ℂ) → ℂ) (representative : ℕ → (Fin n → ℂ) → ℂ),
      (∀ β ∈ simpleRelativeRoots fam.i fam.ν, 0 < eval fam.T β T) →
      fam.IsWeylConeRayRepresentative P full Q c π T₀ T freq p weight representative →
      ∀ f : (Coord → ℝ) → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        let onAxis : (Coord → ℝ) → (Fin n → ℂ) :=
          fun y => imaginarySlice (full.symm (relative y).val)
        let ξ (l : L) (α : Roots l) : ℝ :=
          realParameterPairing F (fam.P (Q l)) (freq l) (fam.relativeCoroot (Q l) α)
        let w (l : L) (y : Roots l → ℝ) : ℂ :=
          f ((e l).symm y) * weight l (onAxis ((e l).symm y))
        (∀ᶠ k : ℕ in atTop, Integrable (fun x => f x * representative k (onAxis x)) spectral) ∧
        Tendsto (fun (k : ℕ) => ∫ x, f x * representative k (onAxis x) ∂spectral) atTop
          (𝓝 (∑ l ∈ Finset.univ.filter (fun l => Q l = P ∧ classOf l = 1),
            ((C l : ℝ) : ℂ) * coordinatePolynomialPointEvaluation (p l) (ξ l) (w l)))

/-- The spectral test of a holomorphic finite Weyl cone sum converges along a strictly
dominant truncation ray. Its limit is the sum of local polynomial distributions for
the identity Weyl class at the inducing parabolic. -/
def WeylConeTruncationRayStatement : Prop :=
  ∀ [spectral.IsAddHaarMeasure],
  (∀ l, fam.l (Q l) ≫ π l = 𝟙 (fam.M (Q l))) →
  (∀ l, IsWeylConjugation (fam.p P) (fam.l P) (fam.p (Q l)) (fam.l (Q l)) (a l).val (c l)) →
  (∀ l, schemeWeylCharacterAction fam.i (classOf l)⁻¹ '' (Q l).val = P.val) →
  ∃ (e : ∀ l, (Coord → ℝ) ≃L[ℝ] (Roots l → ℝ)) (C : L → ℝ≥0),
    (∀ l x α, e l x α = realParameterPairing F (fam.P (Q l))
      (realWeylParameter (fam.l P) (c l) (π l) (relative x).val) (fam.relativeCoroot (Q l) α)) ∧
    (∀ l, 0 < C l) ∧ fam.HasWeylConeTruncationRayLimit P full relative spectral Q a c π e C

/-- The Weyl cone test limit with the pushforward identity for each spectral Haar factor. -/
theorem weylConeTruncationRay_withHaar [spectral.IsAddHaarMeasure]
    (hπ : ∀ l, fam.l (Q l) ≫ π l = 𝟙 (fam.M (Q l)))
    (hconj : ∀ l, IsWeylConjugation (fam.p P) (fam.l P) (fam.p (Q l)) (fam.l (Q l)) (a l).val (c l))
    (hmatch : ∀ l, schemeWeylCharacterAction fam.i (classOf l)⁻¹ '' (Q l).val = P.val) :
    ∃ (e : ∀ l, (Coord → ℝ) ≃L[ℝ] (Roots l → ℝ)) (C : L → ℝ≥0),
      (∀ l x α, e l x α = realParameterPairing F (fam.P (Q l))
        (realWeylParameter (fam.l P) (c l) (π l) (relative x).val) (fam.relativeCoroot (Q l) α)) ∧
      (∀ l, Measure.map (e l) spectral = C l • coordinateSpectralMeasure (Roots l)) ∧
      (∀ l, 0 < C l) ∧ fam.HasWeylConeTruncationRayLimit P full relative spectral Q a c π e C := by
  choose e he hchart using fun l =>
    fam.weylConeCorootChart P (Q l) full relative (a l) (c l) (π l) (hπ l) (hconj l)
  obtain ⟨C, hMap, hC, hBoundary⟩ := relativeConeFourierBoundary_withHaar spectral e
  refine ⟨e, C, he, hMap, hC, ?_⟩
  obtain ⟨Λ, hΛ⟩ := fam.exists_weylConeDisplacement P
  intro T₀ T freq p weight representative hT hReg f hf hfs onAxis ξ w
  let z (l : L) := fam.weylConeCorootValue P (Q l) full (c l) (π l) (freq l)
  let b (k : ℕ) (l : L) := fam.weightCoordinate (Q l) (T₀ + (k : ℝ) • T)
  let d (l : L) := fam.weylConeSlope (Q l) (classOf l)⁻¹ (fam.chamberEmbedding P Λ.val)
  let chart : ℝ × (Coord → ℝ) → (Fin n → ℂ) := fam.displacedRelativeSpectralChart P full relative Λ
  have hγzero (x : Coord → ℝ) : chart (0, x) = onAxis x :=
    fam.displacedRelativeSpectralChart_zero P full relative Λ x
  have hγaxis (x : Coord → ℝ) : chart (0, x) ∈ range imaginarySlice :=
    ⟨full.symm (relative x).val, (hγzero x).symm⟩
  have hd (l : L) := hΛ (Q l) (classOf l) (hmatch l)
  have hFourier : ∀ᶠ k in atTop,
      (∀ l, ContDiff ℝ ∞ (w l) ∧ HasCompactSupport (w l)) ∧
      Integrable (fun x => f x * representative k (onAxis x)) spectral ∧
      (∫ x, f x * representative k (onAxis x) ∂spectral) =
        ∑ l, ((C l : ℝ) : ℂ) * orthantSign (d l) *
          ∫ u in translatedOrientedOrthant (d l) (b k l),
            orthantPolynomialTest (coordinateSpectralMeasure (Roots l))
              (fun y => w l (y + ξ l)) (p l) u := by
    dsimp only [IsWeylConeRayRepresentative] at hReg
    filter_upwards [hReg] with k hk
    obtain ⟨U, S, hU, hAxis, hS, hRep, hWeight, hIdentity⟩ := hk
    have hz (l : L) (α : Roots l) : DifferentiableOn ℂ (fun y => z l y α) U :=
      (fam.differentiable_weylConeCorootValue P (Q l) full (c l) (π l) (freq l) α).differentiableOn
    have h := hBoundary (b k) d ξ p z weight (representative k) U S chart hU hAxis hS hRep
      hWeight hz hIdentity (fam.contDiff_displacedRelativeSpectralChart P full relative Λ)
      hγaxis (fun l => (hd l).1) (fun t x l => hchart l Λ (freq l) t x) f hf hfs
    simpa only [hγzero, w] using h
  obtain ⟨k, hw, _⟩ := hFourier.exists
  refine ⟨hFourier.mono (fun _ h => h.2.1), ?_⟩
  have hTerm (l : L) :
      Tendsto (fun k => ((C l : ℝ) : ℂ) * orthantSign (d l) *
        ∫ u in translatedOrientedOrthant (d l) (b k l),
          orthantPolynomialTest (coordinateSpectralMeasure (Roots l))
            (fun y => w l (y + ξ l)) (p l) u) atTop
        (𝓝 (if Q l = P ∧ classOf l = 1 then
          ((C l : ℝ) : ℂ) * coordinatePolynomialPointEvaluation (p l) (ξ l) (w l) else 0)) := by
    have hb (k : ℕ) :
        b k l = fam.weightCoordinate (Q l) T₀ + (k : ℝ) • fam.weightCoordinate (Q l) T := by
      funext α
      simp only [b, weightCoordinate, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    have h := translatedOrthant_compactTest_tendsto (d l) (fam.weightCoordinate (Q l) T₀)
      (fam.weightCoordinate (Q l) T) (ξ l) (hd l).1 (fam.weightCoordinate_pos_of_simple_pos (Q l) hT)
      (p l) (w l) (hw l).1 (hw l).2
    have hScaled := (tendsto_const_nhds (x := ((C l : ℝ) : ℂ) * orthantSign (d l))).mul h
    by_cases hp : Q l = P ∧ classOf l = 1
    · have hpos : ∀ α, 0 < d l α := (hd l).2.mpr hp
      have hsign : orthantSign (d l) = 1 := by simp [orthantSign, hpos]
      simpa only [hb, ite_eq_left hp, ite_eq_left hpos, hsign, mul_one] using hScaled
    · have hn : ¬ ∀ α, 0 < d l α := fun hpos => hp ((hd l).2.mp hpos)
      simpa only [hb, ite_eq_right hp, ite_eq_right hn, mul_zero] using hScaled
  rw [Finset.sum_filter]
  exact (tendsto_finsetSum Finset.univ (fun l _ => hTerm l)).congr'
    (hFourier.mono fun _ h => h.2.2.symm)

theorem weylConeTruncationRay :
    fam.WeylConeTruncationRayStatement P full relative spectral Q a c π := by
  intro _ hπ hconj hmatch
  obtain ⟨e, C, he, _, hC, h⟩ :=
    fam.weylConeTruncationRay_withHaar P full relative spectral Q a c π hπ hconj hmatch
  exact ⟨e, C, he, hC, h⟩

end Langlands.Global.StandardParabolicFamily
