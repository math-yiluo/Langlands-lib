import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.Global.AdelicConvolutionFiniteModel
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Global.AdelicHaarUnimodularityProof

/-! # Convolution equations under infinite compact conjugation -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj ContDiff Manifold

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G

variable (a : InfiniteAdelicGroupPoints F G)

local notation "t" => ofInfinite F G a
local notation "B" => MulAut.conj ((ofInfinite F G a)⁻¹)

private theorem apply_infiniteConjugation (x : A) : B x = t⁻¹ * x * t := by
  change t⁻¹ * x * (t⁻¹)⁻¹ = t⁻¹ * x * t
  rw [inv_inv]

private theorem infiniteConjugation_ofInfinite (x : A∞) :
    B (ofInfinite F G x) = ofInfinite F G ((MulAut.conj a⁻¹) x) := by
  rw [apply_infiniteConjugation]
  change t⁻¹ * ofInfinite F G x * t = ofInfinite F G (a⁻¹ * x * (a⁻¹)⁻¹)
  simp only [inv_inv, map_mul, map_inv]

private theorem infiniteConjugation_ofFinite (x : A_f) : B (ofFinite F G x) = ofFinite F G x := by
  rw [apply_infiniteConjugation, mul_assoc, ← (factors_commute F G a x).eq,
    inv_mul_cancel_left]

/-- Conjugation by an infinite adelic point leaves every finite coordinate unchanged. -/
theorem finite_infiniteConjugation (x : A) : finite F G (B x) = finite F G x := by
  rw [apply_infiniteConjugation]
  simp only [map_mul, map_inv, finite_ofInfinite, inv_one, one_mul, mul_one]

/-- Conjugating by an infinite adelic point preserves smooth adelic test functions. -/
theorem isAdelicTestFunction_comp_infiniteConjugation {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (fun x => h (B x)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let e : A ≃ₜ A := (Homeomorph.mulLeft t⁻¹).trans (Homeomorph.mulRight t)
  have he (x : A) : e x = B x := (apply_infiniteConjugation a x).symm
  obtain ⟨L, hLopen, hL⟩ := hh.1.2.2
  obtain ⟨U, hUopen, hU⟩ := hh.2.2
  have hcont : Continuous (fun x : A => B x) := by
    rw [← funext he]
    exact e.continuous
  have hsupp : HasCompactSupport (fun x => h (B x)) := by
    simpa only [Function.comp_def, he] using hh.2.1.comp_homeomorph e
  refine ⟨⟨hh.1.1.comp hcont, ?_, L, hLopen, ?_⟩, hsupp, U, hUopen, ?_⟩
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
    have hslice := (isPlotSmooth_iff_contMDiff F G hsmooth _).1 (hh.1.2.1 b)
    have hmul : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d) ∞
        (fun x : A∞ => a⁻¹ * x * a) := (contMDiff_const.mul contMDiff_id).mul contMDiff_const
    apply (hslice.comp hmul).congr
    intro x
    change h (B (pair F G x b)) = h (pair F G (a⁻¹ * x * a) b)
    rw [apply_infiniteConjugation, ← map_inv (ofInfinite F G) a]
    simp only [ofInfinite_eq_pair, pair_mul, one_mul, mul_one]
  · intro l hl x
    change h (B (x * ofFinite F G l)) = h (B x)
    rw [map_mul, infiniteConjugation_ofFinite]
    exact hL l hl (B x)
  · intro l hl x
    change h (B (ofFinite F G l * x)) = h (B x)
    rw [map_mul, infiniteConjugation_ofFinite]
    exact hU l hl (B x)

/-- The compact translate spans pull back along infinite conjugation. -/
theorem isInfiniteSubgroupFiniteFunction_comp_infiniteConjugation
    (C : Subgroup A∞) {h : A → ℂ}
    (hh : IsInfiniteSubgroupFiniteFunction F G (C.map (MulAut.conj a⁻¹).toMonoidHom) h) :
    IsInfiniteSubgroupFiniteFunction F G C (fun x => h (B x)) := by
  let C' := C.map (MulAut.conj a⁻¹).toMonoidHom
  let S := Submodule.span ℂ (Set.range fun k : C' => fun x : A => h (x * ofInfinite F G k.val))
  let T : (A → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ B
  let : FiniteDimensional ℂ S := hh
  apply Submodule.finiteDimensional_of_le (S₂ := S.map T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let k' : C' := ⟨MulAut.conj a⁻¹ k.val, ⟨k.val, k.property, rfl⟩⟩
  refine ⟨fun x => h (x * ofInfinite F G k'.val), Submodule.subset_span ⟨k', rfl⟩, ?_⟩
  funext x
  change h (B x * ofInfinite F G k'.val) = h (B (x * ofInfinite F G k.val))
  rw [map_mul, infiniteConjugation_ofInfinite]

/-- Taking the infinite part commutes with conjugation by an inverse infinite point. -/
theorem comap_ofInfinite_conjugate (K : Subgroup A) :
    (K.map (B).toMonoidHom).comap (ofInfinite F G).toMonoidHom =
      (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom := by
  ext k
  change ofInfinite F G k ∈ K.map (B).toMonoidHom ↔
    k ∈ (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom
  simp only [Subgroup.mem_map_equiv]
  change (B).symm (ofInfinite F G k) ∈ K ↔
    ofInfinite F G ((MulAut.conj a⁻¹).symm k) ∈ K
  have heq : (B).symm (ofInfinite F G k) = ofInfinite F G ((MulAut.conj a⁻¹).symm k) := by
    apply (B).injective
    rw [MulEquiv.apply_symm_apply, infiniteConjugation_ofInfinite, MulEquiv.apply_symm_apply]
  rw [heq]

variable [LocallyOfFiniteType G.X.hom]

private theorem rightConvolution_comp_infiniteConjugation
    (hG : IsConnectedReductive G) (h f : A → ℂ) (x : A) :
    rightConvolution F G h f (x * t) =
      rightConvolution F G (fun y => h (B y)) (fun y => f (y * t)) x := by
  let measure : Measure A := Measure.haar
  let : measure.IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  let g (y : A) := h y * f (x * t * y)
  have hSub : (∫ y, g (B y) ∂measure) = ∫ y, g y ∂measure := by
    conv_lhs => simp only [apply_infiniteConjugation]
    rw [integral_mul_left_eq_self (fun y => g (y * t)) t⁻¹,
      integral_mul_right_eq_self g t]
  change (∫ y, g y ∂measure) = ∫ y, h (B y) * f (x * y * t) ∂measure
  rw [← hSub]
  congr 1
  funext y
  dsimp only [g]
  rw [apply_infiniteConjugation]
  congr 2
  group

/-- Right translating a parameterized family transports its uniform convolution equations
by conjugating every kernel, with the same scalar coefficients. -/
theorem hasConvolutionEquationAt_infiniteRightTranslate {d n : ℕ}
    (hG : IsConnectedReductive G) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (C : Subgroup A∞) (f : (Fin n → ℂ) → A → ℂ) (s₀ : Fin n → ℂ)
    (heq : HasConvolutionEquationAt (C.map (MulAut.conj a⁻¹).toMonoidHom) f s₀) :
    HasConvolutionEquationAt C (fun s x => f s (x * t)) s₀ := by
  obtain ⟨m, h, b, c, hh, hb, hc, hc₀, hconvolution⟩ := heq
  refine ⟨m, fun j x => h j (B x), b, c, fun j => ?_, hb, hc, hc₀, fun s x => ?_⟩
  · refine ⟨isAdelicTestFunction_comp_infiniteConjugation a hsmooth (hh j).1,
      isInfiniteSubgroupFiniteFunction_comp_infiniteConjugation a C (hh j).2.1, ?_⟩
    have he : (fun x : A => h j (B x⁻¹)) = fun x => h j (B x)⁻¹ :=
      funext fun x => congrArg (h j) (map_inv (B) x)
    rw [he]
    exact isInfiniteSubgroupFiniteFunction_comp_infiniteConjugation a C
      (h := fun x => h j x⁻¹) (hh j).2.2
  · calc
      _ = ∑ j, b j s * rightConvolution F G (h j) (f s) (x * t) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (b j s * ·) (rightConvolution_comp_infiniteConjugation a hG (h j) (f s) x).symm
      _ = _ := hconvolution s (x * t)

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Changing the Iwasawa compact by infinite conjugation and translating the
inducing function transfers the entire-coefficient convolution equation. -/
theorem IsIwasawaCompact.hasConvolutionEquationAt_of_infiniteConjugation {d n : ℕ}
    (hG : IsConnectedReductive G) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hK' : IsIwasawaCompact p (K.map (B).toMonoidHom))
    (f : A → ℂ) (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ)
    (heq : HasConvolutionEquationAt ((K.map (B).toMonoidHom).comap (ofInfinite F G).toMonoidHom)
      (fun s => hK'.parameterTwist f (e s)) s₀) :
    HasConvolutionEquationAt (K.comap (ofInfinite F G).toMonoidHom)
      (fun s => hK.parameterTwist (fun x => f (x * t)) (e s)) s₀ := by
  rw [comap_ofInfinite_conjugate a] at heq
  obtain ⟨m, h, b, c, hh, hb, hc, hc₀, hconv⟩ := hasConvolutionEquationAt_infiniteRightTranslate
    a hG hsmooth _ _ s₀ heq
  refine ⟨m, h, b, c, hh, hb, hc, hc₀, fun s x => ?_⟩
  let v := hK.parameterTwist (fun x => f (x * t)) (e s)
  let scale := hK'.heightPower (e s) t
  have ht (y : A) : hK'.parameterTwist f (e s) (y * t) = v y * scale := by
    unfold v scale IsIwasawaCompact.parameterTwist
    rw [hK.heightPower_mul_conjInv t hK', mul_assoc]
  have hconv' (j : Fin m) :
      rightConvolution F G (h j) (fun y => hK'.parameterTwist f (e s) (y * t)) x =
        rightConvolution F G (h j) v x * scale := by
    unfold rightConvolution
    simp_rw [ht, ← mul_assoc, integral_mul_const]
  have he := hconv s x
  change ∑ j, b j s * rightConvolution F G (h j)
      (fun y => hK'.parameterTwist f (e s) (y * t)) x =
    c s * hK'.parameterTwist f (e s) (x * t) at he
  simp_rw [hconv', ht, ← mul_assoc, ← Finset.sum_mul] at he
  exact (mul_right_cancel₀ (Complex.exp_ne_zero _) he)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme

/-- With an infinite adelic conjugation of the Iwasawa compact, the uniform equation
for the twists transfers to infinite right translates of the inducing function. -/
def HarishChandraCompactConjugationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (a : InfiniteAdelicGroupPoints F G),
    let t := ofInfinite F G a
    let K' := K.map (MulAut.conj t⁻¹).toMonoidHom
    ∀ (hK' : IsIwasawaCompact p K'), IsConnectedReductive G →
      ∀ {d n : ℕ}, SmoothOfRelativeDimension d G.X.hom →
        ∀ (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
          (s₀ : Fin n → ℂ) (f : AdelicGroupPoints F G → ℂ),
          HasConvolutionEquationAt (K'.comap (ofInfinite F G).toMonoidHom)
            (fun s => hK'.parameterTwist f (e s)) s₀ →
          HasConvolutionEquationAt (K.comap (ofInfinite F G).toMonoidHom)
            (fun s => hK.parameterTwist (fun x => f (x * t)) (e s)) s₀

theorem harishChandraCompactConjugation : HarishChandraCompactConjugationStatement.{u} := by
  intro F _ _ G P _ _ _ p _ K hK a t K' hK' hG d n hsmooth e s₀ f heq
  exact hK.hasConvolutionEquationAt_of_infiniteConjugation a hG hsmooth hK' f e s₀ heq

end Langlands.Global
