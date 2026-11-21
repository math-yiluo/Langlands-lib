import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct
import Langlands.Global.RankinSelberg.UnequalKernelLocalPoint

/-! # Prescribed archimedean factors for the infinite Whittaker residual -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Langlands.Automorphic InfinitePlaceFamily
open CompletionPadic FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open Langlands.ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}
local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

private theorem map_padGL {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') {m n : ℕ} (h : m ≤ n) (g : Langlands.GeneralLinear m R) :
    Matrix.GeneralLinearGroup.map f (padGL h g) = padGL h (Matrix.GeneralLinearGroup.map f g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change f ((padGL h g).val i j) = (padGL h (Matrix.GeneralLinearGroup.map f g)).val i j
  rw [Unfolding.padGL_apply, Unfolding.padGL_apply]
  split_ifs <;> first | rfl | simp

/-- Real components commute with the diagonal inclusion used by the unequal-rank integral. -/
theorem realComponent_pad {m n : ℕ} (h : m ≤ n) (v : RP) (g : Points F m) :
    realComponent F n v (pad F h g) = padGL h (realComponent F m v g) := by
  let f := (Pi.evalRingHom (fun _ : RP => ℝ) v).comp (RingHom.fst (RP → ℝ) (CP → ℂ))
  let e := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
  unfold realComponent archimedeanComponent
  rw [UnequalAnalytic.adelicEquiv_pad, infinite_padGL]
  change Matrix.GeneralLinearGroup.map f
    (Matrix.GeneralLinearGroup.map e (padGL h (AdelicGL.infinite F m (E m g)))) = _
  rw [map_padGL, map_padGL]
  rfl

/-- Complex components commute with the same diagonal inclusion. -/
theorem complexComponent_pad {m n : ℕ} (h : m ≤ n) (w : CP) (g : Points F m) :
    complexComponent F n w (pad F h g) = padGL h (complexComponent F m w g) := by
  let f := (Pi.evalRingHom (fun _ : CP => ℂ) w).comp (RingHom.snd (RP → ℝ) (CP → ℂ))
  let e := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
  unfold complexComponent archimedeanComponent
  rw [UnequalAnalytic.adelicEquiv_pad, infinite_padGL]
  change Matrix.GeneralLinearGroup.map f
    (Matrix.GeneralLinearGroup.map e (padGL h (AdelicGL.infinite F m (E m g)))) = _
  rw [map_padGL, map_padGL]
  rfl

private theorem adelicEquiv_infinitePoint {n : ℕ} (S : Finset (FinitePlace F)) (g : Points F (n + 1)) :
    E (n + 1) (infinitePoint S g) = AdelicGL.ofInfinite F (n + 1)
      (AdelicGL.infinite F (n + 1) (E (n + 1) g)) := by
  let m := n + 1
  let z := (UnipotentClass.adelicSplit F m S).symm g
  have he : E m g = AdelicGL.pair F m ((UnipotentClass.archSplit F m).symm z.1)
      ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm z.2) := by
    rw [← UnipotentClass.adelicEquiv_adelicSplit F m S z]
    exact congrArg (E m) ((UnipotentClass.adelicSplit F m S).apply_symm_apply g).symm
  rw [infinitePoint, UnipotentClass.adelicEquiv_adelicSplit, he, AdelicGL.infinite_pair]
  change AdelicGL.pair F m ((UnipotentClass.archSplit F m).symm z.1)
      ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm (1 : UnipotentClass.LocalGL F m S ×
        UnipotentClass.AwayGL F m S)) = _
  rw [map_one]
  rfl

/-- Taking the infinite component with all finite components one commutes with padding. -/
theorem pad_infinitePoint {m n : ℕ} (h : m + 1 ≤ n + 1) (S : Finset (FinitePlace F))
    (g : Points F (m + 1)) :
    pad F h (infinitePoint S g) = infinitePoint S (pad F h g) := by
  apply (E (n + 1)).injective
  rw [UnequalAnalytic.adelicEquiv_pad, adelicEquiv_infinitePoint, adelicEquiv_infinitePoint,
    UnequalAnalytic.adelicEquiv_pad]
  apply adelicGL_ext_infinite_finite
  · rw [infinite_padGL, AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofInfinite, infinite_padGL]
  · rw [finite_padGL, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofInfinite, map_one]

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {hP : HasIrreducibleAdmissibleComponents P}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {S : Finset (FinitePlace F)}
  {hPS : P.exceptional ⊆ S}

/-- A joint infinite residual is the product of the specified real and complex functions. -/
def HasPrescribedInfiniteWhittakerProduct (U : Points F (r + 1) → ℂ) (κ : ℂ)
    (WR : RP → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (WC : CP → Langlands.GeneralLinear (r + 1) ℂ → ℂ) : Prop :=
  ∀ g, U g = κ * ((∏ v, WR v (realComponent F (r + 1) v g)) *
    ∏ w, WC w (complexComponent F (r + 1) w g))

/-- Local functions in the supplied slice model ranges can be realized simultaneously
by one infinite pure tensor, with the prescribed normalized finite references. -/
theorem exists_prescribed_infiniteResidual_product
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (M : ModelData P hP ψ.complex)
    (WR : RP → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (WC : CP → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (hR : ∀ v, WR v ∈ LinearMap.range (M.model (.inl v)))
    (hC : ∀ w, WC w ∈ LinearMap.range (M.model (.inr w))) :
    ∃ (b : ∀ i : Index F, T.placeDensityModels.subspace i) (κ : ℂ), κ ≠ 0 ∧
      HasPrescribedInfiniteWhittakerProduct
        (infiniteResidual S P hP hPS ψ.complex a₀ (PiTensorProduct.tprod ℂ b)) κ WR WC := by
  choose bR hbR using fun v => LinearMap.mem_range.mp (hR v)
  choose bC hbC using fun w => LinearMap.mem_range.mp (hC w)
  let b (i : Index F) : T.placeDensityModels.subspace i := match i with
    | .inl v => bR v
    | .inr w => bC w
  obtain ⟨_, κ, hκ, _, _, hprod⟩ :=
    exists_normalized_product (P := P) (hP := hP) ψ hψ S hPS hS ψv hψv ℓ a₀ ha₀ M
  refine ⟨b, κ, hκ, fun g => (hprod b g).trans ?_⟩
  apply congrArg (fun z : ℂ => κ * z)
  let f (i : Index F) := M.model i (b i) (placeComponents (r + 1) g i)
  change (∏ i, f i) = _
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (fun x y : ℂ => x * y)
    (Finset.prod_congr rfl (fun v _ => congrFun (hbR v) (realComponent F (r + 1) v g)))
    (Finset.prod_congr rfl (fun w _ => congrFun (hbC w) (complexComponent F (r + 1) w g)))

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
