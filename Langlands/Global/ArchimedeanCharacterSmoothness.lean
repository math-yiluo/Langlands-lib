import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Global.ArchimedeanGL
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness of the archimedean determinant factor of a Hecke character

A continuous character `ψ` of the units of a commutative real Banach algebra `A` is smooth.
Its composite with the exponential is a continuous homomorphism from `(A, +)` to `ℂˣ`;
lifting through the covering `exp : ℂ → ℂˣ` and using that continuous additive maps are
real-linear gives `ψ (exp x) = exp (L x)` for a continuous real-linear `L`. Near `1` the
exponential has a smooth local inverse, so `ψ` is smooth near `1`, and translation by units
moves this to every unit.

For a number field, the archimedean component of a Hecke character `χ` is such a character
of the units of the mixed space. The determinant is a polynomial in the matrix entries, so
`x ↦ χ(det x)` is smooth on the real archimedean matrix group, and on every slice
`x ↦ χ(det (x, b))` of the adelic matrix group. No finite-order hypothesis is used.
-/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator Topology
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

/-- A continuous multiplicative function on a real normed space with values in `ℂˣ` is the
exponential of a continuous real-linear functional. -/
theorem exists_continuousLinearMap_exp_of_continuous_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℂ) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) (hne : ∀ x, f x ≠ 0) :
    ∃ L : V →L[ℝ] ℂ, ∀ x, f x = Complex.exp (L x) := by
  let F : C(V, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨f x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, hg, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0
    (by apply Subtype.ext; simpa [F] using h0.symm)
  have hg0 : g 0 = 0 := hg.1
  have hgexp (x : V) : Complex.exp (g x) = f x :=
    congrArg Subtype.val (congrFun hg.2 x)
  have hadd (x y : V) : g (x + y) = g x + g y := by
    have he : (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
        (fun p : V × V => g (p.1 + p.2)) =
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
        (fun p : V × V => g p.1 + g p.2) := by
      funext p
      apply Subtype.ext
      simp only [Function.comp_apply, Complex.exp_add, hgexp, ha]
    have h := Complex.isCoveringMap_exp.eq_of_comp_eq
      (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))
      he (0, 0) (by simp [hg0])
    exact congrFun h (x, y)
  refine ⟨(AddMonoidHom.mk' g hadd).toRealLinearMap g.continuous, fun x => ?_⟩
  rw [← hgexp]
  rfl

section UnitsCharacter

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private theorem exp_add_comm (x y : A) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact NormedSpace.exp_add

private theorem exp_continuous' : Continuous (NormedSpace.exp : A → A) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact NormedSpace.exp_continuous

/-- The exponential of an element of a commutative real Banach algebra, as a unit. -/
def banachExpUnit (x : A) : Aˣ where
  val := NormedSpace.exp x
  inv := NormedSpace.exp (-x)
  val_inv := by rw [← exp_add_comm, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by rw [← exp_add_comm, neg_add_cancel, NormedSpace.exp_zero]

@[simp]
theorem coe_banachExpUnit (x : A) : (banachExpUnit x : A) = NormedSpace.exp x := rfl

theorem banachExpUnit_zero : banachExpUnit (0 : A) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

theorem banachExpUnit_add (x y : A) : banachExpUnit (x + y) = banachExpUnit x * banachExpUnit y := by
  apply Units.ext
  exact exp_add_comm x y

theorem continuous_banachExpUnit : Continuous (banachExpUnit : A → Aˣ) :=
  Units.continuous_iff.mpr ⟨exp_continuous', exp_continuous'.comp continuous_neg⟩

variable (ψ : Aˣ →ₜ* ℂˣ)

/-- The values of a continuous character of the units, extended by zero to the algebra. -/
def unitsCharacterExtension (a : A) : ℂ :=
  if h : IsUnit a then (ψ h.unit : ℂ) else 0

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
@[simp]
theorem unitsCharacterExtension_unit (u : Aˣ) :
    unitsCharacterExtension ψ (u : A) = ψ u := by
  simp [unitsCharacterExtension]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem unitsCharacterExtension_mul_unit (u : Aˣ) (a : A) :
    unitsCharacterExtension ψ ((u : A) * a) = ψ u * unitsCharacterExtension ψ a := by
  by_cases h : IsUnit a
  · obtain ⟨a, rfl⟩ := h
    rw [← Units.val_mul, unitsCharacterExtension_unit, unitsCharacterExtension_unit, map_mul,
      Units.val_mul]
  · have h' : ¬ IsUnit ((u : A) * a) := by
      rwa [Units.isUnit_units_mul]
    simp [unitsCharacterExtension, h, h']

/-- The character composed with the exponential is the exponential of a real-linear form. -/
theorem exists_unitsCharacter_exp :
    ∃ L : A →L[ℝ] ℂ, ∀ x, (ψ (banachExpUnit x) : ℂ) = Complex.exp (L x) :=
  exists_continuousLinearMap_exp_of_continuous_add (fun x => (ψ (banachExpUnit x) : ℂ))
    (Units.continuous_val.comp (ψ.continuous.comp continuous_banachExpUnit))
    (by simp [banachExpUnit_zero])
    (fun x y => by rw [banachExpUnit_add, map_mul, Units.val_mul])
    (fun x => (ψ _).ne_zero)

theorem contDiffAt_unitsCharacterExtension_one :
    ContDiffAt ℝ ∞ (unitsCharacterExtension ψ) 1 := by
  obtain ⟨L, hL⟩ := exists_unitsCharacter_exp ψ
  have hexp : ContDiffAt ℝ ∞ (NormedSpace.exp : A → A) 0 :=
    (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (0 : A)
      (by simp [NormedSpace.expSeries_radius_eq_top])).contDiffAt
  have hder : HasFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 :=
    hasFDerivAt_exp_zero (𝕂 := ℝ)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv := hexp.to_localInverse hder hn
  rw [NormedSpace.exp_zero] at hinv
  have hright : ∀ᶠ y in 𝓝 (1 : A),
      NormedSpace.exp (hexp.localInverse hder hn y) = y := by
    have h := (hexp.hasStrictFDerivAt' hder hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at h
    exact h
  have heq : unitsCharacterExtension ψ =ᶠ[𝓝 1]
      fun y => Complex.exp (L (hexp.localInverse hder hn y)) := by
    filter_upwards [hright] with y hy
    have hy' : (banachExpUnit (hexp.localInverse hder hn y) : A) = y := hy
    rw [← hy', unitsCharacterExtension_unit, hL, hy']
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt).comp _
    (L.contDiff.contDiffAt.comp _ hinv)

/-- A continuous character of the units of a commutative real Banach algebra is smooth at
every unit. -/
theorem contDiffAt_unitsCharacterExtension (u : Aˣ) :
    ContDiffAt ℝ ∞ (unitsCharacterExtension ψ) (u : A) := by
  have hlin : ContDiffAt ℝ ∞ (fun a : A => ((u⁻¹ : Aˣ) : A) * a) (u : A) :=
    ((ContinuousLinearMap.mul ℝ A) ((u⁻¹ : Aˣ) : A)).contDiff.contDiffAt
  have hcomp : ContDiffAt ℝ ∞
      (fun a => unitsCharacterExtension ψ (((u⁻¹ : Aˣ) : A) * a)) (u : A) := by
    refine ContDiffAt.comp (g := unitsCharacterExtension ψ) (u : A) ?_ hlin
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact contDiffAt_unitsCharacterExtension_one ψ
  have heq : unitsCharacterExtension ψ =
      fun a => (ψ u : ℂ) * unitsCharacterExtension ψ (((u⁻¹ : Aˣ) : A) * a) := by
    funext a
    rw [unitsCharacterExtension_mul_unit, ← mul_assoc, ← Units.val_mul, ← map_mul,
      mul_inv_cancel, map_one, Units.val_one, one_mul]
  rw [heq]
  exact contDiffAt_const.mul hcomp

end UnitsCharacter

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The determinant of real archimedean matrices is smooth. -/
theorem contDiff_archimedeanDet :
    ContDiff ℝ ∞ (fun M : ArchimedeanMatrix K n => M.det) := by
  have hentry : ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun M : ArchimedeanMatrix K n => M i j) := by
    intro i j
    let e : ArchimedeanMatrix K n →ₗ[ℝ] mixedEmbedding.mixedSpace K :=
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap e).contDiff
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (contDiff_prod fun i _ => hentry (σ i) i)

namespace AdelicGL

theorem pair_eq_ofInfinite_mul_ofFinite (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    pair K n a b = ofInfinite K n a * ofFinite K n b := by
  apply (split K n).injective
  rw [map_mul]
  change (infinite K n (pair K n a b), finite K n (pair K n a b)) =
    (split K n) ((split K n).symm (a, 1)) * (split K n) ((split K n).symm (1, b))
  rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply,
    infinite_pair, finite_pair]
  simp

theorem determinant_ofInfinite (a : InfiniteAdelicGL K n) :
    determinant K n (ofInfinite K n a) =
      infiniteIdelesInclusion K (Matrix.GeneralLinearGroup.det a) := by
  apply Units.ext
  apply Prod.ext
  · change RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
        (ofInfinite K n a).val.det = a.val.det
    rw [RingHom.map_det]
    rfl
  · change RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
        (ofInfinite K n a).val.det = 1
    rw [RingHom.map_det]
    change (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)).det = 1
    exact Matrix.det_one

end AdelicGL

namespace HeckeCharacter

variable {K}

/-- The archimedean component of a Hecke character on the units of the mixed space. -/
def mixedCharacter (χ : HeckeCharacter K) : (mixedEmbedding.mixedSpace K)ˣ →ₜ* ℂˣ :=
  χ.atInfinity.comp
    { toMonoidHom :=
        Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.toMonoidHom
      continuous_toFun := (continuous_infiniteAdeleCoordinates_symm K).units_map _ }

theorem adelicDeterminant_ofInfinite_coordinates (χ : HeckeCharacter K)
    (x : ArchimedeanGL K n) :
    χ.adelicDeterminant n (AdelicGL.ofInfinite K n ((archimedeanGLCoordinates K n).symm x)) =
      χ.mixedCharacter (Matrix.GeneralLinearGroup.det x) := by
  change χ.onIdeles (AdelicGL.determinant K n (AdelicGL.ofInfinite K n _)) = _
  rw [AdelicGL.determinant_ofInfinite]
  change χ.onIdeles (infiniteIdelesInclusion K _) = χ.onIdeles (infiniteIdelesInclusion K _)
  congr 2
  exact Matrix.GeneralLinearGroup.map_det _ _

/-- The archimedean determinant factor of every Hecke character is smooth. -/
theorem contMDiff_adelicDeterminant_ofInfinite (χ : HeckeCharacter K) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ (fun x : ArchimedeanGL K n =>
      (χ.adelicDeterminant n
        (AdelicGL.ofInfinite K n ((archimedeanGLCoordinates K n).symm x)) : ℂ)) := by
  intro x
  have h : ContDiffAt ℝ ∞
      (fun M : ArchimedeanMatrix K n => unitsCharacterExtension χ.mixedCharacter M.det)
      (x : ArchimedeanMatrix K n) := by
    have hd := contDiffAt_unitsCharacterExtension χ.mixedCharacter
      (Matrix.GeneralLinearGroup.det x)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    exact hd.comp _ (contDiff_archimedeanDet K n).contDiffAt
  have hc := h.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) x)
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, adelicDeterminant_ofInfinite_coordinates]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, unitsCharacterExtension_unit]

/-- On every slice of the adelic matrix group, the determinant factor of every Hecke
character is smooth in the archimedean variable. -/
theorem contMDiff_adelicDeterminant_pair (χ : HeckeCharacter K) (b : FiniteAdelicGL K n) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ (fun x : ArchimedeanGL K n =>
      (χ.adelicDeterminant n
        (AdelicGL.pair K n ((archimedeanGLCoordinates K n).symm x) b) : ℂ)) := by
  have h := (((ContinuousLinearMap.mul ℝ ℂ)
    (χ.adelicDeterminant n (AdelicGL.ofFinite K n b) : ℂ)).contDiff.contMDiff).comp
      (χ.contMDiff_adelicDeterminant_ofInfinite n)
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, ContinuousLinearMap.mul_apply',
    AdelicGL.pair_eq_ofInfinite_mul_ofFinite, map_mul, Units.val_mul]
  ring

end HeckeCharacter

end Langlands.Global
