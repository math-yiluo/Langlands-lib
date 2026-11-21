import Langlands.BaseChange.SatakeCharacter
import Langlands.BaseChange.SatakeTwoBlockConstantTerm

/-! Spherical base change on finite expansions of two-block constant terms. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.Correspondence Langlands.GeneralLinear Langlands.Unramified
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg

universe u v

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance constantTermBaseChangeFieldMeasurable (K : PadicField p) :
    MeasurableSpace K.Carrier := borel _
local instance constantTermBaseChangeFieldBorel (K : PadicField p) :
    BorelSpace K.Carrier := ⟨rfl⟩

private theorem sphericalHecke_eq_of_satakeTuple_eq (F : PadicField.{u} p) {r : ℕ}
    (f g : SphericalHeckeAlgebra F r)
    (h : ∀ (z : Fin (r + 1) → ℂˣ) (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ),
      IsSatakeCharacter F r (Eigenvalues.ofTuple z) ω → ω f = ω g) :
    f = g := by
  apply sub_eq_zero.mp ((satakeCharacter p F r).2 (f - g) ?_)
  intro s ω hω
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
  rw [map_sub, h z ω hω, sub_self]

private theorem sphericalGeneration_evalAt_apply (F : PadicField.{u} p) {r : ℕ}
    (x : GeneralLinear (r + 1) F.Carrier) (f : SphericalHeckeAlgebra F r) :
    SphericalGeneration.evalAt F x f = f x := rfl

set_option maxHeartbeats 600000 in
private theorem sphericalProductSum_eq_of_satakeTuple_eq (F : PadicField.{u} p)
    {a b I J : ℕ}
    (f₀ : Fin I → SphericalHeckeAlgebra F a) (f₁ : Fin I → SphericalHeckeAlgebra F b)
    (g₀ : Fin J → SphericalHeckeAlgebra F a) (g₁ : Fin J → SphericalHeckeAlgebra F b)
    (h : ∀ (z : Fin (a + 1) → ℂˣ) (w : Fin (b + 1) → ℂˣ)
        (ω₀ : SphericalHeckeAlgebra F a →ₐ[ℂ] ℂ) (ω₁ : SphericalHeckeAlgebra F b →ₐ[ℂ] ℂ),
      IsSatakeCharacter F a (Eigenvalues.ofTuple z) ω₀ →
      IsSatakeCharacter F b (Eigenvalues.ofTuple w) ω₁ →
      ∑ i, ω₀ (f₀ i) * ω₁ (f₁ i) = ∑ j, ω₀ (g₀ j) * ω₁ (g₁ j)) :
    ∀ x y, ∑ i, f₀ i x * f₁ i y = ∑ j, g₀ j x * g₁ j y := by
  intro x y
  have hy (z : Fin (a + 1) → ℂˣ) (ω₀ : SphericalHeckeAlgebra F a →ₐ[ℂ] ℂ)
      (hω₀ : IsSatakeCharacter F a (Eigenvalues.ofTuple z) ω₀) :
      (∑ i, ω₀ (f₀ i) • f₁ i) = ∑ j, ω₀ (g₀ j) • g₁ j := by
    apply sphericalHecke_eq_of_satakeTuple_eq F
    intro w ω₁ hω₁
    simpa only [map_sum, map_smul, smul_eq_mul] using h z w ω₀ ω₁ hω₀ hω₁
  have hx : (∑ i, f₁ i y • f₀ i) = ∑ j, g₁ j y • g₀ j := by
    apply sphericalHecke_eq_of_satakeTuple_eq F
    intro z ω₀ hω₀
    have he := congrArg (SphericalGeneration.evalAt F (r := b) y) (hy z ω₀ hω₀)
    simpa only [map_sum, map_smul, smul_eq_mul, sphericalGeneration_evalAt_apply, mul_comm] using he
  have he := congrArg (SphericalGeneration.evalAt F (r := a) x) hx
  simpa only [map_sum, map_smul, smul_eq_mul, sphericalGeneration_evalAt_apply, mul_comm] using he

section ConstantTerm

variable (F : PadicField.{u} p) (E : PadicField.{v} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "Rect" K => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K

set_option maxHeartbeats 1000000 in
/-- If the ordinary normalized radical integrals have spherical tensor expansions,
the two expansions for `b φ` and `φ` are related by applying lower-rank base change
to the factors. This is a pointwise equality of functions on the actual block Levi. -/
theorem sphericalConstantTerm_baseChange
    (dxF : Measure (Rect F.Carrier)) [dxF.IsAddHaarMeasure]
    (dxE : Measure (Rect E.Carrier)) [dxE.IsAddHaarMeasure]
    (hF : dxF {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer} = 1)
    (hE : dxE {x | ∀ i j, x i j ∈ (ValuativeRel.valuation E.Carrier).integer} = 1)
    {l : ℕ} (b : SphericalHeckeAlgebra E t →ₐ[ℂ] SphericalHeckeAlgebra F t)
    (b₀ : SphericalHeckeAlgebra E (m 0) →ₐ[ℂ] SphericalHeckeAlgebra F (m 0))
    (b₁ : SphericalHeckeAlgebra E (m 1) →ₐ[ℂ] SphericalHeckeAlgebra F (m 1))
    (hb : IsUnramifiedBaseChangeHom F E l t b)
    (hb₀ : IsUnramifiedBaseChangeHom F E l (m 0) b₀)
    (hb₁ : IsUnramifiedBaseChangeHom F E l (m 1) b₁) (φ : SphericalHeckeAlgebra E t)
    {I J : ℕ}
    (f₀ : Fin I → SphericalHeckeAlgebra F (m 0)) (f₁ : Fin I → SphericalHeckeAlgebra F (m 1))
    (φ₀ : Fin J → SphericalHeckeAlgebra E (m 0)) (φ₁ : Fin J → SphericalHeckeAlgebra E (m 1))
    (hCTF : ∀ L : (B).Levi F.Carrier,
      (F.canonicalTopologicalData.leviHalfModulus B L : ℂ) *
        (∫ x, (b φ) (parabolicPoint h (L, x)) ∂dxF) = ∑ i, f₀ i (L 0) * f₁ i (L 1))
    (hCTE : ∀ L : (B).Levi E.Carrier,
      (E.canonicalTopologicalData.leviHalfModulus B L : ℂ) *
        (∫ x, φ (parabolicPoint h (L, x)) ∂dxE) = ∑ j, φ₀ j (L 0) * φ₁ j (L 1)) :
    ∀ L : (B).Levi F.Carrier,
      ∑ i, f₀ i (L 0) * f₁ i (L 1) = ∑ j, b₀ (φ₀ j) (L 0) * b₁ (φ₁ j) (L 1) := by
  suffices hSums : ∀ x y, ∑ i, f₀ i x * f₁ i y = ∑ j, b₀ (φ₀ j) x * b₁ (φ₁ j) y from
    fun L => hSums (L 0) (L 1)
  apply sphericalProductSum_eq_of_satakeTuple_eq F
  intro z₀ z₁ ω₀ ω₁ hω₀ hω₁
  let z : Fin (t + 1) → ℂˣ := Sum.elim z₀ z₁ ∘ (blockEquiv h).symm
  let w : Fin (t + 1) → ℂˣ := fun j => z j ^ l
  have hZ₀ : (fun a => z ((B).index 0 a)) = z₀ := by
    funext a
    rw [← blockEquiv_inl]
    simp [z]
  have hZ₁ : (fun a => z ((B).index 1 a)) = z₁ := by
    funext a
    rw [← blockEquiv_inr]
    simp [z]
  obtain ⟨ω, hω⟩ := (satakeCharacter p F t).1 (Eigenvalues.ofTuple z)
  obtain ⟨ε, hε⟩ := (satakeCharacter p E t).1 (Eigenvalues.ofTuple w)
  obtain ⟨ε₀, hε₀⟩ := (satakeCharacter p E (m 0)).1 (Eigenvalues.power (Eigenvalues.ofTuple z₀) l)
  obtain ⟨ε₁, hε₁⟩ := (satakeCharacter p E (m 1)).1 (Eigenvalues.power (Eigenvalues.ofTuple z₁) l)
  have hW₀ : (fun a => w ((B).index 0 a)) = (fun a => z₀ a ^ l) :=
    congrArg (fun f : Fin (m 0 + 1) → ℂˣ => fun a => f a ^ l) hZ₀
  have hW₁ : (fun a => w ((B).index 1 a)) = (fun a => z₁ a ^ l) :=
    congrArg (fun f : Fin (m 1 + 1) → ℂˣ => fun a => f a ^ l) hZ₁
  have hEvalF := satakeCharacter_eq_sum_of_twoBlock_constantTerm F h dxF hF (b φ)
    f₀ f₁ hCTF z ω ω₀ ω₁ hω (hZ₀.symm ▸ hω₀) (hZ₁.symm ▸ hω₁)
  have hEvalE := satakeCharacter_eq_sum_of_twoBlock_constantTerm E h dxE hE φ
    φ₀ φ₁ hCTE w ε ε₀ ε₁ hε (by rwa [hW₀, ← Eigenvalues.power_ofTuple])
    (by rwa [hW₁, ← Eigenvalues.power_ofTuple])
  have hMatch := DFunLike.congr_fun (hb _ ω ε hω (by rwa [Eigenvalues.power_ofTuple])) φ
  change ω (b φ) = ε φ at hMatch
  rw [← hEvalF, hMatch, hEvalE]
  apply Finset.sum_congr rfl
  intro j _
  have h₀ := DFunLike.congr_fun (hb₀ _ ω₀ ε₀ hω₀ hε₀) (φ₀ j)
  have h₁ := DFunLike.congr_fun (hb₁ _ ω₁ ε₁ hω₁ hε₁) (φ₁ j)
  exact congrArg₂ (· * ·) h₀.symm h₁.symm

end ConstantTerm

end Langlands.BaseChange
