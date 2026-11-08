import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Rational characters have valuation one on the original integral image -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Geometry.Building GaloisPointComparison

section Bound

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
  (M : IntegralModel R K G)
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

/-- A rational point, as a `K`-algebra map on the generic regular functions. -/
private def pointAlgHom (g : rationalPoints G) : AffineCoordinateRing K G.X →ₐ[K] K :=
  affineSchemePointEquiv K G.X K (rationalPointEquiv K G.X g)

private theorem pointAlgHom_apply (g : rationalPoints G) (a : AffineCoordinateRing K G.X) :
    pointAlgHom g a =
      G.affinePointEvaluation (CommAlgCat.of K K) (rationalCoeffEquiv K G g) a := by
  rw [rationalCoeffEquiv_eq]
  exact affineSchemePointEquiv_apply_eq_evaluation G _ a

/-- Every generic coordinate is bounded on the original integral image, as a point algebra
map. -/
private theorem exists_pointAlgHom_bound (hv : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (a : AffineCoordinateRing K G.X) :
    ∃ B : Γ₀, ∀ g ∈ M.integralPoints, v (pointAlgHom g a) ≤ B := by
  have ha : a ∈ Algebra.adjoin K (Set.range M.genericCoordinate) := by
    rw [M.adjoin_range_genericCoordinate_eq_top]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    refine ⟨1, fun g hg => ?_⟩
    rw [pointAlgHom_apply]
    obtain ⟨r, hr⟩ := (M.mem_integralPoints_iff_genericCoordinates g).mp hg b
    rw [← hr]
    exact hv r
  | algebraMap c =>
    exact ⟨v c, fun g _ => by rw [AlgHom.commutes]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨B, hB⟩ := hx
    obtain ⟨C, hC⟩ := hy
    exact ⟨max B C, fun g hg => by
      rw [map_add]
      exact (v.map_add _ _).trans (max_le_max (hB g hg) (hC g hg))⟩
  | mul x y _ _ hx hy =>
    obtain ⟨B, hB⟩ := hx
    obtain ⟨C, hC⟩ := hy
    exact ⟨B * C, fun g hg => by
      rw [map_mul, v.map_mul]
      exact mul_le_mul' (hB g hg) (hC g hg)⟩

/-- Every generic regular function has valuation bounded on the original integral image,
when the valuation is at most one on the original integral ring. -/
theorem exists_valuation_bound (hv : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (a : Γ(G.X.left, ⊤)) :
    ∃ B : Γ₀, ∀ g ∈ M.integralPoints,
      v (G.affinePointEvaluation (CommAlgCat.of K K) (rationalCoeffEquiv K G g) a) ≤ B := by
  obtain ⟨B, hB⟩ := M.exists_pointAlgHom_bound hv a
  exact ⟨B, fun g hg => by rw [← pointAlgHom_apply]; exact hB g hg⟩

omit [IsAffine G.X.left] in
/-- The global function of an actual rational character: the pullback along it of the
universal unit coordinate of `𝔾_m`. -/
def rationalCharacterCoordinate (χ : rationalCharacters G) : Γ(G.X.left, ⊤) :=
  χ.toMul.hom.hom.left.appTop (Gm.universalUnit (CommRingCat.of K)).val

omit [IsAffine G.X.left] in
/-- The value of an actual rational character is the evaluation of its global function. -/
theorem rationalCharacterEval_val_eq_evaluation (χ : rationalCharacters G)
    (g : rationalPoints G) :
    (rationalCharacterEval χ g : K) =
      G.affinePointEvaluation (CommAlgCat.of K K) (rationalCoeffEquiv K G g)
        (rationalCharacterCoordinate χ) := by
  rw [rationalCharacterEval_eq_affineUnitsEquiv, Gm.affineUnitsEquiv_eq_map, Units.coe_map,
    rationalCoeffEquiv_eq]
  rfl

/-- In a multiplicatively archimedean value group, an element whose positive and negative
powers are all bounded is one. -/
private theorem eq_one_of_pow_le_of_inv_pow_le [MulArchimedean Γ₀] {a B : Γ₀} (ha : a ≠ 0)
    (h : ∀ n : ℕ, a ^ n ≤ B) (h' : ∀ n : ℕ, a⁻¹ ^ n ≤ B) : a = 1 := by
  have key : ∀ b : Γ₀, (∀ n : ℕ, b ^ n ≤ B) → ¬ 1 < b := by
    intro b hb hlt
    obtain ⟨n, hn⟩ := MulArchimedean.arch B hlt
    have hpos : 0 < b ^ n := pow_pos (zero_lt_one.trans hlt) n
    have h1 : b ^ n * b ≤ b ^ n * 1 := by
      rw [mul_one, ← pow_succ]
      exact (hb (n + 1)).trans hn
    exact (not_le.mpr hlt) ((mul_le_mul_iff_right₀ hpos).mp h1)
  rcases lt_trichotomy a 1 with hlt | heq | hgt
  · exact absurd ((one_lt_inv₀ (zero_lt_iff.mpr ha)).mpr hlt) (key a⁻¹ h')
  · exact heq
  · exact absurd hgt (key a h)

/-- Every actual rational character has valuation one on the original integral image, for
any multiplicatively archimedean valuation that is at most one on the original integral
ring. -/
theorem integralPoints_le_characterValuationKernel [MulArchimedean Γ₀]
    (hv : ∀ r : R, v (algebraMap R K r) ≤ 1) :
    M.integralPoints ≤ characterValuationKernel v G := by
  intro g hg
  rw [mem_characterValuationKernel]
  intro χ
  obtain ⟨B, hB⟩ := M.exists_valuation_bound hv (rationalCharacterCoordinate χ)
  have hbound : ∀ h ∈ M.integralPoints, v (rationalCharacterEval χ h : K) ≤ B := by
    intro h hh
    rw [rationalCharacterEval_val_eq_evaluation]
    exact hB h hh
  apply eq_one_of_pow_le_of_inv_pow_le (B := B)
  · exact (Valuation.ne_zero_iff v).mpr (Units.ne_zero _)
  · intro n
    have := hbound (g ^ n) (M.integralPoints.pow_mem hg n)
    rwa [map_pow, Units.val_pow_eq_pow_val, map_pow] at this
  · intro n
    have := hbound (g⁻¹ ^ n) (M.integralPoints.pow_mem (M.integralPoints.inv_mem hg) n)
    rwa [map_pow, map_inv, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow,
      map_inv₀] at this

end Bound

section Unramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

private instance unramifiedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

private instance unramifiedAffine : IsAffine (baseChanged F (inertiaFixedField F) G).X.left :=
  isAffine_of_isAffineHom (baseChanged F (inertiaFixedField F) G).X.hom

/-- The image of the actual maximal-unramified base change of the supplied model lies in
the common kernel of the normalized valuations of the rational characters upstairs. -/
theorem baseChangeUnramified_integralPoints_le_characterValuationKernel :
    M.baseChangeUnramified.integralPoints ≤
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) :=
  M.baseChangeUnramified.integralPoints_le_characterValuationKernel fun r =>
    ((MaximalUnramified.valuation_isEquiv F).le_one_iff_le_one).mpr r.property

end Unramified

end Langlands.GroupScheme.IntegralModel
