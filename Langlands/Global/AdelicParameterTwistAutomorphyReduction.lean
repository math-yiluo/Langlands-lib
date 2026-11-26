import Langlands.Global.AdelicParameterTwistAutomorphyReductionStatement
import Langlands.Global.AdelicSmoothIwasawaHeight
import Langlands.Global.AdelicHeightPowerPolynomialBound
import Langlands.Global.AdelicIntertwiningAutomorphyReduction
import Langlands.Global.AdelicIntertwiningModerateGrowthProof

/-! # Automorphy of twists from center finiteness of twists: proof

For a compact `K` with `P(𝔸) K = G(𝔸)` and `λ ∈ X^*(P) ⊗ ℂ`, the twist
`φ_λ(g) = φ(g) m_P(g)^λ` inherits from `φ`:

* left invariance under `U(𝔸) M(F)` (`IsIwasawaCompact.isLeftInvariantUnder_parameterTwist`);
* smoothness, for a maximal compact `K` (`IsIwasawaCompact.isAdelicSmoothFunction_parameterTwist`);
* finiteness under the archimedean part of `K`
  (`IsIwasawaCompact.isInfiniteSubgroupFiniteFunction_parameterTwist`);
* moderate growth for a closed matrix embedding
  (`IsIwasawaCompact.hasModerateGrowthFunction_parameterTwist`).

With the remaining condition, `𝔷`-finiteness, supplied by `ParameterTwistCenterFiniteStatement`,
`parameterTwistAutomorphy_of_centerFinite` proves `ParameterTwistAutomorphyStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints RepresentationGrowth

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The factor `m_P^λ` is right `K`-invariant. -/
theorem IsIwasawaCompact.heightPower_mul_right (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    hK.heightPower lam (g * k) = hK.heightPower lam g := by
  rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, hK.height_mul_right g hk]

/-- The twist is left invariant under `U(𝔸) M(F)` when `φ` is and `U` is unipotent. -/
theorem IsIwasawaCompact.isLeftInvariantUnder_parameterTwist (hK : IsIwasawaCompact p K)
    {U M : GroupScheme (Spec (CommRingCat.of F))} (iU : U ⟶ P) (l : M ⟶ P)
    (hU : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (hK.parameterTwist φ lam) := by
  have hH : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l)
      (hK.heightPower lam) := by
    apply isLeftInvariantUnder_sup
    · rintro _ ⟨x, rfl⟩ g
      exact hK.heightPower_unipotent_mul hU iU lam x g
    · rintro _ ⟨m₀, rfl⟩ g
      change hK.heightPower lam (map F M G (l ≫ p) (rational F M m₀) * g) = _
      rw [map_comp_apply_of_hom, map_rational_eq_rational, hK.heightPower_rational_mul]
  intro x hx g
  simp only [IsIwasawaCompact.parameterTwist, hφ x hx g, hH x hx g]

/-- The twist of a smooth function is smooth, for a maximal compact `K`: it is continuous, its
infinite slices are smooth because those of the height pairing are
(`IsIwasawaCompact.hasSmoothHeightPairings_of_maximalCompact`), and an open subgroup of the
finite projection of `K` contained in the finite level of `φ` fixes it. -/
theorem IsIwasawaCompact.isAdelicSmoothFunction_parameterTwist [LocallyOfFiniteType G.X.hom]
    (hK : IsIwasawaCompact p K) (hmax : IsMaximalCompactSubgroup F G K) {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAdelicSmoothFunction F G φ) (lam : ComplexCharacterParameter F P) :
    IsAdelicSmoothFunction F G (hK.parameterTwist φ lam) := by
  obtain ⟨hcont, hslice, L, hLo, hL⟩ := hφ
  refine ⟨hK.continuous_parameterTwist hcont lam, fun b => ?_, ?_⟩
  · have hH := hK.hasSmoothHeightPairings_of_maximalCompact hsmooth hmax
    have hφs := fun b' => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hslice b')
    exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
      (hK.contMDiff_parameterTwist_slice hsmooth hH φ lam hφs b)
  · refine ⟨L ⊓ K.map (finite F G).toMonoidHom,
      hLo.inter (IsMaximalCompactSubgroup.isOpen_finite F G K hmax), fun b hb g => ?_⟩
    have hbK : ofFinite F G b ∈ K :=
      IsMaximalCompactSubgroup.map_finite_le_comap_ofFinite hmax hb.2
    simp only [IsIwasawaCompact.parameterTwist, hL b hb.1 g, hK.heightPower_mul_right lam g hbK]

/-- The right translates of the twist by the archimedean part of `K` are the translates of `φ`
multiplied by the fixed function `m_P^λ`, so they span a finite-dimensional space when those of
`φ` do. -/
theorem IsIwasawaCompact.isInfiniteSubgroupFiniteFunction_parameterTwist
    (hK : IsIwasawaCompact p K) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ)
    (lam : ComplexCharacterParameter F P) :
    IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
      (hK.parameterTwist φ lam) := by
  let T : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    LinearMap.mulRight ℂ (hK.heightPower lam)
  have heq : (fun k : K.comap (ofInfinite F G).toMonoidHom => fun g : AdelicGroupPoints F G =>
      hK.parameterTwist φ lam (g * ofInfinite F G k)) =
      T ∘ fun k : K.comap (ofInfinite F G).toMonoidHom => fun g : AdelicGroupPoints F G =>
        φ (g * ofInfinite F G k) := by
    funext k g
    have hk : ofInfinite F G k ∈ K := k.2
    simp only [Function.comp_apply, T, LinearMap.mulRight_apply, Pi.mul_apply,
      IsIwasawaCompact.parameterTwist, hK.heightPower_mul_right lam g hk]
  unfold IsInfiniteSubgroupFiniteFunction at hφ ⊢
  rw [heq, Set.range_comp, Submodule.span_image]
  infer_instance

/-- The twist of a function of moderate growth has moderate growth, since `m_P^λ` is bounded by
a power of the adelic height of a closed matrix embedding
(`IsIwasawaCompact.exists_norm_heightPower_le_adelicHeight`). For a matrix embedding of size
zero the adelic points form a trivial group. -/
theorem IsIwasawaCompact.hasModerateGrowthFunction_parameterTwist (hK : IsIwasawaCompact p K)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ} (hφ : HasModerateGrowthFunction F G rho φ)
    (lam : ComplexCharacterParameter F P) :
    HasModerateGrowthFunction F G rho (hK.parameterTwist φ lam) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have := subsingleton_adelicGroupPoints_of_closed_zeroMatrix rho hrho
    refine ⟨‖hK.parameterTwist φ lam 1‖ + 1, by positivity, 0, fun g => ?_⟩
    rw [Subsingleton.elim g 1, Real.rpow_zero, mul_one]
    exact le_add_of_nonneg_right zero_le_one
  obtain ⟨C, hC, r, hr⟩ := hφ
  obtain ⟨A, e, hA, he, hb⟩ := hK.exists_norm_heightPower_le_adelicHeight rho hN hrho lam
  let s : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hs : 0 < s := pow_pos (Nat.cast_pos.mpr hN) _
  refine ⟨C * A * s ^ e, by positivity, r + e, fun g => ?_⟩
  have hsN : 0 < adelicSourceNorm F G rho g := adelicSourceNorm_pos F G rho hN g
  have hHs : adelicHeight F G rho g = s * adelicSourceNorm F G rho g :=
    adelicHeight_eq_scalar_mul_sourceNorm F G rho g
  rw [IsIwasawaCompact.parameterTwist, norm_mul]
  calc ‖φ g‖ * ‖hK.heightPower lam g‖
      ≤ (C * adelicSourceNorm F G rho g ^ r) * (A * adelicHeight F G rho g ^ e) :=
        mul_le_mul (hr g) (hb g) (norm_nonneg _)
          (mul_nonneg hC.le (Real.rpow_nonneg hsN.le _))
    _ = C * A * s ^ e * adelicSourceNorm F G rho g ^ (r + e) := by
        rw [hHs, Real.mul_rpow hs.le hsN.le, Real.rpow_add hsN]
        ring

end AdelicGroupPoints

/-- **Automorphy of twists from center finiteness of twists.**
`ParameterTwistCenterFiniteStatement` implies `ParameterTwistAutomorphyStatement`. Left
invariance, smoothness, finiteness under the archimedean part of `K` and moderate growth pass
from `φ` to `φ_λ` by the four lemmas of this module; `𝔷`-finiteness is the premise, applied with
the left invariance of `φ` under `U_I(𝔸)`. -/
theorem parameterTwistAutomorphy_of_centerFinite
    (hZ : ParameterTwistCenterFiniteStatement.{u}) : ParameterTwistAutomorphyStatement.{u} := by
  intro F _ _ G _ _ _ fam I _ K hK hmax _ _ N d rho hsmooth hrho phi hphi lam
  obtain ⟨hleft, hsm, hfin, hcen, hgrowth⟩ := hphi
  exact ⟨hK.isLeftInvariantUnder_parameterTwist (fam.iU I) (fam.l I)
      (fam.isUnipotentRadical I).1.isUnipotent hleft lam,
    hK.isAdelicSmoothFunction_parameterTwist hmax hsmooth hsm lam,
    hK.isInfiniteSubgroupFiniteFunction_parameterTwist hfin lam,
    hZ F G fam I K hK hmax hsmooth _ phi (fun x hx g => hleft x (Subgroup.mem_sup_left hx) g)
      hsm hcen lam,
    hK.hasModerateGrowthFunction_parameterTwist rho hrho hgrowth lam⟩

/-- Proof of `ParameterTwistAutomorphyReductionStatement`. -/
theorem parameterTwistAutomorphyReduction : ParameterTwistAutomorphyReductionStatement.{u} :=
  parameterTwistAutomorphy_of_centerFinite

end Langlands.Global
