import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.AdelicEisensteinRationalCosets
import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.ProjectiveHeightSummability

/-! # Absolute convergence from polynomially bounded rational representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Rational parabolic cosets admit representatives of matrix height bounded by a
fixed power of their supplied coset heights. -/
def HasPolynomialRationalCosetRepresentatives {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (height : ParabolicRationalCosets F p → ℝ) : Prop :=
  ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ c : ParabolicRationalCosets F p,
    ∃ x : RationalGroupPoints F G, Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩ = c ∧
      adelicHeightAtLeastOne rho (rational F G x) ≤ B * height c ^ d

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  [Fintype (relativeWeylGroup r.data.i)]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

include hA hT in
set_option maxHeartbeats 800000 in
/-- Moderate growth, regular parameter decay, and polynomially bounded rational
representatives give a compact-uniform summable majorant for the Eisenstein terms. -/
theorem IsIwasawaCompact.exists_summable_eisenstein_majorant_of_projectiveRepresentatives
    (hK : IsIwasawaCompact p K) (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {N n : ℕ} (rho : MatrixRepresentation G (Fin N)) (σ : MatrixRepresentation G (Fin n))
    (j : Fin n) (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (hrep : HasPolynomialRationalCosetRepresentatives rho
      (fun c => (parabolicRationalProjectiveEmbedding σ j hstab c).mulHeight))
    (φ : AdelicGroupPoints F G → ℂ)
    (hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hφ : HasModerateGrowthFunction F G rho φ) :
    ∃ R : ℝ, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∀ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (Λ : Set (Fin m → ℂ)), IsCompact Λ →
        (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
        ∃ b : ParabolicRationalCosets F p → ℝ, Summable b ∧
          ∀ c : ParabolicRationalCosets F p, ∀ g ∈ C, ∀ s ∈ Λ,
            ‖hK.eisensteinTerm φ (e s) g c‖ ≤ b c := by
  classical
  let E := parabolicRationalProjectiveEmbedding σ j hstab
  let H := fun c : ParabolicRationalCosets F p => (E c).mulHeight
  have hH (c : ParabolicRationalCosets F p) : 0 < H c := Projectivization.mulHeight_pos (E c)
  obtain ⟨B, d, hB, hd, hrep⟩ := hrep
  choose x hx hrep using hrep
  obtain ⟨r₀, hr₀, hφC⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hφ
  obtain ⟨t, ht, hsum⟩ := summable_projectivization_mulHeight_rpow F (Fin n)
  let weight := d * r₀ + t
  obtain ⟨R, hparam⟩ := hK.exists_norm_heightPower_rational_le_projectiveHeight r hA hT hG
    σ j hstab weight (add_nonneg (mul_nonneg hd hr₀) ht)
  refine ⟨R, fun C hC m e Λ hΛ hreg => ?_⟩
  obtain ⟨A₀, hA₀, hφbound⟩ := hφC C hC
  obtain ⟨D₀, hD₀, hparamBound⟩ := hparam m e.toLinearMap Λ hΛ hreg
  obtain ⟨D₁, hD₁, hcompactBound⟩ := hK.exists_norm_heightPower_mul_le hC e.toLinearMap hΛ
  let Cφ := A₀ * B ^ r₀
  let Ctwist := D₁ * D₀
  have hCφ : 0 ≤ Cφ := mul_nonneg hA₀.le (Real.rpow_nonneg hB.le _)
  let b := fun c : ParabolicRationalCosets F p => Cφ * Ctwist * H c ^ (-t)
  refine ⟨b, ((hsum t le_rfl).comp_injective E.injective).mul_left _, ?_⟩
  intro c g hg s hs
  rw [hK.eisensteinTerm_eq_of_representative hinv r.isCompatible.levi hU _ g c
    ⟨rational F G (x c), ⟨x c, rfl⟩⟩ (hx c), IsIwasawaCompact.parameterTwist, norm_mul]
  have hφx : ‖φ (rational F G (x c) * g)‖ ≤ Cφ * H c ^ (d * r₀) := by
    have hgrowth : 0 ≤ adelicHeightAtLeastOne rho (rational F G (x c)) :=
      zero_le_one.trans (le_max_left _ _)
    have hr := Real.rpow_le_rpow hgrowth (hrep c) hr₀
    rw [Real.mul_rpow hB.le (Real.rpow_nonneg (hH c).le _), ← Real.rpow_mul (hH c).le] at hr
    exact (hφbound _ g hg).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hr hA₀.le)
  have htwist : ‖hK.heightPower (e s) (rational F G (x c) * g)‖ ≤
      Ctwist * H c ^ (-weight) := by
    have hp := hparamBound (x c) s hs
    rw [hx c] at hp
    refine (hcompactBound _ g hg s hs).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hp hD₁.le
  calc
    _ ≤ (Cφ * H c ^ (d * r₀)) * (Ctwist * H c ^ (-weight)) :=
      mul_le_mul hφx htwist (norm_nonneg _) (mul_nonneg hCφ (Real.rpow_nonneg (hH c).le _))
    _ = Cφ * Ctwist * (H c ^ (d * r₀) * H c ^ (-weight)) := by ring
    _ = b c := by
      rw [← Real.rpow_add (hH c), show d * r₀ + -weight = -t by dsimp [weight]; ring]

end Langlands.Global.AdelicGroupPoints
