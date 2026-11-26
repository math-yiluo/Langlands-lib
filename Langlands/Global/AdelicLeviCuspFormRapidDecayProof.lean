import Langlands.Global.AdelicLeviCuspFormRapidDecayStatement
import Langlands.Global.AdelicNormOneCuspidalRapidDecay
import Langlands.Global.AdelicUniformDirectionalGrowth
import Langlands.Global.AdelicStandardLeviInfiniteCompact
import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth

/-! # Rapid decay of Levi cusp forms on norm-one representatives: proof

The cusp form `ψ` on a standard Levi `M_J` has one growth exponent for all its archimedean
derivative words (the elliptic estimate behind `exists_uniformGrowth_functionInfiniteSlices`).
The norm-one Siegel cover of `M_J` from `adelicNormOneCuspidalRapidDecay` then gives the decay,
and the height of `M_J` for the restricted representation is the height of `G` along the Levi
inclusion. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Geometry.Manifold RepresentationGrowth

section Slices

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On a plot-smooth archimedean slice, the actual enveloping action of the ordered product of
the generators of a word of real directions is the iterated right-orbit derivative along the
word. -/
theorem plotSmoothEnvelopingAction_directionalWord_slice
    (hcalc : AdelicDifferentialCommutator F G hG) (s : List (smoothModel F d))
    (φ : AdelicGroupPoints F G → ℂ) (b : FiniteAdelicGroupPoints F G)
    (hs : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G)
    (a : InfiniteAdelicGroupPoints F G) :
    adelicIteratedDirectionalValue hG s φ (pair F G a b) =
      (plotSmoothEnvelopingAction F G hG hcalc (adelicDirectionalWordEnveloping hG s)
        ⟨functionInfiniteSlice F G φ b, hs⟩).val a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  induction s generalizing a with
  | nil =>
    change φ (pair F G a b) =
      (plotSmoothEnvelopingAction F G hG hcalc 1 ⟨functionInfiniteSlice F G φ b, hs⟩).val a
    rw [map_one, Module.End.one_apply]
    rfl
  | cons X s ih =>
    let w := adelicDirectionalWordEnveloping hG s
    let gen : AdelicEnvelopingAlgebra F G hG :=
      UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ]
        (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))
    change adelicDirectionalValue hG X (adelicIteratedDirectionalValue hG s φ) (pair F G a b) =
      (plotSmoothEnvelopingAction F G hG hcalc (gen * w) ⟨functionInfiniteSlice F G φ b, hs⟩).val a
    rw [map_mul, Module.End.mul_apply, plotSmoothEnvelopingAction_real_generator,
      adelicDirectionalValue_pair]
    have hfun : (fun y => adelicIteratedDirectionalValue hG s φ (pair F G y b)) =
        (plotSmoothEnvelopingAction F G hG hcalc w ⟨functionInfiniteSlice F G φ b, hs⟩).val :=
      funext ih
    rw [hfun]
    rfl

end Slices

/-- Mœglin–Waldspurger I.2.12 (Corollary) and I.2.18 on a standard Levi: a cusp form on
`M_J(F) \ M_J(𝔸)` times any power of the ambient height is bounded at one representative of
every class of the norm-one quotient. -/
theorem leviCuspFormRapidDecay : LeviCuspFormRapidDecayStatement.{u} := by
  intro F _ _ G _ _ _ fam K _hK _hIw hKM N rho hN _hrho Kinf J ψ hψ e _he
  obtain ⟨⟨hΓ, hsm, hKfin, hZ, hgrowth⟩, hcusp⟩ := hψ
  let rhoM : MatrixRepresentation (fam.M J) (Fin N) := fam.l J ≫ fam.p J ≫ rho
  have hM : IsConnectedReductive (fam.M J) := (fam.isCompatible J).levi.isConnectedReductive
  have hKinf := fam.leviInfiniteCompact_isMaximal J K (hKM J)
  obtain ⟨R, hR, hderiv⟩ := exists_uniformGrowth_functionInfiniteSlices F (fam.M J)
    (fam.leviSmooth J) (adelicDifferentialCommutator_of_smooth F (fam.M J) (fam.leviSmooth J))
    rhoM hN hM (fam.leviInfiniteCompact Kinf J) hKinf ψ hsm.2.1 hKfin hZ hgrowth
  have hGrowth : ∀ s : List (smoothModel F (fam.leviDim J)), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖adelicIteratedDirectionalValue (fam.leviSmooth J) s ψ x‖ ≤
        C * adelicHeight F (fam.M J) rhoM x ^ R := by
    intro s
    obtain ⟨C, hC, hb⟩ := hderiv (adelicDirectionalWordEnveloping (fam.leviSmooth J) s)
    refine ⟨C, hC, fun x => ?_⟩
    rw [← pair_projections F (fam.M J) x, plotSmoothEnvelopingAction_directionalWord_slice
      (fam.leviSmooth J) (adelicDifferentialCommutator_of_smooth F (fam.M J) (fam.leviSmooth J))
      s ψ _ (hsm.2.1 _)]
    exact hb _ _
  obtain ⟨S, hSsub, hScover, hdecay⟩ := adelicNormOneCuspidalRapidDecay (fam.leviSmooth J) rhoM hM hN
  obtain ⟨C, hC, hCb⟩ := hdecay ψ hsm hΓ hcusp R hR hGrowth ⌈e⌉₊
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective _ x
  obtain ⟨q, hq⟩ := hScover y
  let qn : rationalNormOneSubgroup F (fam.M J) := ⟨rationalNormOne F (fam.M J) q, q, rfl⟩
  refine ⟨⟨rational F (fam.M J) q * y.val, hSsub hq⟩, ?_, ?_⟩
  · have hrep : (⟨rational F (fam.M J) q * y.val, hSsub hq⟩ : normOneSubgroup F (fam.M J)) =
        (qn : normOneSubgroup F (fam.M J)) * y := Subtype.ext rfl
    rw [hrep, LeftCosetSpace.mk_subgroup_mul]
  · set z := rational F (fam.M J) q * y.val
    have hHeight : adelicHeight F (fam.M J) rhoM z =
        adelicHeight F G rho (map F (fam.M J) G (fam.l J ≫ fam.p J) z) := by
      change AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
          (map F (fam.M J) _ ((fam.l J ≫ fam.p J) ≫ rho) z)) =
        AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
          (map F G _ rho (map F (fam.M J) G (fam.l J ≫ fam.p J) z)))
      rw [map_comp_apply_of_hom]
    have h1 : 1 ≤ adelicHeight F G rho (map F (fam.M J) G (fam.l J ≫ fam.p J) z) :=
      one_le_adelicHeight F G rho hN _
    calc
      adelicHeight F G rho (map F (fam.M J) G (fam.l J ≫ fam.p J) z) ^ e * ‖ψ z‖ ≤
          adelicHeight F G rho (map F (fam.M J) G (fam.l J ≫ fam.p J) z) ^ (⌈e⌉₊ : ℝ) *
            ‖ψ z‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil e))
          (norm_nonneg _)
      _ = ‖ψ z‖ * adelicHeight F (fam.M J) rhoM z ^ ⌈e⌉₊ := by
        rw [Real.rpow_natCast, hHeight, mul_comm]
      _ ≤ C := hCb z hq

end Langlands.Global
