import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.AdelicRelativeCuspidalConstantTerm
import Langlands.Global.ArthurTruncationAverage

/-! # Pointwise Siegel majorants under unipotent averaging -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter MeasureTheory
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSubgroupPoints AdelicSiegelFactors PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "Torus" => intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "chamber" => weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)

/-- A bound depending only on the torus coordinate passes through an ordinary constant term.
The right factor ranges over one enlarged compact set, and invariance is needed under
the rational points of the radical being averaged. -/
theorem exists_compact_siegelRightFactors_constantTerm
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hrho : IsClosedSubgroup rho)
    (J : StandardIndex F G fam.i fam.ν) (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ Ω' : Set A, IsCompact Ω' ∧
      ∀ (f : A → ℂ), (∀ u ∈ rationalImage F (fam.iU J ≫ fam.p J), ∀ g, f (u * g) = f g) →
      ∀ B : Torus → ℝ, (∀ a ∈ chamber t, ∀ w ∈ Ω', ‖f (aG a * w)‖ ≤ B a) →
      ∀ a ∈ chamber t, ∀ w ∈ Ω, ‖fam.constantTerm J f (aG a * w)‖ ≤ B a := by
  let U₀ := Standard.unipotentScheme fam.i fam.ν ∅
  let i₀ := Standard.unipotentHom fam.i fam.ν ∅
  have h₀ := Standard.isClosedSubgroup_unipotentHom fam.i fam.ν ∅
  let : IsAffine U₀.X.left := isAffine_left_of_isClosedSubgroup F i₀ h₀
  let V := adelicPoints F G (rad(J))
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G (rad(J))
  let Q := RationalQuotient F G (rad(J))
  let : IsClosed (V : Set A) := isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
  let : CompactSpace Q := fam.compactSpace_radicalRationalQuotient J
  let mQ := normalizedRationalQuotientHaarMeasure F G (rad(J))
  let : IsProbabilityMeasure mQ := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (rad(J))
  obtain ⟨E, hE, hRep⟩ := ArthurTruncation.exists_compact_radical_representatives (F := F) (rad(J))
  have hle : V ≤ standardUnipotentImage F G fam.T fam.i fam.ν := by
    rw [AdelicSiegelFactors.standardUnipotentImage_eq]
    change (rad(J)).carrier _ ≤ (standardUnipotent fam.i fam.ν ∅).carrier _
    rw [fam.range_radical_eq_standardUnipotent J]
    exact (((standardParabolicOrder F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν
      fam.generic).1 ∅ J.val (Set.empty_subset _) J.property).2 (Set.empty_subset _)).2 _
  let e := rangeEquiv F i₀ (isClosedEmbedding_map_of_isClosedSubgroup F i₀ h₀).isEmbedding
  let b (u : V) : AdelicGroupPoints F U₀ := e.symm (Subgroup.inclusion hle u)
  have hb : Continuous b := e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have he (u : V) : map F U₀ G i₀ (b u) = u.val :=
    map_rangeEquiv_symm F i₀ _ (Subgroup.inclusion hle u)
  obtain ⟨D, hD, hConj⟩ := exists_isCompact_conj_unipotent fam.connectedReductive hsetup rho hrho
    (b '' E) (hE.image hb) t
  refine ⟨D * Ω, hD.mul hΩ, fun f hInv B hB a ha w hw => ?_⟩
  let x := aG a * w
  let l : Q → ℂ := LeftCosetSpace.lift Γ (fun u : V => f (u.val * x)) (fun r u => by
    change f ((r.val.val * u.val) * x) = f (u.val * x)
    rw [mul_assoc]
    exact hInv _ ((mem_rationalSubgroup_range_iff (fam.iU J ≫ fam.p J) r.val).mp r.property) _)
  change ‖∫ q : Q, f ((Quotient.out q : V).val * x) ∂mQ‖ ≤ B a
  refine (norm_integral_le_of_norm_le_const (C := B a) (Eventually.of_forall fun q => ?_)).trans_eq (by simp)
  obtain ⟨u, hu, hq⟩ := hRep q
  have hiq : f ((Quotient.out q : V).val * x) = f (u.val * x) := by
    change l (LeftCosetSpace.mk Γ (Quotient.out q)) = l (LeftCosetSpace.mk Γ u)
    exact congrArg l ((Quotient.out_eq q).trans hq.symm)
  have hm : (aG a)⁻¹ * u.val * aG a ∈ D := by
    have h := hConj (b u) ⟨u, hu, rfl⟩ a ha
    rwa [he u] at h
  rw [hiq]
  have heq : u.val * x = aG a * (((aG a)⁻¹ * u.val * aG a) * w) := by
    dsimp only [x]
    group
  rw [heq]
  exact hB _ ha _ (Set.mul_mem_mul hm hw)

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- A torus-dependent majorant transfers through a standard radical average by enlarging
the compact right factors. -/
def AdelicSiegelWeightedAverageStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
    (j : T₀ ⟶ fam.T) {N : ℕ} (rho : MatrixRepresentation G (Fin N)),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j → IsClosedSubgroup rho →
    ∀ (J : StandardIndex F G fam.i fam.ν) (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)),
      IsCompact Ω →
    let chamber := weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t
    let aG := positiveMap F G fam.T fam.i T₀ j
    ∃ Ω' : Set (AdelicGroupPoints F G), IsCompact Ω' ∧
      ∀ (f : AdelicGroupPoints F G → ℂ),
        (∀ u ∈ rationalImage F (fam.iU J ≫ fam.p J), ∀ g, f (u * g) = f g) →
      ∀ B : intrinsicSubgroup F T₀ → ℝ,
        (∀ a ∈ chamber, ∀ w ∈ Ω', ‖f (aG a * w)‖ ≤ B a) →
        ∀ a ∈ chamber, ∀ w ∈ Ω, ‖fam.constantTerm J f (aG a * w)‖ ≤ B a

theorem adelicSiegelWeightedAverage : AdelicSiegelWeightedAverageStatement := by
  intro F _ _ G _ _ _ fam T₀ j N rho hsetup hrho J t Ω hΩ
  exact fam.exists_compact_siegelRightFactors_constantTerm j rho hsetup hrho J t Ω hΩ

end Langlands.Global
