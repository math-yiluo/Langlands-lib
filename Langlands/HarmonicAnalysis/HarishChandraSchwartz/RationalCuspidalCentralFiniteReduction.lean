import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements

/-! # Elementary reductions for Waldspurger VIII.4.1

The first paragraph of the proof of VIII.4.1 disposes of a character that is
nontrivial on `A_G ∩ H`: every central integral of a left `H`-invariant function
vanishes, with no convergence premise. Central convergence identifies the span
with the raw image. The remaining assertion is finite dimensionality in the case
where the character is trivial on `A_G ∩ H`; it is a named proposition here.
-/

noncomputable section

universe u uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Generic

section Translation

variable {Γ : Type uG} [Group Γ] {A : Subgroup Γ} [MeasurableSpace A]
  [MeasurableMul A] {μA : Measure A} [μA.IsMulLeftInvariant] {χ : A →* ℂˣ}

/-- Translation by `b ∈ A ∩ H` in the Haar integral: `p_χ f = χ(b)⁻¹ p_χ f` for a
left `H`-invariant `f`. No integrability is needed. -/
theorem centralProjection_eq_inv_mul_of_isLeftInvariant {H : Subgroup Γ} {f : Γ → ℂ}
    (hf : IsLeftInvariant H f) {b : A} (hbH : (b : Γ) ∈ H) (g : Γ) :
    centralProjection μA χ f g = (((χ b)⁻¹ : ℂˣ) : ℂ) * centralProjection μA χ f g := by
  unfold centralProjection
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hx : ((b * a : A) : Γ) * g = (b : Γ) * ((a : Γ) * g) := by
    simp only [Subgroup.coe_mul, mul_assoc]
  simp only [hx, hf (b : Γ) hbH, map_mul, mul_inv_rev, Units.val_mul]
  ring

/-- The first step of VIII.4.1: if `χ` is nontrivial on `A ∩ H`, the central
integral of every left `H`-invariant function is zero. -/
theorem centralProjection_eq_zero_of_isLeftInvariant {H : Subgroup Γ} {f : Γ → ℂ}
    (hf : IsLeftInvariant H f) {b : A} (hbH : (b : Γ) ∈ H) (hχb : χ b ≠ 1) :
    centralProjection μA χ f = 0 := by
  funext g
  have h := centralProjection_eq_inv_mul_of_isLeftInvariant (μA := μA) (χ := χ) hf hbH g
  have hne : (((χ b)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
    intro h1
    apply hχb
    have : (χ b)⁻¹ = 1 := Units.ext (by simpa using h1)
    simpa using congrArg (·⁻¹) this
  have h' : ((((χ b)⁻¹ : ℂˣ) : ℂ) - 1) * centralProjection μA χ f g = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · simpa using h0

variable [TopologicalSpace Γ] {Ξ σ : Γ → ℝ} (E : Submodule ℂ (Space Ξ σ))

/-- If every element of `E` is left `H`-invariant and `χ` is nontrivial on `A ∩ H`,
the raw image is `{0}`. -/
theorem schwartzCentralIntegralImage_eq_zero_of_isLeftInvariant {H : Subgroup Γ}
    (hE : ∀ φ ∈ E, IsLeftInvariant H (φ : Γ → ℂ)) {b : A} (hbH : (b : Γ) ∈ H)
    (hχb : χ b ≠ 1) :
    schwartzCentralIntegralImage E μA χ = {0} := by
  ext f
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact centralProjection_eq_zero_of_isLeftInvariant (hE φ hφ) hbH hχb
  · rintro rfl
    exact ⟨0, E.zero_mem,
      centralProjection_eq_zero_of_isLeftInvariant (fun _ _ _ => rfl) hbH hχb⟩

/-- In the same situation the span is zero. -/
theorem schwartzCentralIntegralSpan_eq_bot_of_isLeftInvariant {H : Subgroup Γ}
    (hE : ∀ φ ∈ E, IsLeftInvariant H (φ : Γ → ℂ)) {b : A} (hbH : (b : Γ) ∈ H)
    (hχb : χ b ≠ 1) :
    schwartzCentralIntegralSpan E μA χ = ⊥ := by
  rw [schwartzCentralIntegralSpan,
    schwartzCentralIntegralImage_eq_zero_of_isLeftInvariant E hE hbH hχb,
    Submodule.span_singleton_eq_bot]

end Translation

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] {A : Subgroup Γ} [MeasurableSpace A]
  {μA : Measure A} {χ : A →* ℂˣ} {Ξ σ : Γ → ℝ}

/-- Convergence on a larger submodule restricts to a smaller one. -/
theorem CentralIntegralConvergesOn.mono_of_le {E E' : Submodule ℂ (Space Ξ σ)} (h : E' ≤ E)
    (hE : CentralIntegralConvergesOn E μA χ) : CentralIntegralConvergesOn E' μA χ :=
  fun φ hφ g => hE φ (h hφ) g

end Generic

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
  (χ : (rationalPoints.map s).range →* ℂˣ)

/-- VIII.4.1 when `χ` is nontrivial on `A_G ∩ H`: the actual level image is `{0}`. -/
theorem rationalCuspidalCentralLevelImage_eq_zero (H : Subgroup (rationalPoints G))
    {b : (rationalPoints.map s).range} (hbH : (b : rationalPoints G) ∈ H) (hχb : χ b ≠ 1) :
    rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H = {0} :=
  schwartzCentralIntegralImage_eq_zero_of_isLeftInvariant _
    (fun _ hφ => hφ.2.isLeftInvariant) hbH hχb

/-- VIII.4.1 when `χ` is nontrivial on `A_G ∩ H`: the actual level span is zero. -/
theorem rationalCuspidalCentralLevelSpan_eq_bot (H : Subgroup (rationalPoints G))
    {b : (rationalPoints.map s).range} (hbH : (b : rationalPoints G) ∈ H) (hχb : χ b ≠ 1) :
    rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H = ⊥ :=
  schwartzCentralIntegralSpan_eq_bot_of_isLeftInvariant _
    (fun _ hφ => hφ.2.isLeftInvariant) hbH hχb

/-- Both conclusions of VIII.4.1, unconditionally, when `χ` is nontrivial on `A_G ∩ H`. -/
theorem rationalCuspidalCentralLevel_finite_of_ne_one (H : Subgroup (rationalPoints G))
    {b : (rationalPoints.map s).range} (hbH : (b : rationalPoints G) ∈ H) (hχb : χ b ≠ 1) :
    (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H : Set (rationalPoints G → ℂ)) =
        rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H ∧
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H) := by
  rw [rationalCuspidalCentralLevelSpan_eq_bot hKc hPK ρ muA χ H hbH hχb,
    rationalCuspidalCentralLevelImage_eq_zero hKc hPK ρ muA χ H hbH hχb]
  exact ⟨Submodule.bot_coe, inferInstance⟩

end Rational

/-- The remaining case of VIII.4.1: finite dimensionality of the actual level span
when `χ` is trivial on `A_G ∩ H`. All parameters are those of
`RationalCuspidalCentralProjectionFiniteStatement`. -/
def RationalCuspidalCentralTrivialLevelFiniteStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G), IsSplitComponent s →
    ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
    ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      (∀ b : (rationalPoints.map s).range, (b : rationalPoints G) ∈ H → χ b = 1) →
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup)

/-- VIII.4.1 from closed central convergence and the trivial-character case. -/
theorem RationalCuspidalCentralTrivialLevelFiniteStatement.centralProjectionFinite
    (hconv : RationalSchwartzCentralConvergenceStatement.{u})
    (htriv : RationalCuspidalCentralTrivialLevelFiniteStatement.{u}) :
    RationalCuspidalCentralProjectionFiniteStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _ χ hχc hχu H hH
  by_cases hb : ∃ b : (rationalPoints.map s).range, (b : rationalPoints G) ∈ H ∧ χ b ≠ 1
  · obtain ⟨b, hbH, hχb⟩ := hb
    exact rationalCuspidalCentralLevel_finite_of_ne_one hKc hPK ρ muA χ H.toSubgroup hbH hχb
  · push Not at hb
    refine ⟨coe_schwartzCentralIntegralSpan_eq_image _ muA χ
      (CentralIntegralConvergesOn.mono_of_le le_top
        (hconv F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχc hχu)), ?_⟩
    exact htriv F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχc hχu H hH hb

end Langlands.HarishChandraSchwartz
