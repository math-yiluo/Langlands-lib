import Langlands.Global.AdelicSiegelPointTorusFactor
import Langlands.Global.AdelicWeakConstantTermChamberExtrapolation
import Langlands.Global.AdelicSiegelSetupConjugacyStatement
import Langlands.Global.AdelicWeakConstantTermLeviTemperedReduction
import Langlands.Global.AdelicLeviSiegelModulus
import Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeReduction
import Langlands.Global.AdelicSiegelConstantTermGrowth
import Langlands.Global.AdelicExponentOrbitSpan
import Langlands.Global.AdelicSiegelOrbitGrowth
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof
import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.GroupScheme.Rational.RootOrthogonalCentralizer
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # The Siegel bound for weak constant terms on the Levi, by reduction

`weakConstantTermLeviSiegelBound_of_reduction` derives `WeakConstantTermLeviSiegelBoundStatement`
(Delorme 2023, Lemma 3.8 (ii)) from `LogSquareIntegrableSiegelDerivativeBoundsStatement` and
`SiegelSetupConjugacyStatement`. The module first shows that the maximal split torus and the
generic cocharacter of a standard parabolic family give an algebraic Siegel setup of each
standard Levi `M_J`, proves the bound for that setup from the logarithmic Siegel chamber bound
on `G` (`StandardParabolicFamily.exists_leviSiegelBound_of_chamberGrowth`), and passes to an
arbitrary Siegel setup of `M_J` by rational conjugacy. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors RepresentationGrowth

section Heights

variable {F : Type} [Field F] [NumberField F]

/-- Adelic points of a composite morphism. -/
theorem map_map_apply {K H G : GroupScheme (Spec (CommRingCat.of F))} (g : K ⟶ H) (f : H ⟶ G)
    (x : AdelicGroupPoints F K) : map F H G f (map F K H g x) = map F K G (g ≫ f) x := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

/-- Left translation by a fixed point multiplies the logarithmic height
`σ(x) = 1 + log max(1, ‖x‖)` by at most a fixed factor: `σ(q x) ≤ L σ(x)`. -/
theorem exists_adelicLogHeight_mul_left_le {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho) (q : AdelicGroupPoints F G) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x : AdelicGroupPoints F G,
      adelicLogHeight F G rho (q * x) ≤ L * adelicLogHeight F G rho x := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    refine ⟨1, le_rfl, fun x => ?_⟩
    rw [Subsingleton.elim (q * x) x, one_mul]
  · set M' : ℝ := max 1 (RepresentationGrowth.adelicHeight F G rho q) with hM'
    have hM'1 : 1 ≤ M' := le_max_left _ _
    have hlogM := Real.log_nonneg hM'1
    refine ⟨1 + Real.log M', by linarith, fun x => ?_⟩
    set c₀ : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) with hc₀def
    have hc₀ : 0 < c₀ := pow_pos (by exact_mod_cast hN) _
    have hx0 := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le
    have hsn : RepresentationGrowth.adelicSourceNorm F G rho (q * x) ≤
        M' * RepresentationGrowth.adelicSourceNorm F G rho x := by
      have h1 := RepresentationGrowth.adelicHeight_mul_le F G rho hN q x
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho (q * x),
        RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x] at h1
      have h2 : c₀ * RepresentationGrowth.adelicSourceNorm F G rho (q * x) ≤
          c₀ * (M' * RepresentationGrowth.adelicSourceNorm F G rho x) := by
        calc c₀ * RepresentationGrowth.adelicSourceNorm F G rho (q * x)
            ≤ RepresentationGrowth.adelicHeight F G rho q *
                (c₀ * RepresentationGrowth.adelicSourceNorm F G rho x) := h1
          _ ≤ M' * (c₀ * RepresentationGrowth.adelicSourceNorm F G rho x) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hc₀.le hx0)
          _ = c₀ * (M' * RepresentationGrowth.adelicSourceNorm F G rho x) := by ring
      exact le_of_mul_le_mul_left h2 hc₀
    have hmax : max 1 (RepresentationGrowth.adelicSourceNorm F G rho (q * x)) ≤
        max 1 (RepresentationGrowth.adelicSourceNorm F G rho x) * M' := by
      refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hM'1) ?_
      rw [mul_comm]
      exact hsn.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
    have hpos : 0 < max 1 (RepresentationGrowth.adelicSourceNorm F G rho (q * x)) :=
      lt_max_of_lt_left one_pos
    have hpos' : 0 < max 1 (RepresentationGrowth.adelicSourceNorm F G rho x) :=
      lt_max_of_lt_left one_pos
    have hlog := Real.log_le_log hpos hmax
    rw [Real.log_mul hpos'.ne' (by linarith)] at hlog
    have hσ1 := one_le_adelicLogHeight rho x
    unfold adelicLogHeight at hσ1 ⊢
    nlinarith

end Heights

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

section LeviTorus

omit [NumberField F] in
/-- The Levi `M_J → G` of a standard parabolic is a closed subgroup. -/
theorem isClosedSubgroup_levi : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
  (fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup

omit [NumberField F] in
/-- The Levi `M_J → G` represents the standard Levi subgroup. -/
theorem isRepresentedBy_standardLevi :
    (standardLevi fam.i fam.ν J.val).IsRepresentedBy (fam.l J ≫ fam.p J) :=
  ⟨IsClosedSubgroup.mono_overHom (fam.isClosedSubgroup_levi J), (fam.isCompatible J).levi_eq⟩

omit [NumberField F] in
/-- The maximal split torus of `G` is a maximal split torus of the standard Levi `M_J`. -/
theorem isMaximalSplitTorus_torus : IsMaximalSplitTorus (fam.torus J) :=
  IsMaximalSplitTorus.of_comp (fam.isClosedSubgroup_levi J)
    (by rw [fam.torus_comp J]; exact fam.maximalSplit)

omit [NumberField F] in
/-- The generic cocharacter of the family stays generic for the standard Levi `M_J`. -/
theorem isGenericCocharacter_torus : IsGenericCocharacter (fam.torus J) fam.ν := fun α hα =>
  fam.generic α (relativeRoots_subset_of_factor (fam.isRepresentedBy_standardLevi J)
    (fam.torus J) (fam.torus_comp J) hα)

omit [NumberField F] in
/-- The simple roots in `J` are simple roots of the standard Levi `M_J`. -/
theorem subset_simpleRelativeRoots_torus : J.val ⊆ simpleRelativeRoots (fam.torus J) fam.ν := by
  obtain ⟨ζ, hζ, -, hcent⟩ := (fam.isCompatible J).realization
  have hl : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ fam.i)).IsRepresentedBy
      (fam.l J ≫ fam.p J) :=
    ⟨IsClosedSubgroup.mono_overHom (fam.isClosedSubgroup_levi J), hcent⟩
  have hsub : relativeRoots (fam.torus J) ⊆ relativeRoots fam.i :=
    relativeRoots_subset_of_factor (fam.isRepresentedBy_standardLevi J) (fam.torus J)
      (fam.torus_comp J)
  intro β hβ
  have hβG : β ∈ simpleRelativeRoots fam.i fam.ν := J.property hβ
  refine ⟨⟨mem_relativeRoots_of_pairing_eq_zero fam.i ζ hl (fam.torus J) (fam.torus_comp J)
    hβG.1.1 (hζ.2.1 β hβ), hβG.1.2⟩, ?_⟩
  rintro ⟨β₁, h₁, β₂, h₂, hsum⟩
  exact hβG.2 ⟨β₁, ⟨hsub h₁.1, h₁.2⟩, β₂, ⟨hsub h₂.1, h₂.2⟩, hsum⟩

omit [NumberField F] in
/-- The standard Levi `M_J` has an algebraic Siegel setup on the maximal split torus and the
generic cocharacter of the family. -/
theorem exists_leviSiegelAlgebraicSetup :
    ∃ (T₁ : CommGroupScheme (Spec (CommRingCat.of F))) (k : T₁ ⟶ fam.T),
      IsSiegelAlgebraicSetup F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k :=
  exists_isSiegelAlgebraicSetup (fam.isCompatible J).levi.isConnectedReductive (fam.torus J)
    (fam.isMaximalSplitTorus_torus J) fam.ν (fam.isGenericCocharacter_torus J)

end LeviTorus

section LeviBound

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "ι" => map F (fam.M J) G (fam.l J ≫ fam.p J)

/-- **The Siegel bound on the Levi for the Siegel setup of the family.** Let `ψ = ∑_{λ ∈ s} c_λ`
with unitary normalized exponents `λ` along `P = P_J` satisfy the logarithmic Siegel chamber
bound of `G`. For the algebraic Siegel setup `(T, torus_J, ν, T₁, k)` of the Levi `M = M_J` on
the maximal split torus of the family, every Siegel set of `M` and every compact `Ω' ⊆ G(𝔸)`,
there are `e` and `B` with `‖ψ(m w)‖ ≤ B δ_M(a)^{1/2} σ_M(m)^e` for every norm-one point `m` of
the Siegel set with torus coordinate `a` and every `w ∈ Ω'`.

Proof: `m = a · y` with `y` in a compact set (`exists_isCompact_siegelPoint_eq_mul`); the image
of `a` in `G(𝔸)` is a point `a_G(b)` of the Siegel torus of `G` that satisfies the chamber
inequalities of the simple roots in `J`; `exists_leviChamber_bound_of_unitaryExponents` bounds
`ψ(a_G(b) y w)`, the moduli agree (`siegelModulus_eq_levi_of_normOne`), and the logarithmic
height of `a_G(b) = m y⁻¹` is bounded by a multiple of `σ_M(m)`. -/
theorem exists_leviSiegelBound_of_chamberGrowth
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ fam.T}
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → A → ℂ)
    (hexp : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (hunit : ∀ lam ∈ s, parameterRealPart F (fam.P J) lam = 0)
    (hf : fam.HasSiegelChamberGrowth j rho (∑ lam ∈ s, c lam))
    {T₁ : CommGroupScheme (Spec (CommRingCat.of F))} {k : T₁ ⟶ fam.T}
    (hsetupM : IsSiegelAlgebraicSetup F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k)
    (C : CompactFactors F (fam.M J) (Standard.unipotentScheme (fam.torus J) fam.ν ∅)
      (Standard.leviScheme (fam.torus J) fam.ν ∅))
    (t : ℝ≥0ˣ) {Ω : Set (AdelicGroupPoints F (fam.M J))} (hΩ : IsCompact Ω)
    {Ω' : Set A} (hΩ' : IsCompact Ω') :
    ∃ (e : ℕ) (B : ℝ), ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₁)
      (m : AdelicGroupPoints F (fam.M J)),
      IsSiegelPoint F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k C t Ω a m →
      m ∈ normOneSubgroup F (fam.M J) →
      ∀ w ∈ Ω', ‖(∑ lam ∈ s, c lam) (ι m * w)‖ ≤
        B * Real.sqrt (siegelModulus F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k a) *
          adelicLogHeight F (fam.M J) (rho.restrict (fam.l J ≫ fam.p J)) m ^ e := by
  set ψ := ∑ lam ∈ s, c lam with hψ
  have hM : IsConnectedReductive (fam.M J) := (fam.isCompatible J).levi.isConnectedReductive
  have hιc : IsClosedSubgroup (fam.l J ≫ fam.p J) := fam.isClosedSubgroup_levi J
  have hρM : IsClosedSubgroup (rho.restrict (fam.l J ≫ fam.p J)) :=
    show IsClosedSubgroup ((fam.l J ≫ fam.p J) ≫ rho) from hιc.comp hrho
  obtain ⟨Y, hY, hYmem⟩ := exists_isCompact_siegelPoint_eq_mul hM hsetupM
    (rho.restrict (fam.l J ≫ fam.p J)) hρM C t hΩ
  obtain ⟨Ω'', hΩ''def⟩ : ∃ Ω'' : Set A, Ω'' = ι '' Y * Ω' := ⟨_, rfl⟩
  have hΩ'' : IsCompact Ω'' := by
    rw [hΩ''def]
    exact (hY.image (map F (fam.M J) G (fam.l J ≫ fam.p J)).continuous).mul hΩ'
  obtain ⟨e, B, hB0, hB⟩ := fam.exists_leviChamber_bound_of_unitaryExponents j rho J hδ hsetup hN
    hrho s c hexp hunit hf t hΩ''
  obtain ⟨L, hL1, hL⟩ :=
    exists_adelicLogHeight_mul_le (rho.restrict (fam.l J ≫ fam.p J)) hρM hY.inv
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ,
      c₀ = Real.log ((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀def]
    exact Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hN))
  refine ⟨e, B * (1 + c₀ + L) ^ e, fun a m hm hm1 w hw => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hYmem a m hm hm1
  obtain ⟨-, -, -, -, -, -, ha, -⟩ := hm
  set aM := positiveMap F (fam.M J) fam.T (fam.torus J) T₁ k a with haMdef
  have haM1 : aM ∈ normOneSubgroup F (fam.M J) :=
    IsSiegelAlgebraicSetup.positiveMap_mem_normOne F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k
      hsetupM a
  let tpt : PositiveRealTorus.intrinsicSubgroup F fam.T :=
    ⟨map F T₁.toGrp fam.T.toGrp (CommGroupScheme.groupHom k) a.val,
      PositiveRealTorus.map_intrinsicSubgroup_le F T₁ fam.T k ⟨a.val, a.property, rfl⟩⟩
  have hιaM : ι aM = map F fam.T.toGrp G fam.i tpt.val := by
    change map F (fam.M J) G (fam.l J ≫ fam.p J)
        (map F T₁.toGrp (fam.M J) (CommGroupScheme.groupHom k ≫ fam.torus J) a.val) =
      map F fam.T.toGrp G fam.i (map F T₁.toGrp fam.T.toGrp (CommGroupScheme.groupHom k) a.val)
    rw [map_map_apply, map_map_apply, Category.assoc, fam.torus_comp J]
  have htpt : characterLog F G (map F fam.T.toGrp G fam.i tpt.val) = 0 := by
    rw [← hιaM, characterLog_eq_zero_iff]
    exact map_normOneSubgroup_le F (fam.M J) G (fam.l J ≫ fam.p J)
      (Subgroup.mem_map_of_mem _ haM1)
  obtain ⟨b, hb⟩ := fam.exists_siegelTorus_lift_of_characterLog_eq_zero j hsetup tpt htpt
  have haGb : positiveMap F G fam.T fam.i T₀ j b = ι aM := by
    rw [hιaM]
    change map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ fam.i) b.val = _
    rw [← map_map_apply, hb]
  have hJb : ∀ β ∈ J.val,
      Real.log ((t : ℝ≥0) : ℝ) ≤ characterLog F T₀.toGrp b.val (j ≫ β) := by
    intro β hβ
    have hch := (PositiveRealTorus.mem_weakSimpleRootChamber_iff_log F T₁ fam.T k (fam.M J)
      (fam.torus J) fam.ν t a).mp ha β (fam.subset_simpleRelativeRoots_torus J hβ)
    rw [characterLog_comp, hb]
    exact hch.trans_eq (characterLog_comp k β a.val)
  have hδeq : siegelModulus F G fam.T fam.i fam.ν T₀ j b =
      siegelModulus F (fam.M J) fam.T (fam.torus J) fam.ν T₁ k a :=
    siegelModulus_eq_levi_of_normOne fam.i fam.ν fam.connectedReductive fam.maximalSplit
      fam.generic J.val J.property (fam.isRepresentedBy_standardLevi J) (fam.torus J)
      (fam.torus_comp J) j k b a hb haM1
  have hpt : ι (aM * y) * w = positiveMap F G fam.T fam.i T₀ j b * (ι y * w) := by
    rw [map_mul, haGb, mul_assoc]
  have hw' : ι y * w ∈ Ω'' := by
    rw [hΩ''def]
    exact Set.mul_mem_mul ⟨y, hy, rfl⟩ hw
  have hbound := hB b hJb (ι y * w) hw'
  -- the height of the torus point
  set σ := adelicLogHeight F (fam.M J) (rho.restrict (fam.l J ≫ fam.p J)) (aM * y) with hσdef
  have hσ1 : 1 ≤ σ := one_le_adelicLogHeight _ _
  have hHb : 1 + Real.log (adelicHeight F G rho (positiveMap F G fam.T fam.i T₀ j b)) ≤
      (1 + c₀ + L) * σ := by
    have h1 : adelicHeight F G rho (positiveMap F G fam.T fam.i T₀ j b) =
        adelicHeight F (fam.M J) (rho.restrict (fam.l J ≫ fam.p J)) aM := by
      rw [haGb, adelicHeight_map_eq_adelicHeight_comp]
      rfl
    have h2 := log_adelicHeight_le (rho.restrict (fam.l J ≫ fam.p J)) hN aM
    have h3 : adelicLogHeight F (fam.M J) (rho.restrict (fam.l J ≫ fam.p J)) aM ≤ L * σ := by
      have := hL (aM * y) y⁻¹ (Set.inv_mem_inv.mpr hy)
      rwa [mul_inv_cancel_right] at this
    rw [h1]
    rw [← hc₀def] at h2
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (adelicHeight F G rho (positiveMap F G fam.T fam.i T₀ j b)) := by
    have := Real.log_nonneg (one_le_adelicHeight F G rho hN (positiveMap F G fam.T fam.i T₀ j b))
    linarith
  rw [hpt]
  calc ‖ψ (positiveMap F G fam.T fam.i T₀ j b * (ι y * w))‖
      ≤ B * Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j b) *
          (1 + Real.log (adelicHeight F G rho (positiveMap F G fam.T fam.i T₀ j b))) ^ e :=
        hbound
    _ ≤ B * Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j b) * ((1 + c₀ + L) * σ) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hHb e)
          (mul_nonneg hB0 (Real.sqrt_nonneg _))
    _ = _ := by
        rw [hδeq, mul_pow]
        ring

end LeviBound

end StandardParabolicFamily

/-- **The Siegel bound for weak constant terms on the Levi** (Delorme 2023, Lemma 3.8 (ii)),
reduced to the logarithmic Siegel bounds of log-square-integrable automorphic forms and their
derivatives (`LogSquareIntegrableSiegelDerivativeBoundsStatement`) and to the rational conjugacy
of Siegel sets of two Siegel setups (`SiegelSetupConjugacyStatement`).

The first gives the logarithmic Siegel chamber bound of the weak constant term `ψ` on `G`
(`adelicSiegelConstantTermGrowth`, `hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan`);
`exists_leviSiegelBound_of_chamberGrowth` turns it into the bound on the Siegel sets of the Levi
for the Siegel setup of `M_J` on the maximal split torus of the family. The conjugacy statement,
applied to `M_J`, carries every Siegel set of an arbitrary setup of `M_J` into one of that setup
by a rational point `q ∈ M(F)`, which leaves `ψ` invariant, preserves the modulus, and changes
the logarithmic height `σ_M` by at most a fixed factor. For `N = 0` the group `G(𝔸)` is trivial,
the torus coordinate has modulus one, and the bound holds with `e = 0`. -/
theorem weakConstantTermLeviSiegelBound_of_reduction
    (hD : LogSquareIntegrableSiegelDerivativeBoundsStatement)
    (hC : SiegelSetupConjugacyStatement) :
    WeakConstantTermLeviSiegelBoundStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ hψ T i ν T₀ j hsetup
    C t Ω hΩ Ω' hΩ'
  have hM : IsConnectedReductive (𝓕.M J) := (𝓕.isCompatible J).levi.isConnectedReductive
  have hιc : IsClosedSubgroup (𝓕.l J ≫ 𝓕.p J) := 𝓕.isClosedSubgroup_levi J
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `G(𝔸)` is trivial
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    have hiC : IsClosedSubgroup i := hsetup.1.1.2
    have : IsAffineHom T.X.hom := hsetup.1.1.1.isAffineHom
    have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
    refine ⟨0, ‖ψ 1‖, fun a m _ _ w _ => ?_⟩
    have ht1 : PositiveRealTorus.pointMap F T₀.toGrp T.toGrp (Adeles F) (CommGroupScheme.groupHom j) a.val = 1 := by
      apply (isClosedEmbedding_map_of_isClosedSubgroup F i hiC).injective
      apply (isClosedEmbedding_map_of_isClosedSubgroup F (𝓕.l J ≫ 𝓕.p J) hιc).injective
      exact Subsingleton.elim _ _
    have hδ1 : siegelModulus F (𝓕.M J) T i ν T₀ j a = 1 := by
      unfold siegelModulus
      refine finprod_mem_of_eqOn_one fun β _ => ?_
      rw [PositiveRealTorus.normCharacter_pullback, ht1, map_one]
      simp
    rw [hδ1, Real.sqrt_one, mul_one, pow_zero, mul_one, Subsingleton.elim (_ * w) 1]
  -- the chamber growth of `ψ` on `G`
  obtain ⟨T₀G, jG, hsetupG⟩ := exists_isSiegelAlgebraicSetup 𝓕.connectedReductive 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic
  have hgrowth : 𝓕.HasSiegelChamberGrowth jG rho ψ :=
    𝓕.hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan jG rho hN J
      (adelicSiegelConstantTermGrowth hD F G 𝓕 T₀G jG hsetupG rho hN hrho K hKmax hK hsmooth hcalc
        Φ hΦ J)
      (StandardParabolicFamily.IsWeakConstantTerm.mem_splitComponentOrbitSpan 𝓕 hψ)
  -- the unitary exponent decomposition
  obtain ⟨s, c, hdec, hψeq⟩ := hψ
  obtain ⟨S, hSs, hunit, hψS⟩ : ∃ S : Finset (ComplexCharacterParameter F (𝓕.P J)), S ⊆ s ∧
      (∀ lam ∈ S, parameterRealPart F (𝓕.P J) lam = 0) ∧ ψ = ∑ lam ∈ S, c lam :=
    by
      classical
      exact ⟨s.filter (fun lam => parameterRealPart F (𝓕.P J) lam = 0), Finset.filter_subset _ _,
        fun lam h => (Finset.mem_filter.mp h).2, hψeq⟩
  have hexp : ∀ lam ∈ S, 𝓕.HasExponent J lam (c lam) := fun lam h => hdec.exponent lam (hSs h)
  -- invariance under the rational points of the Levi
  have hinv : ∀ q ∈ AdelicGroupPoints.rationalSubgroup F (𝓕.M J), ∀ g,
      ψ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) q * g) = ψ g := by
    rintro _ ⟨r, rfl⟩ g
    have hmem : map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (rational F (𝓕.M J) r) ∈
        parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J) :=
      Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨r, rfl⟩)
    rw [hψS, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun lam hlam => (hdec.automorphic lam (hSs hlam)).1 _ hmem g
  -- the Levi setup of the family and the conjugacy
  obtain ⟨T₁, k, hsetupM⟩ := 𝓕.exists_leviSiegelAlgebraicSetup J
  obtain ⟨q, hq, C', t', Ω₁, hΩ₁, hconj⟩ := hC F (𝓕.M J) hM T i ν T₀ j hsetup 𝓕.T (𝓕.torus J)
    𝓕.ν T₁ k hsetupM C t Ω hΩ
  rw [hψS] at hgrowth hinv ⊢
  obtain ⟨e, B, hB⟩ := 𝓕.exists_leviSiegelBound_of_chamberGrowth J rho
    standardNestedHalfModulusCompatibility hsetupG hN hrho S c hexp hunit hgrowth hsetupM C' t' hΩ₁
    hΩ'
  have hρM : IsClosedSubgroup (rho.restrict (𝓕.l J ≫ 𝓕.p J)) :=
    show IsClosedSubgroup ((𝓕.l J ≫ 𝓕.p J) ≫ rho) from hιc.comp hrho
  obtain ⟨L, hL1, hL⟩ := exists_adelicLogHeight_mul_left_le (rho.restrict (𝓕.l J ≫ 𝓕.p J)) hρM q
  refine ⟨e, |B| * L ^ e, fun a m hm hm1 w hw => ?_⟩
  obtain ⟨a', ha', hδ'⟩ := hconj a m hm
  have hqm1 : q * m ∈ normOneSubgroup F (𝓕.M J) :=
    (normOneSubgroup F (𝓕.M J)).mul_mem (rationalSubgroup_le_normOneSubgroup F (𝓕.M J) hq) hm1
  have h1 := hB a' (q * m) ha' hqm1 w hw
  rw [map_mul, mul_assoc, hinv q hq, hδ'] at h1
  have hσ0 : 0 ≤ adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) (q * m) :=
    zero_le_one.trans (one_le_adelicLogHeight _ _)
  calc _ ≤ B * Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
        adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) (q * m) ^ e := h1
    _ ≤ |B| * Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
        (L * adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m) ^ e := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _))
          (pow_le_pow_left₀ hσ0 (hL m) e) (pow_nonneg hσ0 e)
          (mul_nonneg (abs_nonneg B) (Real.sqrt_nonneg _))
    _ = _ := by
        rw [mul_pow]
        ring

end Langlands.Global
