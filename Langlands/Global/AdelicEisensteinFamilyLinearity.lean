import Langlands.Global.AdelicLeviPairingExpansion
import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionStatement
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.AdelicIntertwiningAutomorphyReduction

/-! # Finite linear combinations in the cuspidal tests of convergent Eisenstein series

Elementary tools for passing from one inducing function to a finite family in the cuspidal
tests of Bernstein–Lapid §6.10: raising the degree bound and scaling a polynomial orbit, the
complex linearity of constant terms and of norm-one Levi pairings over finite sums of
integrable integrands, the continuity and rational invariance of a convergent Eisenstein series
and of a twist, and the concatenation of finitely many families of competing Weyl labels. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-! ### Polynomial orbits -/

section PolynomialOrbit

variable (J : StandardIndex F G fam.i fam.ν)

/-- A degree bound of a polynomial orbit may be raised. -/
theorem hasPolynomialOrbit_of_degree_le {lam : ComplexCharacterParameter F (fam.P J)}
    {k k' : ℕ} (hkk' : k ≤ k') {φ : AdelicGroupPoints F G → ℂ}
    (hφ : fam.HasPolynomialOrbit J lam k φ) : fam.HasPolynomialOrbit J lam k' φ := by
  intro g
  obtain ⟨p, hp, hpx⟩ := hφ g
  refine ⟨p, Submodule.span_mono ?_ hp, hpx⟩
  rintro f ⟨j, hj, ℓ, rfl⟩
  exact ⟨j, hj.trans hkk', ℓ, rfl⟩

/-- A scalar multiple of a polynomial orbit has the same exponent and degree bound. -/
theorem hasPolynomialOrbit_const_mul {lam : ComplexCharacterParameter F (fam.P J)} {k : ℕ}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : fam.HasPolynomialOrbit J lam k φ) (c : ℂ) :
    fam.HasPolynomialOrbit J lam k (fun x => c * φ x) := by
  intro g
  obtain ⟨p, hp, hpx⟩ := hφ g
  refine ⟨c • p, (polynomialFunctions _ k).smul_mem c hp, fun x hx => ?_⟩
  have h := hpx x hx
  simp only [unnormalizedAction] at h ⊢
  rw [Pi.smul_apply, smul_eq_mul, ← h, mul_assoc]

end PolynomialOrbit

/-! ### Linearity of the norm-one Levi pairing -/

section Pairing

variable (J : StandardIndex F G fam.i fam.ν)

theorem leviPairingIntegrand_finset_sum {Ω : Type*} (s : Finset Ω) (a : Ω → ℂ)
    (f : Ω → AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (ψ : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (fun x => ∑ i ∈ s, a i * f i x) g ψ =
      fun q => ∑ i ∈ s, a i * fam.leviPairingIntegrand J (f i) g ψ q := by
  funext q
  simp only [leviPairingIntegrand, Finset.sum_mul, mul_assoc]

/-- The integrand of a finite combination of functions with integrable integrands is
integrable. -/
theorem integrable_leviPairingIntegrand_finset_sum {Ω : Type*} (s : Finset Ω) (a : Ω → ℂ)
    (f : Ω → AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (ψ : AdelicGroupPoints F (fam.M J) → ℂ)
    (hint : ∀ i ∈ s, Integrable (fam.leviPairingIntegrand J (f i) g ψ)
      (normOneRationalQuotientHaarMeasure F (fam.M J))) :
    Integrable (fam.leviPairingIntegrand J (fun x => ∑ i ∈ s, a i * f i x) g ψ)
      (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
  rw [leviPairingIntegrand_finset_sum]
  exact integrable_finsetSum s fun i hi => (hint i hi).const_mul (a i)

theorem leviPairingIntegrand_const_mul (c : ℂ) (f : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (fun x => c * f x) g ψ =
      fun q => c * fam.leviPairingIntegrand J f g ψ q := by
  funext q
  simp only [leviPairingIntegrand, mul_assoc]

end Pairing

/-! ### Linearity of constant terms -/

section ConstantTerm

variable (J : StandardIndex F G fam.i fam.ν)

local notation "UJ" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "μJ" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G UJ

/-- A continuous function invariant under the rational points of `G` has an integrable
constant-term integrand along every standard parabolic. -/
theorem integrable_constantTermIntegrand_of_rationalInvariant {f : AdelicGroupPoints F G → ℂ}
    (hcont : Continuous f) (hinv : IsLeftInvariantUnder F G (rationalSubgroup F G) f)
    (g : AdelicGroupPoints F G) :
    letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G UJ : Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
    Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G UJ =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UJ) :
        AdelicGroupPoints F G) * g)) μJ := by
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G UJ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G UJ) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
      (fam.iU J ≫ fam.p J) (fam.isUnipotentRadical J).1.smooth
        (fam.isUnipotentRadical J).1.connectedSpace (fam.isUnipotentRadical J).1.isUnipotent
  let : IsProbabilityMeasure μJ :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G UJ
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G UJ) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G UJ
  let l := LeftCosetSpace.lift (AdelicSubgroupPoints.rationalSubgroup F G UJ)
    (fun x : AdelicSubgroupPoints.adelicPoints F G UJ => f ((x : AdelicGroupPoints F G) * g))
    (fun x y => by
      change f (((x.val : AdelicGroupPoints F G) * y.val) * g) = f (y.val * g)
      rw [mul_assoc]
      exact hinv _ (rationalImage_le_rationalSubgroup _
        ((mem_rationalSubgroup_range_iff _ x.val).mp x.2)) _)
  have hl : Continuous l :=
    (LeftCosetSpace.continuous_iff (AdelicSubgroupPoints.rationalSubgroup F G UJ)).mpr
      (hcont.comp (continuous_subtype_val.mul continuous_const))
  have heq : (fun q : AdelicSubgroupPoints.RationalQuotient F G UJ =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UJ) :
        AdelicGroupPoints F G) * g)) = l := by
    funext q
    exact congrArg l (Quotient.out_eq q)
  rw [heq]
  exact hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The constant term is linear on finite combinations of functions whose constant-term
integrands are integrable. -/
theorem constantTerm_finset_sum {Ω : Type*} (s : Finset Ω) (a : Ω → ℂ)
    (f : Ω → AdelicGroupPoints F G → ℂ)
    (hint : ∀ i ∈ s, ∀ g : AdelicGroupPoints F G,
      letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G UJ : Set (AdelicGroupPoints F G)) :=
        AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
      Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G UJ =>
        f i (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UJ) :
          AdelicGroupPoints F G) * g)) μJ) :
    fam.constantTerm J (fun x => ∑ i ∈ s, a i * f i x) =
      fun g => ∑ i ∈ s, a i * fam.constantTerm J (f i) g := by
  funext g
  unfold constantTerm subgroupConstantTerm
  rw [integral_finsetSum s fun i hi => (hint i hi g).const_mul (a i)]
  simp only [integral_const_mul]

/-- The parabolic constant term is linear on finite combinations of functions whose
constant-term integrands along `J` are integrable. -/
theorem parabolicConstantTerm_finset_sum (P : StandardIndex F G fam.i fam.ν) {Ω : Type*}
    (s : Finset Ω) (a : Ω → ℂ) (f : Ω → AdelicGroupPoints F G → ℂ)
    (hint : J ≤ P → ∀ i ∈ s, ∀ g : AdelicGroupPoints F G,
      letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G UJ : Set (AdelicGroupPoints F G)) :=
        AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
      Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G UJ =>
        f i (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UJ) :
          AdelicGroupPoints F G) * g)) μJ) :
    fam.parabolicConstantTerm P J (fun x => ∑ i ∈ s, a i * f i x) =
      fun g => ∑ i ∈ s, a i * fam.parabolicConstantTerm P J (f i) g := by
  classical
  unfold parabolicConstantTerm
  by_cases hJP : J ≤ P
  · simp only [hJP, ↓reduceIte]
    exact fam.constantTerm_finset_sum J s a f (hint hJP)
  · simp only [hJP, ↓reduceIte, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rfl

end ConstantTerm

/-! ### Continuity and invariance of convergent series and twists -/

section Series

variable (I : StandardIndex F G fam.i fam.ν) [IsClosedImmersion (fam.p I).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p I) K)

/-- A twist is invariant under `U_I(𝔸) M_I(F)` when the twisted function is. -/
theorem isLeftInvariantUnder_parameterTwist {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
      (hK.parameterTwist φ lam) := by
  have hU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I))
      (hK.heightPower lam) := by
    rintro _ ⟨y, rfl⟩ g
    exact hK.heightPower_unipotent_mul (fam.isUnipotentRadical I).1.isUnipotent (fam.iU I)
      lam y g
  have hM : IsLeftInvariantUnder F G (parabolicLeviRationalImage F (fam.p I) (fam.l I))
      (hK.heightPower lam) := by
    rintro _ ⟨y, rfl⟩ g
    change hK.heightPower lam (map F (fam.M I) G (fam.l I ≫ fam.p I) (rational F (fam.M I) y) *
      g) = _
    rw [map_comp_apply_of_hom, map_rational_eq_rational]
    exact hK.heightPower_rational_mul lam _ g
  intro x hx g
  unfold IsIwasawaCompact.parameterTwist
  rw [hφ x hx g, isLeftInvariantUnder_sup hU hM x hx g]

/-- A twist of an automorphic inducing function has an integrable constant-term integrand along
every smaller standard parabolic. -/
theorem integrable_constantTermIntegrand_parameterTwist (J : StandardIndex F G fam.i fam.ν)
    (hJI : J ≤ I) {φ : AdelicGroupPoints F G → ℂ} (hcont : Continuous φ)
    (hφ : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (lam : ComplexCharacterParameter F (fam.P I)) (g : AdelicGroupPoints F G) :
    letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (fam.iU J ≫ fam.p J)) : Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
    Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (fam.iU J ≫ fam.p J)) =>
      hK.parameterTwist φ lam (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) : AdelicGroupPoints F G) * g))
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
        (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) :=
  fam.integrable_constantTermIntegrand_of_le I J hJI (hK.continuous_parameterTwist hcont lam)
    (fam.isLeftInvariantUnder_parameterTwist I hK hφ lam) g

/-- A series of continuous terms dominated on every compact set by a summable sequence is
continuous. -/
theorem continuous_eisensteinSeries_of_compactBound {φ : AdelicGroupPoints F G → ℂ}
    (hcont : Continuous φ) (lam : ComplexCharacterParameter F (fam.P I))
    (hb : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ b : ParabolicRationalCosets F (fam.p I) → ℝ, Summable b ∧
        ∀ c, ∀ g ∈ C, ‖hK.eisensteinTerm φ lam g c‖ ≤ b c) :
    Continuous (hK.eisensteinSeries φ lam) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨b, hbs, hb⟩ := hb C hC
  have hterm : ∀ c, Continuous fun g => hK.eisensteinTerm φ lam g c := fun c =>
    (hK.continuous_parameterTwist hcont lam).comp (continuous_const.mul continuous_id)
  have hon : ContinuousOn (hK.eisensteinSeries φ lam) C :=
    continuousOn_tsum (fun c => (hterm c).continuousOn) hbs fun c g hg => hb c g hg
  exact hon.continuousAt hCx

end Series

end StandardParabolicFamily

/-! ### Concatenating competing Weyl labels -/

section Labels

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {I J : StandardIndex F G fam.i fam.ν}
  {selected : relativeWeylGroup fam.i}

theorem CompetingWeylExponents.sigma_label_index {m : ℕ}
    (data : Fin m → CompetingWeylExponents fam I J selected)
    (k : Fin (CompetingWeylExponents.sigma data).size)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    (CompetingWeylExponents.sigma data).label k lam =
      (data (finSigmaFinEquiv.symm k).1).label (finSigmaFinEquiv.symm k).2 lam :=
  rfl

end Labels

end Langlands.Global
