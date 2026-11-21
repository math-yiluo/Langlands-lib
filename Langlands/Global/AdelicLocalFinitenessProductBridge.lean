import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Equations of `Ξ_main` from the product step of Bernstein–Lapid Lemma 8.1

The product step `aeval_prod_adelicLeftShift_constantTerm_eq_zero` gives a polynomial in a raw
left shift that kills a constant term. Here this is rewritten in the form of the constant-term
and central equations of the system `Ξ_main` (`IsTranslationPolynomialSolution` applied to
`subgroupConstantTerm` along a closed subgroup with the standard radical as image). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Shift

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

theorem adelicLeftShift_pow_apply (x : AdelicGroupPoints F G) (k : ℕ)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    (adelicLeftShift x ^ k) φ g = φ (x ^ k * g) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, adelicLeftShift_apply, ih, ← mul_assoc, ← pow_succ]

theorem aeval_adelicLeftShift_apply (x : AdelicGroupPoints F G) (D : Polynomial ℂ)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    Polynomial.aeval (adelicLeftShift x) D φ g =
      ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (x ^ k * g) := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, adelicLeftShift_pow_apply]

/-- The difference equation of `Ξ_main` is the vanishing of the polynomial in the raw shift. -/
theorem isTranslationPolynomialSolution_iff_aeval_adelicLeftShift (x : AdelicGroupPoints F G)
    (D : Polynomial ℂ) (φ : AdelicGroupPoints F G → ℂ) :
    IsTranslationPolynomialSolution x D φ ↔ Polynomial.aeval (adelicLeftShift x) D φ = 0 := by
  rw [funext_iff]
  refine forall_congr' fun g => ?_
  rw [aeval_adelicLeftShift_apply, Pi.zero_apply]

end Shift

section Congr

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The constant term along a closed subgroup depends only on its image. -/
theorem subgroupConstantTerm_congr_range {H₁ H₂ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H₁.X.left] [IsAffine H₂.X.left] (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    [IsClosedImmersion j₁.hom.hom.left] [IsClosedImmersion j₂.hom.hom.left]
    (h : SubgroupFunctor.range j₁ = SubgroupFunctor.range j₂) :
    subgroupConstantTerm F j₁ = subgroupConstantTerm F j₂ := by
  funext φ g
  unfold subgroupConstantTerm
  have key : ∀ (S₁ S₂ : SubgroupFunctor G), S₁ = S₂ →
      ∀ (c₁ : IsClosed (AdelicSubgroupPoints.adelicPoints F G S₁ : Set (AdelicGroupPoints F G)))
        (c₂ : IsClosed (AdelicSubgroupPoints.adelicPoints F G S₂ : Set (AdelicGroupPoints F G))),
      (haveI := c₁
       ∫ x, φ (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G S₁) :
          AdelicGroupPoints F G) * g)
        ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G S₁) =
      (haveI := c₂
       ∫ x, φ (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G S₂) :
          AdelicGroupPoints F G) * g)
        ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G S₂) := by
    rintro S _ rfl c₁ c₂
    rfl
  exact key _ _ h _ _

end Congr

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

/-- A closed subgroup whose image is the standard radical `U_J` gives the constant term `C_J`. -/
theorem subgroupConstantTerm_eq_constantTerm {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (u : H ⟶ G) [IsClosedImmersion u.hom.hom.left] (J : Idx)
    (hu : SubgroupFunctor.range u = standardUnipotent 𝓕.i 𝓕.ν J.1) :
    subgroupConstantTerm F u = 𝓕.constantTerm J :=
  subgroupConstantTerm_congr_range u (𝓕.iU J ≫ 𝓕.p J)
    (hu.trans (𝓕.range_radical_eq_standardUnipotent J).symm)

/-- The constant term along `G` itself is the identity. -/
theorem constantTerm_top (φ : AdelicGroupPoints F G → ℂ) : 𝓕.constantTerm 𝓕.top φ = φ := by
  funext g
  let U := SubgroupFunctor.range (𝓕.iU 𝓕.top ≫ 𝓕.p 𝓕.top)
  have hU : U = ⊥ := (𝓕.range_radical_eq_standardUnipotent 𝓕.top).trans
    (standardUnipotent_simple_eq_bot 𝓕.i 𝓕.ν)
  have : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU 𝓕.top ≫ 𝓕.p 𝓕.top)
  let := 𝓕.compactSpace_radicalRationalQuotient 𝓕.top
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure m :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  have hone : ∀ n : AdelicSubgroupPoints.adelicPoints F G U, (n : AdelicGroupPoints F G) = 1 := by
    rintro ⟨y, hy⟩
    change y ∈ U.carrier _ at hy
    rw [hU] at hy
    exact (Subgroup.mem_bot).mp hy
  unfold constantTerm subgroupConstantTerm
  change ∫ x, φ (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G U) :
    AdelicGroupPoints F G) * g) ∂m = φ g
  simp only [hone, one_mul, integral_const, probReal_univ, one_smul]

section Main

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

/-- The product step of Bernstein–Lapid Lemma 8.1, conditional on (8.1), in the form of a
constant-term equation of `Ξ_main`: for a closed subgroup `u` whose image is the standard
radical `U_P`, and `x` the image in `G(𝔸)` of a positive point `a` of `A_P`, the product of the
`D_Q` (over a finite set containing every `Q ≤ P`) is a difference equation for left translation
by `x` satisfied by the constant term of `f` along `u`. -/
theorem isTranslationPolynomialSolution_subgroupConstantTerm
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hIw : ∀ Q : Idx, IsIwasawaCompact (𝓕.p Q) K) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (P : Idx) (f : ContinuousRationalFunctions F G)
    (hf : HasModerateGrowthFunction F G rho (evaluate F G f))
    (a : 𝓕.positiveSplitComponent P) (S : Finset Idx) (hS : ∀ Q : Idx, Q ≤ P → Q ∈ S)
    (D : Idx → Polynomial ℂ)
    (hD : ∀ Q : Idx, Q ≤ P →
      Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) (D Q)
          (𝓕.constantTerm Q (evaluate F G f)) ∈
        𝓕.cuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q)
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] (u : H ⟶ G)
    [IsClosedImmersion u.hom.hom.left]
    (hu : SubgroupFunctor.range u = standardUnipotent 𝓕.i 𝓕.ν P.1)
    (x : AdelicGroupPoints F G) (hx : map F (𝓕.P P) G (𝓕.p P) a = x) :
    IsTranslationPolynomialSolution x (∏ Q ∈ S, D Q) (subgroupConstantTerm F u (evaluate F G f)) := by
  subst hx
  rw [isTranslationPolynomialSolution_iff_aeval_adelicLeftShift,
    𝓕.subgroupConstantTerm_eq_constantTerm u P hu]
  exact 𝓕.aeval_prod_adelicLeftShift_constantTerm_eq_zero rho hvan K hK hIw hN hrho P f hf a S hS
    D hD

/-- The case `P = G` of the product step, conditional on (8.1), in the form of a central
equation of `Ξ_main`: the product of the `D_Q` over a finite set containing every standard `Q`
is a difference equation for left translation by `x` satisfied by `f` itself, when `x` is the
image of a positive point of `A_G`. -/
theorem isTranslationPolynomialSolution_top
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hIw : ∀ Q : Idx, IsIwasawaCompact (𝓕.p Q) K) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (f : ContinuousRationalFunctions F G)
    (hf : HasModerateGrowthFunction F G rho (evaluate F G f))
    (a : 𝓕.positiveSplitComponent 𝓕.top) (S : Finset Idx) (hS : ∀ Q : Idx, Q ∈ S)
    (D : Idx → Polynomial ℂ)
    (hD : ∀ Q : Idx,
      Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a)) (D Q)
          (𝓕.constantTerm Q (evaluate F G f)) ∈
        𝓕.cuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q)
    (x : AdelicGroupPoints F G) (hx : map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a = x) :
    IsTranslationPolynomialSolution x (∏ Q ∈ S, D Q) (evaluate F G f) := by
  subst hx
  rw [isTranslationPolynomialSolution_iff_aeval_adelicLeftShift]
  have h := 𝓕.aeval_prod_adelicLeftShift_constantTerm_eq_zero rho hvan K hK hIw hN hrho 𝓕.top f
    hf a S (fun Q _ => hS Q) D (fun Q _ => hD Q)
  rwa [𝓕.constantTerm_top] at h

end Main

end StandardParabolicFamily

/-- The product step of Bernstein–Lapid Lemma 8.1 in the form of the constant-term equations of
`Ξ_main`, conditional on the vanishing criterion (8.1): for a closed subgroup `u` with image the
standard radical `U_P` and a positive point `a` of `A_P`, if every `D_Q(L_a)` (`Q ≤ P`) sends
`C_Q f` into the cuspidal annihilator along `Q`, then `∏_{Q ∈ S} D_Q` is a difference equation for
left translation by the image of `a`, satisfied by the constant term of `f` along `u`. -/
def ProductStepLocalFinitenessEquationStatement : Prop :=
  ParabolicCuspidalVanishingStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (𝓕 : StandardParabolicFamily F G)
    (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, IsIwasawaCompact (𝓕.p Q) K) →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
    ∀ (P : StandardIndex F G 𝓕.i 𝓕.ν) (f : ContinuousRationalFunctions F G),
      HasModerateGrowthFunction F G rho (evaluate F G f) →
    ∀ (a : 𝓕.positiveSplitComponent P) (S : Finset (StandardIndex F G 𝓕.i 𝓕.ν)),
      (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, Q ≤ P → Q ∈ S) →
    ∀ (D : StandardIndex F G 𝓕.i 𝓕.ν → Polynomial ℂ),
      (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, Q ≤ P →
        Polynomial.aeval (adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) (D Q)
            (𝓕.constantTerm Q (evaluate F G f)) ∈
          𝓕.cuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q) →
    ∀ {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] (u : H ⟶ G)
      [IsClosedImmersion u.hom.hom.left],
      SubgroupFunctor.range u = standardUnipotent 𝓕.i 𝓕.ν P.1 →
      IsTranslationPolynomialSolution (map F (𝓕.P P) G (𝓕.p P) a) (∏ Q ∈ S, D Q)
        (subgroupConstantTerm F u (evaluate F G f))

theorem productStepLocalFinitenessEquation :
    ProductStepLocalFinitenessEquationStatement.{u} :=
  fun hvan _ _ _ _ _ _ _ 𝓕 K hK hIw _ rho hN hrho P f hf a S hS D hD _ _ u _ hu =>
    𝓕.isTranslationPolynomialSolution_subgroupConstantTerm rho hvan K hK hIw hN hrho P f hf a S hS
      D hD u hu _ rfl

end Langlands.Global
