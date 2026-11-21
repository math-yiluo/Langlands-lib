import Langlands.Global.AdelicIntertwiningOperator
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Comparison of Eisenstein series and intertwining integrals by their twists -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {K L : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hL : IsIwasawaCompact p L)

/-- A pointwise finite expansion of the inducing twist gives the same expansion of the
Eisenstein series at a point where the comparison terms are summable. -/
theorem IsIwasawaCompact.eisensteinSeries_eq_finset_sum_of_twist
    {J : Type v} (s : Finset J) (a : J → ℂ) (φ : AdelicGroupPoints F G → ℂ)
    (ψ : J → AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (h : ∀ x, hK.parameterTwist φ lam x = ∑ i ∈ s, a i * hL.parameterTwist (ψ i) lam x)
    (g : AdelicGroupPoints F G) (hψ : ∀ i ∈ s, Summable (hL.eisensteinTerm (ψ i) lam g)) :
    hK.eisensteinSeries φ lam g = ∑ i ∈ s, a i * hL.eisensteinSeries (ψ i) lam g := by
  have hterm (c : ParabolicRationalCosets F p) :
      hK.eisensteinTerm φ lam g c = ∑ i ∈ s, a i * hL.eisensteinTerm (ψ i) lam g c :=
    h (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g)
  unfold eisensteinSeries
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left]
  · exact fun i hi => (hψ i hi).mul_left (a i)

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine V.X.left]

/-- The finite expansion of the inducing twist passes through the intertwining integral
when the finitely many comparison integrands are integrable on the actual rational quotient. -/
theorem IsIwasawaCompact.intertwiningIntegral_eq_finset_sum_of_twist
    {J : Type v} (s : Finset J) (a : J → ℂ) (φ : AdelicGroupPoints F G → ℂ)
    (ψ : J → AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (h : ∀ x, hK.parameterTwist φ lam x = ∑ i ∈ s, a i * hL.parameterTwist (ψ i) lam x)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (g : AdelicGroupPoints F G)
    (hψ : ∀ i ∈ s, Integrable (hL.intertwiningIntegrand iU j w (ψ i) lam g)
      (intertwiningMeasure F p iU j (innerAdelicPoint F G w))) :
    hK.intertwiningIntegral iU j w φ lam g =
      ∑ i ∈ s, a i * hL.intertwiningIntegral iU j w (ψ i) lam g := by
  unfold intertwiningIntegral
  have hintegrand (x : LeftCosetSpace
      (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))) :
      hK.intertwiningIntegrand iU j w φ lam g x =
        ∑ i ∈ s, a i * hL.intertwiningIntegrand iU j w (ψ i) lam g x :=
    h ((innerAdelicPoint F G w)⁻¹ *
      ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
        AdelicGroupPoints F G) * g)
  simp_rw [hintegrand]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · exact fun i hi => (hψ i hi).const_mul (a i)

variable {Q M M' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine Q.X.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (hQ : IsIwasawaCompact q K)
  (hQL : IsIwasawaCompact q L)

/-- Twisting the intertwining operator at the transported parameter cancels its target height. -/
theorem IsIwasawaCompact.parameterTwist_intertwiningOperator
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) :
    hQ.parameterTwist (hK.intertwiningOperator hQ iU l iV c π' w φ lam)
        (weylParameter l c π' lam) g = hK.intertwiningIntegral iU (iV ≫ q) w φ lam g := by
  simp only [parameterTwist, intertwiningOperator, heightPower, map_neg, LinearMap.neg_apply]
  rw [mul_right_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- A finite change of the source twist transports the twisted intertwining operator.
The two target height factors cancel separately. -/
theorem IsIwasawaCompact.parameterTwist_intertwiningOperator_eq_finset_sum_of_twist
    {J : Type v} (s : Finset J) (a : J → ℂ) (φ : AdelicGroupPoints F G → ℂ)
    (ψ : J → AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (h : ∀ x, hK.parameterTwist φ lam x = ∑ i ∈ s, a i * hL.parameterTwist (ψ i) lam x)
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (g : AdelicGroupPoints F G)
    (hψ : ∀ i ∈ s, Integrable (hL.intertwiningIntegrand iU (iV ≫ q) w (ψ i) lam g)
      (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))) :
    hQ.parameterTwist (hK.intertwiningOperator hQ iU l iV c π' w φ lam)
        (weylParameter l c π' lam) g =
      ∑ i ∈ s, a i * hQL.parameterTwist (hL.intertwiningOperator hQL iU l iV c π' w (ψ i) lam)
        (weylParameter l c π' lam) g := by
  simp_rw [IsIwasawaCompact.parameterTwist_intertwiningOperator]
  exact hK.intertwiningIntegral_eq_finset_sum_of_twist hL s a φ ψ lam h iU (iV ≫ q) w g hψ

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints

/-- A finite pointwise expansion of a twist transports the actual series and twisted
intertwining operator wherever the respective comparison terms converge. -/
def EisensteinTwistComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (K L : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (hL : IsIwasawaCompact p L) (hQ : IsIwasawaCompact q K) (hQL : IsIwasawaCompact q L)
    (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (J : Type v) (s : Finset J) (a : J → ℂ) (φ : AdelicGroupPoints F G → ℂ)
    (ψ : J → AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P),
    (∀ x, hK.parameterTwist φ lam x = ∑ i ∈ s, a i * hL.parameterTwist (ψ i) lam x) →
    (∀ g, (∀ i ∈ s, Summable (hL.eisensteinTerm (ψ i) lam g)) →
      hK.eisensteinSeries φ lam g = ∑ i ∈ s, a i * hL.eisensteinSeries (ψ i) lam g) ∧
    (∀ g, (∀ i ∈ s, Integrable (hL.intertwiningIntegrand iU (iV ≫ q) w (ψ i) lam g)
        (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))) →
      hQ.parameterTwist (hK.intertwiningOperator hQ iU l iV c π' w φ lam)
          (weylParameter l c π' lam) g =
        ∑ i ∈ s, a i * hQL.parameterTwist (hL.intertwiningOperator hQL iU l iV c π' w (ψ i) lam)
          (weylParameter l c π' lam) g)

theorem eisensteinTwistComparison : EisensteinTwistComparisonStatement.{u, v} := by
  intro F _ _ G P M U Q M' V _ _ _ _ p iU l q _ iV _ K L hK hL hQ hQL c π' w J s a φ ψ lam h
  exact ⟨hK.eisensteinSeries_eq_finset_sum_of_twist hL s a φ ψ lam h,
    hK.parameterTwist_intertwiningOperator_eq_finset_sum_of_twist hL hQ hQL s a φ ψ lam h
      iU l iV c π' w⟩

end Langlands.Global
