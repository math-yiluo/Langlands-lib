import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralInversion
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.HermitianSchurOrthogonality
import Langlands.Representation.Plancherel.DiscreteSeriesFormalDegree
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction
import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # The pairing of a coefficient with a wave packet (Proposition VII.2.1, `M = G`)

Waldspurger, proof of Proposition VII.2.1, case `M = G` (printed pp. 317–318): for
`ψ ∈ C^∞(O, G)` and `ψ' ∈ E' ⊗ Ě'`,
`(E^G_G ψ', f_ψ)_G = ∫_G conj((E^G_G ψ')(g)) f_ψ(g) dg = ∫_{A_G\G} conj((E^G_G ψ')(g)) ϕ(g) dg`
with `ϕ(g) = ∫_{A_G} f_ψ(a g) χ_{ω'}(a⁻¹) da`,
then `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)` by Fourier inversion over `A_G`, hence
`(E^G_G ψ', f_ψ)_G = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ', E^G_G ψ_ω)_{A_G\G}`, and by the Hermitian
Schur relations this is `0` if `ω' ∉ O` and `(ψ', ψ_{ω'})` if `ω' ∈ O`.

This module proves these steps. A generic theorem treats a wave packet `g ↦ ∫_O e(ω)(g) dω` of
functions with central characters `cc(ω)` against a function with central character `η`, given
the Fourier inversion over `A` as a hypothesis. For actual rational points, a section
`ψ` of coefficient tensors of the chosen representatives of the classes of an orbit `O` defines
the wave packet `rationalOrbitWavePacket`, the Fourier inversion is supplied by
`RationalOrbitCentralInversion`, and the Hermitian Schur relations by
`HermitianSchurOrthogonality`.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u uV

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {O : Type*} [MeasurableSpace O] (ρ : Measure O)

include hA in
/-- **The pairing of a function with central character `η` and a wave packet.** Let
`K(a g) = η(a) K(g)` and `e(ω)(a g) = cc(ω)(a) e(ω)(g)` for `a ∈ A`, and suppose that for every
`g` the Fourier inversion `∫_A η(a⁻¹) ∫_O e(ω)(g) cc(ω)(a) dω da = c ∑_{ω ∈ S} e(ω)(g)` holds
over a finite set `S`. Then for the wave packet `f(g) = ∫_O e(ω)(g) dω`,
`∫_G conj(K) f = c ∑_{ω ∈ S} ∫_{A\G} conj(K(q̇)) e(ω)(q̇) dν(q)`, with `q̇ = Quotient.out q`. -/
theorem integral_conj_mul_integral_eq_finsum [MeasurableMul A] (hν : IsCompatible A μG μA ν)
    {eta : A →* Circle} (hη : Measurable fun a => (eta a : ℂ))
    {K : G → ℂ} (hK : ∀ (a : A) (g : G), K ((a : G) * g) = (eta a : ℂ) * K g)
    {e : O → G → ℂ} {cc : O → A →* Circle}
    (he : ∀ ω (a : A) (g : G), e ω ((a : G) * g) = (cc ω a : ℂ) * e ω g)
    (hint : Integrable (fun g => conj (K g) * ∫ ω, e ω g ∂ρ) μG)
    {c : ℂ} {S : Set O} (hS : S.Finite)
    (hinv : ∀ g, ∫ a, ((eta a⁻¹ : Circle) : ℂ) * ∫ ω, e ω g * (cc ω a : ℂ) ∂ρ ∂μA =
      c * ∑ᶠ ω ∈ S, e ω g)
    (hintS : ∀ ω ∈ S, Integrable (fun q : LeftQuotient A => conj (K q.out) * e ω q.out) ν) :
    ∫ g, conj (K g) * ∫ ω, e ω g ∂ρ ∂μG =
      c * ∑ᶠ ω ∈ S, ∫ q, conj (K q.out) * e ω q.out ∂ν := by
  have hχv : ∀ a, (((Circle.toUnits.comp eta) a : ℂˣ) : ℂ) = (eta a : ℂ) := fun a => rfl
  have hχ : IsUnitaryCharacter (Circle.toUnits.comp eta) :=
    ⟨fun a => by rw [hχv, Circle.norm_coe], by simpa only [hχv] using hη⟩
  rw [← integral_centralProjection_mul_conj hA hν hχ (K := K)
    (fun a g => by rw [hK, hχv]) hint]
  have hproj : ∀ g, centralProjection μA (Circle.toUnits.comp eta)
      (fun g => ∫ ω, e ω g ∂ρ) g = c * ∑ᶠ ω ∈ S, e ω g := by
    intro g
    rw [← hinv g]
    unfold centralProjection
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [he, Units.val_inv_eq_inv_val, hχv, map_inv, Circle.coe_inv]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  simp_rw [hproj]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => by ring)
  · intro ω hω
    refine ((hintS ω (hS.mem_toFinset.mp hω)).const_mul c).congr
      (Filter.Eventually.of_forall fun q => ?_)
    ring

end Generic

section Representatives

open CategoryTheory Langlands.Plancherel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]

/-- The chosen representative `Quotient.out ω` of a discrete-series class is square integrable
modulo `A`. -/
theorem isSquareIntegrableModCentralSubgroup_out (ω : DiscreteSeriesClass.{u, uV} A hA μ) :
    IsSquareIntegrableModCentralSubgroup A hA (Quotient.out ω.val).obj.representation μ := by
  have h := ω.property
  rw [← Quotient.out_eq ω.val] at h
  exact h

theorem discreteSeriesClass_out (ω : DiscreteSeriesClass.{u, uV} A hA μ) :
    discreteSeriesClass A hA μ (Quotient.out ω.val)
      (isSquareIntegrableModCentralSubgroup_out A hA μ ω) = ω :=
  Subtype.ext (Quotient.out_eq ω.val)

/-- `A` acts on the chosen representative of `ω` by the restriction `χ_ω` of its central
character, read in `ℂˣ`. -/
theorem out_representation_central (ω : DiscreteSeriesClass.{u, uV} A hA μ) (a : A)
    (v : (Quotient.out ω.val).obj) :
    (Quotient.out ω.val).obj.representation (a : G) v =
      (((Circle.toUnits.comp (discreteSeriesCentralRestriction A hA μ A hA ω)) a : ℂˣ) : ℂ) •
        v := by
  have h := discreteSeriesUnitaryCentralCharacter_acts A hA μ (Quotient.out ω.val)
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω) ⟨a, hA a.2⟩ v
  rw [discreteSeriesClass_out] at h
  exact h

omit [IsTopologicalGroup G] in
/-- Classes whose chosen representatives are equivalent are equal. -/
theorem eq_of_out_equiv {ω₁ ω₂ : SmoothDualClass.{0, u, uV} (k := ℂ) (G := G)}
    (e : (Quotient.out ω₁).obj.representation.Equiv (Quotient.out ω₂).obj.representation) :
    ω₁ = ω₂ :=
  Quotient.out_equiv_out.mp
    ⟨(irreducibleAdmissibleProperty (k := ℂ) (G := G)).isoMk (SmoothRep.mkIso e)⟩

/-- If `χ_{ω₁} = η` on `A`, then `A` acts on the chosen representative of `ω₁` by `η`. -/
theorem out_representation_central_of_eq {ω₁ : DiscreteSeriesClass.{u, uV} A hA μ}
    {η : A →* Circle} (hη : discreteSeriesCentralRestriction A hA μ A hA ω₁ = η) (a : A)
    (v : (Quotient.out ω₁.val).obj) :
    (Quotient.out ω₁.val).obj.representation (a : G) v =
      (((Circle.toUnits.comp η) a : ℂˣ) : ℂ) • v := by
  subst hη
  exact out_representation_central A hA μ ω₁ a v

/-- The coefficients of the chosen representative of `ω` transform under `A` by `χ_ω`:
`(E ψ)(a g) = χ_ω(a) (E ψ)(g)`. -/
theorem coefficientTensorMap_out_mul (ω : DiscreteSeriesClass.{u, uV} A hA μ)
    (ψ : CoefficientTensor (Quotient.out ω.val).obj) (a : A) (g : G) :
    coefficientTensorMap _ ψ ((a : G) * g) =
      (discreteSeriesCentralRestriction A hA μ A hA ω a : ℂ) * coefficientTensorMap _ ψ g := by
  rw [← Subgroup.mem_center_iff.mp (hA a.2) g]
  exact coefficientTensorMap_mul_of_central A (out_representation_central A hA μ ω) ψ g a

end Representatives

section LeftQuotientPairing

open Langlands.Plancherel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal]
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  (μ : Measure (G ⧸ A)) {ν : Measure (LeftQuotient A)}
  (hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ)
  {χ : A →* ℂˣ} {P₁ : SmoothRep.{0, u, uV} ℂ G} {P₂ : SmoothRep.{0, u, uV} ℂ G}
  (h₁ : ∀ (a : A) (x : P₁), P₁.representation a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : P₂), P₂.representation a x = (χ a : ℂ) • x)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

omit [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] [MeasurableSpace (LeftQuotient A)]
  [BorelSpace (LeftQuotient A)] in
/-- The Hermitian integrand on `G/A` read on `A\G` through `A\G ≃ G/A`, at the chosen
representative `q.out` of `q ∈ A\G`. -/
theorem hermitianCoefficientIntegrand_normalLeftQuotientHomeomorph (ψ₂ : CoefficientTensor P₂)
    (ψ₁ : CoefficientTensor P₁) (q : LeftQuotient A) :
    hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ (normalLeftQuotientHomeomorph A q) =
      conj (coefficientTensorMap P₂ ψ₂ q.out) * coefficientTensorMap P₁ ψ₁ q.out := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

include hνμ in
/-- If `ν` on `A\G` corresponds to `μ` on `G/A`, integrability of the Hermitian integrand on
`G/A` gives integrability of `q ↦ conj((E ψ₂)(q̇)) (E ψ₁)(q̇)` on `A\G`. -/
theorem integrable_leftQuotient_of_hermitianCoefficientIntegrand (ψ₂ : CoefficientTensor P₂)
    (ψ₁ : CoefficientTensor P₁) (h : Integrable (hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁) μ) :
    Integrable (fun q : LeftQuotient A =>
      conj (coefficientTensorMap P₂ ψ₂ q.out) * coefficientTensorMap P₁ ψ₁ q.out) ν := by
  rw [← hνμ, (normalLeftQuotientHomeomorph A).measurableEmbedding.integrable_map_iff] at h
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  exact hermitianCoefficientIntegrand_normalLeftQuotientHomeomorph A h₁ h₂ hu ψ₂ ψ₁ q

include hνμ in
/-- If `ν` on `A\G` corresponds to `μ` on `G/A`, the integral over `A\G` of
`conj((E ψ₂)(q̇)) (E ψ₁)(q̇)` is the Hermitian product `(E ψ₂, E ψ₁)_{G/A}`. -/
theorem integral_leftQuotient_eq_hermitianCoefficientPairing [μ.IsHaarMeasure]
    [μ.IsInvInvariant] (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) :
    ∫ q, conj (coefficientTensorMap P₂ ψ₂ q.out) * coefficientTensorMap P₁ ψ₁ q.out ∂ν =
      hermitianCoefficientPairing A μ h₁ h₂ hu ψ₂ ψ₁ := by
  rw [hermitianCoefficientPairing, ← hνμ,
    (normalLeftQuotientHomeomorph A).measurableEmbedding.integral_map]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
    (hermitianCoefficientIntegrand_normalLeftQuotientHomeomorph A h₁ h₂ hu ψ₂ ψ₁ q).symm)

end LeftQuotientPairing

section ClassPairing

open CategoryTheory Langlands.Plancherel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {ν : Measure (LeftQuotient A)} (hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ)

include hcof hνμ in
/-- For discrete-series classes `ω₁`, `ω₂` with `χ_{ω₁} = χ_{ω₂}` on `A`, the function
`q ↦ conj((E ψ₂)(q̇)) (E ψ₁)(q̇)` on `A\G` is integrable. -/
theorem integrable_conj_mul_out {ω₁ ω₂ : DiscreteSeriesClass.{u, uV} A hA μ}
    (hω : discreteSeriesCentralRestriction A hA μ A hA ω₁ =
      discreteSeriesCentralRestriction A hA μ A hA ω₂)
    (ψ₂ : CoefficientTensor (Quotient.out ω₂.val).obj)
    (ψ₁ : CoefficientTensor (Quotient.out ω₁.val).obj) :
    Integrable (fun q : LeftQuotient A =>
      conj (coefficientTensorMap _ ψ₂ q.out) * coefficientTensorMap _ ψ₁ q.out) ν := by
  obtain ⟨b₂⟩ := isUnitarizable_of_isSquareIntegrable A hA μ
    (out_representation_central A hA μ ω₂) hcof
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω₂) (Quotient.out ω₂.val).property.1
  exact integrable_leftQuotient_of_hermitianCoefficientIntegrand A μ hνμ
    (out_representation_central_of_eq A hA μ hω) (out_representation_central A hA μ ω₂)
    (fun a => Circle.norm_coe _) ψ₂ ψ₁
    (integrable_hermitianCoefficientIntegrand A hA μ hcof _ _ _
      (isSquareIntegrableModCentralSubgroup_out A hA μ ω₁)
      (isSquareIntegrableModCentralSubgroup_out A hA μ ω₂) b₂ ψ₂ ψ₁)

include hcof hνμ in
/-- **Hermitian III.1 (2) on `A\G` for distinct classes**: if `ω₁ ≠ ω₂` and
`χ_{ω₁} = χ_{ω₂}` on `A`, then `∫_{A\G} conj((E ψ₂)(q̇)) (E ψ₁)(q̇) dν(q) = 0`. -/
theorem integral_conj_mul_out_eq_zero {ω₁ ω₂ : DiscreteSeriesClass.{u, uV} A hA μ}
    (hω : discreteSeriesCentralRestriction A hA μ A hA ω₁ =
      discreteSeriesCentralRestriction A hA μ A hA ω₂) (hne : ω₁ ≠ ω₂)
    (ψ₂ : CoefficientTensor (Quotient.out ω₂.val).obj)
    (ψ₁ : CoefficientTensor (Quotient.out ω₁.val).obj) :
    ∫ q, conj (coefficientTensorMap _ ψ₂ q.out) * coefficientTensorMap _ ψ₁ q.out ∂ν = 0 := by
  rw [integral_leftQuotient_eq_hermitianCoefficientPairing A μ hνμ
    (out_representation_central_of_eq A hA μ hω) (out_representation_central A hA μ ω₂)
    (fun a => Circle.norm_coe _)]
  exact hermitianCoefficientPairing_eq_zero A hA μ hcof _ _ _
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω₁)
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω₂) (Quotient.out ω₁.val).property.1
    (Quotient.out ω₂.val).property.1 ⟨fun e => hne (Subtype.ext (eq_of_out_equiv e))⟩ ψ₂ ψ₁

omit [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)] in
/-- The formal degree `d(ω)` of a discrete-series class is the formal degree of its chosen
representative. -/
theorem discreteSeriesFormalDegree_eq_formalDegree_out (ω : DiscreteSeriesClass.{u, uV} A hA μ) :
    discreteSeriesFormalDegree A hA μ hcof ω =
      formalDegree A hA μ (out_representation_central A hA μ ω) hcof
        (isSquareIntegrableModCentralSubgroup_out A hA μ ω) (Quotient.out ω.val).property.1 := by
  conv_lhs => rw [← discreteSeriesClass_out A hA μ ω]
  exact discreteSeriesFormalDegree_eq_formalDegree A hA μ hcof _ _
    (out_representation_central A hA μ ω)

include hνμ in
/-- **Hermitian III.1 (3) on `A\G`**: for a discrete-series class `ω` and a positive invariant
form `b` on its chosen representative,
`∫_{A\G} conj((E ψ₂)(q̇)) (E ψ₁)(q̇) dν(q) = d(ω)⁻¹ (ψ₂, ψ₁)_b`. -/
theorem integral_conj_mul_out_self (ω : DiscreteSeriesClass.{u, uV} A hA μ)
    (b : InvariantPositiveForm (Quotient.out ω.val).obj.representation)
    (ψ₂ ψ₁ : CoefficientTensor (Quotient.out ω.val).obj) :
    ∫ q, conj (coefficientTensorMap _ ψ₂ q.out) * coefficientTensorMap _ ψ₁ q.out ∂ν =
      ((discreteSeriesFormalDegree A hA μ hcof ω : ℝ) : ℂ)⁻¹ *
        (coefficientTensorInvariantForm _ hcof
          (isSquareIntegrableModCentralSubgroup_out A hA μ ω).1 b).inner ψ₂ ψ₁ := by
  rw [integral_leftQuotient_eq_hermitianCoefficientPairing A μ hνμ
    (out_representation_central A hA μ ω) (out_representation_central A hA μ ω)
    (fun a => Circle.norm_coe _), discreteSeriesFormalDegree_eq_formalDegree_out A hA μ hcof ω]
  exact hermitianCoefficientPairing_eq_inner A hA μ hcof _ _
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω) _ b ψ₂ ψ₁

end ClassPairing


section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitWavePacket1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitWavePacket2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance instRationalOrbitWavePacket3 : T2Space F := BruhatTits.localField_t2Space F
local instance instRationalOrbitWavePacket4 : T2Space (GroupScheme.rationalPoints G) :=
  rationalPoint_t2Space F G
local instance instRationalOrbitWavePacket5 :
    LocallyCompactSpace (GroupScheme.rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance instRationalOrbitWavePacket6 :
    SecondCountableTopology (GroupScheme.rationalPoints G) := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  exact (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
local instance instRationalOrbitWavePacket7 :
    Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

include hindex in
/-- The classes `ω` of the orbit `O` of `ω₀ = omega` with `χ_ω = η` on `A_G` form a finite set:
they are the images under `χ ↦ χ ω₀` of the finitely many `χ ∈ Im X(G)` with `χ χ_{ω₀} = η`
on `A_G`. -/
theorem finite_setOf_rationalOrbitCentralCharacter_eq :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      {ω | rationalOrbitCentralCharacter s hs mu omega ω = eta}.Finite := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega eta
  refine ((finite_setOf_unitaryUnramifiedCharacter_mul_eq s hs hindex
    (discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center omega)
    eta).image (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)).subset ?_
  intro ω hω
  obtain ⟨χ, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap _ _ _ _ omega).surjective ω
  have hω' : rationalOrbitCentralCharacter s hs mu omega
      (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) =
      eta := hω
  refine ⟨χ, show ∀ a, _ from fun a => ?_, rfl⟩
  rw [← rationalOrbitCentralCharacter_orbitMap s hs mu omega χ a, hω']

/-- **Fourier inversion over `A_G` with the actual central characters, in both cases**: for
`Φ` continuous on `O` and an integrable integrand,
`∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = ν(A_G ∩ G¹) ∑_{ω ∈ O ; χ_ω = η} Φ(ω)`. If `η` differs
from `χ_{ω₀}` on `A_G ∩ G¹`, both sides vanish: the sum is empty. -/
theorem integral_rationalOrbitCentralInversion_eq_finsum
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle)
      {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      Integrable (rationalOrbitInversionIntegrand s hs mu hindex omega
        (rationalOrbitCentralCharacter s hs mu omega) eta Φ) ν →
      ∫ a, rationalOrbitInversionIntegrand s hs mu hindex omega
          (rationalOrbitCentralCharacter s hs mu omega) eta Φ a ∂ν =
        ((ν (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          ∑ᶠ ω ∈ {ω | rationalOrbitCentralCharacter s hs mu omega ω = eta}, Φ ω := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ ν _ eta Φ hΦ hint
  by_cases h : ∀ b : (GroupScheme.rationalPoints.map s).range,
      (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G →
        eta b = discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
            omega b
  · exact integral_rationalOrbitCentralInversion s hs mu hindex hG omega ν eta h hΦ hint
  · push Not at h
    have hempty : {ω | rationalOrbitCentralCharacter s hs mu omega ω = eta} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
      obtain ⟨b, hb, hne⟩ := h
      obtain ⟨χ, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap _ _ _ _ omega).surjective ω
      have hω' : rationalOrbitCentralCharacter s hs mu omega
          (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) =
          eta := hω
      refine hne (Circle.ext ?_)
      rw [← hω', rationalOrbitCentralCharacter_orbitMap s hs mu omega χ b,
        unitaryUnramifiedCharacter_apply_of_mem χ hb, one_mul]
    rw [integral_rationalOrbitCentralInversion_eq_zero s hs mu hindex hG omega ν eta h hΦ,
      hempty, finsum_mem_empty, mul_zero]

/-- **The wave packet** of Waldspurger VI.3 for `M = G` on a discrete-series orbit `O` of
`ω₀ = omega`: for a section `ψ` assigning to every `ω ∈ O` a coefficient tensor of the chosen
representative of `ω`, `f_ψ(g) = ∫_O (E^G_G ψ_ω)(g) dω`, with the I.1 orbit measure
`rationalNormalizedDiscreteSeriesOrbitMeasure`. The Plancherel density `µ(ω)` of VI.3 is `1`
for `M = G`. -/
def rationalOrbitWavePacket :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) →
      GroupScheme.rationalPoints G → ℂ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega ψ g
  exact ∫ ω, coefficientTensorMap _ (ψ ω) g
    ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega

theorem rationalOrbitWavePacket_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center
        mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) (g : GroupScheme.rationalPoints G),
      rationalOrbitWavePacket s hs mu hindex omega ψ g =
        ∫ ω, coefficientTensorMap _ (ψ ω) g
          ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega := by
  intro _ _ _ _
  rfl

variable [MeasurableSpace (GroupScheme.rationalPoints G)]
  [BorelSpace (GroupScheme.rationalPoints G)]
  [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
  [BorelSpace (GroupScheme.rationalPoints.map s).range]
  [MeasurableSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]

/-- **The pairing of a coefficient with a wave packet** (proof of Proposition VII.2.1, `M = G`):
for `ψ' ∈ E' ⊗ Ě'` on the chosen representative of `ω'`,
`(E^G_G ψ', f_ψ)_G = ν_A(A_G ∩ G¹) ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ', E^G_G ψ_ω)_{A_G\G}`, with the
pairing on `A_G\G` read through the chosen representatives `q̇ = Quotient.out q`. -/
theorem integral_conj_mul_rationalOrbitWavePacket (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
        (ψ' : CoefficientTensor (Quotient.out omega'.val).obj),
      Integrable (fun g => conj (coefficientTensorMap _ ψ' g) *
        rationalOrbitWavePacket s hs mu hindex omega ψ g) μG →
      ∫ g, conj (coefficientTensorMap _ ψ' g) *
          rationalOrbitWavePacket s hs mu hindex omega ψ g ∂μG =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          ∑ᶠ ω ∈ {ω | rationalOrbitCentralCharacter s hs mu omega ω =
            discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
                omega'},
            ∫ q, conj (coefficientTensorMap _ ψ' q.out) *
              coefficientTensorMap _ (ψ ω) q.out ∂ν := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ ν hν hνμ ψ hcont hintA omega' ψ' hint
  have hηc := continuous_discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center omega'
  have hintI : ∀ g, Integrable (rationalOrbitInversionIntegrand s hs mu hindex omega
      (rationalOrbitCentralCharacter s hs mu omega)
      (discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center omega')
      (fun ω => coefficientTensorMap _ (ψ ω) g)) μA := by
    intro g
    refine ((hintA g).bdd_mul (c := 1)
      (continuous_subtype_val.comp (hηc.comp continuous_inv)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => (Circle.norm_coe _).le)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    change _ * rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g)
      = _ * ∫ ω, coefficientTensorMap _ (ψ ω) g *
      ((rationalOrbitCentralCharacter s hs mu omega ω a : Circle) : ℂ)
      ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega
    rw [rationalOrbitWavePacket_apply]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (coefficientTensorMap_out_mul _ hs.range_le_center mu ω.val (ψ ω) a g).trans (mul_comm _ _))
  exact integral_conj_mul_integral_eq_finsum hAc
    (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) hν
    (eta := discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center omega')
    (continuous_subtype_val.comp hηc).measurable
    (K := fun g => coefficientTensorMap _ ψ' g)
    (coefficientTensorMap_out_mul _ hs.range_le_center mu omega' ψ')
    (e := fun ω g => coefficientTensorMap _ (ψ ω) g)
    (cc := rationalOrbitCentralCharacter s hs mu omega)
    (fun ω a g => coefficientTensorMap_out_mul _ hs.range_le_center mu ω.val (ψ ω) a g)
    hint (finite_setOf_rationalOrbitCentralCharacter_eq s hs mu hindex omega _)
    (fun g => integral_rationalOrbitCentralInversion_eq_finsum s hs mu hindex hG omega μA _
      (hcont g) (hintI g))
    (fun ω hω => integrable_conj_mul_out _ hs.range_le_center mu CompactOpenSubgroup.cofinal hνμ
      (ω₁ := ω.val) (ω₂ := omega') hω ψ' (ψ ω))

/-- **Vanishing off the orbit** (proof of Proposition VII.2.1, `M = G`): if `ω' ∉ O`, then
`(E^G_G ψ', f_ψ)_G = 0`. -/
theorem integral_conj_mul_rationalOrbitWavePacket_eq_zero
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
        omega' ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →
      ∀ (ψ' : CoefficientTensor (Quotient.out omega'.val).obj),
      Integrable (fun g => conj (coefficientTensorMap _ ψ' g) *
        rationalOrbitWavePacket s hs mu hindex omega ψ g) μG →
      ∫ g, conj (coefficientTensorMap _ ψ' g) *
        rationalOrbitWavePacket s hs mu hindex omega ψ g ∂μG = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ ν hν hνμ ψ hcont hintA omega' homega' ψ' hint
  rw [integral_conj_mul_rationalOrbitWavePacket s hs mu hindex hG hAc omega μA μG ν hν hνμ ψ
    hcont hintA omega' ψ' hint, finsum_mem_eq_zero_of_forall_eq_zero, mul_zero]
  intro ω hω
  exact integral_conj_mul_out_eq_zero _ hs.range_le_center mu CompactOpenSubgroup.cofinal hνμ
    (ω₁ := ω.val) (ω₂ := omega') hω (fun h => homega' (by rw [← h]; exact ω.2)) ψ' (ψ ω)

/-- **The pairing on the orbit** (proof of Proposition VII.2.1, `M = G`): if `ω' ∈ O` and `b` is
a positive invariant form on the chosen representative of `ω'`, then
`(E^G_G ψ', f_ψ)_G = ν_A(A_G ∩ G¹) d(ω')⁻¹ (ψ', ψ_{ω'})_b`, where `( , )_b` is the form on
`E' ⊗ Ě'` induced by `b`. -/
theorem integral_conj_mul_rationalOrbitWavePacket_of_mem
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
        (homega' : omega' ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
        (b : InvariantPositiveForm (Quotient.out omega'.val).obj.representation)
        (ψ' : CoefficientTensor (Quotient.out omega'.val).obj),
      Integrable (fun g => conj (coefficientTensorMap _ ψ' g) *
        rationalOrbitWavePacket s hs mu hindex omega ψ g) μG →
      ∫ g, conj (coefficientTensorMap _ ψ' g) *
          rationalOrbitWavePacket s hs mu hindex omega ψ g ∂μG =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          (((discreteSeriesFormalDegree (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu CompactOpenSubgroup.cofinal omega' : ℝ) : ℂ)⁻¹ *
            (coefficientTensorInvariantForm _ CompactOpenSubgroup.cofinal
              (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1
                b).inner ψ' (ψ ⟨omega', homega'⟩)) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ ν hν hνμ ψ hcont hintA omega' homega' b ψ' hint
  have hS := finite_setOf_rationalOrbitCentralCharacter_eq s hs mu hindex omega
    (discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center omega')
  rw [integral_conj_mul_rationalOrbitWavePacket s hs mu hindex hG hAc omega μA μG ν hν hνμ ψ
    hcont hintA omega' ψ' hint, finsum_mem_eq_finite_toFinset_sum _ hS,
    Finset.sum_eq_single_of_mem ⟨omega', homega'⟩ (hS.mem_toFinset.mpr rfl)]
  · congr 1
    exact integral_conj_mul_out_self _ hs.range_le_center mu CompactOpenSubgroup.cofinal hνμ
      omega' b ψ' (ψ ⟨omega', homega'⟩)
  · intro ω hω hne
    exact integral_conj_mul_out_eq_zero _ hs.range_le_center mu CompactOpenSubgroup.cofinal hνμ
      (ω₁ := ω.val) (ω₂ := omega') (hS.mem_toFinset.mp hω) (fun h => hne (Subtype.ext h)) ψ'
      (ψ ω)

end Rational

end Langlands.HarishChandraSchwartz
