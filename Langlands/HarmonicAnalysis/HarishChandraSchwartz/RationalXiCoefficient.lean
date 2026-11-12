import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Jacquet.DynamicCasselmanConstantTerm

/-! # `Ξ` as a matrix coefficient of the actual `I_{P₀}^G 1`

Waldspurger defines `Ξ(g) = ⟨π(g)e, e⟩` for `(π, V) = I_{P₀}^G 1` and its `K`-fixed vector `e`
(II.1). This module realizes this on the actual rational points: for a decomposition
`P₀(F) = M₀(F) ⋉ U₀(F)` it forms the Library's normalized induction `I_{P₀}^G 1` of the trivial
character of `M₀(F)`, its vector `e_K(p k) = δ₀(p)^{1/2}` and the smooth functional
`ℓ_K(f) = ∫_K f(k) dk`, and proves `Ξ(g) = ℓ_K(π(g) e_K)`. Hence `Ξ ∈ A(I_{P₀}^G 1)`, and
`I_{P₀}^G 1` is admissible. For connected reductive `G` and generic `ν`, the decomposition and the
continuity of its projection are proved.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section General

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The trivial smooth character of a topological group. -/
def trivialSmoothCharacter : Induction.SmoothCharacter ℂ G where
  toMonoidHom := 1
  isOpen_ker := by
    rw [MonoidHom.ker_one]
    exact isOpen_univ

/-- If `G = P K` with `K` compact, then `P \ G` is compact. -/
theorem compactSpace_leftQuotient_of_isIwasawaPair [IsTopologicalGroup G] {P K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hPK : IsIwasawaPair P K) :
    CompactSpace (Induction.LeftQuotient P) := by
  refine ⟨?_⟩
  have himage : Induction.quotientMap P '' (K : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
      refine ⟨k, hk, ?_⟩
      apply Quotient.sound
      show QuotientGroup.rightRel P k (p * k)
      rw [QuotientGroup.rightRel_apply]
      simpa [mul_assoc] using hp
  rw [← himage]
  exact hKc.image (continuous_quotient_mk')

section Induced

variable [LocallyCompactSpace G] [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : Aubert.General.IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, _, 0} ℂ M)

/-- A smooth induced function of the inducing representation `p ↦ δ_P(p)^{1/2} σ(m(p))`, read as
a vector of the Library's normalized induced representation (the carriers agree by
definition). -/
def normalizedInducedOfSmoothFunctions
    (f : Induction.SmoothFunctions P (Aubert.General.inducingRepresentation h hU A)) :
    (Aubert.General.normalizedInductionFunctor h hU).obj A :=
  f

end Induced

end General

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalXiCoefficientNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- **Waldspurger's `(π, V) = I_{P₀}^G 1`** (II.1) on the actual rational points: the Library's
normalized parabolic induction `Aubert.General.normalizedInductionFunctor` along a decomposition
`P₀(F) = M₀(F) ⋉ U₀(F)` of the minimal standard parabolic, applied to the trivial character of
`M₀(F)`. Its vectors are the smooth functions `f` on `G(F)` with `f(p g) = δ₀(p)^{1/2} f(g)`,
and `G(F)` acts by right translation. -/
def rationalMinimalInduced
    (h : Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardUnipotentPoints i ν ∅)) :
    SmoothRep.{0, u, u} ℂ (rationalPoints G) :=
  (Aubert.General.normalizedInductionFunctor h (isClosed_standardUnipotentPoints i ν ∅)).obj
    (trivialSmoothCharacter (G := standardLeviPoints i ν ∅)).toSmoothRep

variable {i ν}
variable (h : Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardUnipotentPoints i ν ∅))

/-- The inducing representation of `rationalMinimalInduced`: `p ↦ δ₀(p)^{1/2}` on `ℂ`. -/
abbrev rationalMinimalInducing :
    Representation ℂ (standardParabolicPoints i ν ∅)
      (trivialSmoothCharacter (G := standardLeviPoints i ν ∅)).toSmoothRep :=
  Aubert.General.inducingRepresentation h (isClosed_standardUnipotentPoints i ν ∅)
    (trivialSmoothCharacter (G := standardLeviPoints i ν ∅)).toSmoothRep

/-- The value of a vector of `rationalMinimalInduced` at a point. -/
def rationalMinimalEval (f : rationalMinimalInduced i ν h) (g : rationalPoints G) : ℂ :=
  Induction.eval (standardParabolicPoints i ν ∅) (rationalMinimalInducing h) f g

/-- `G(F)` acts by right translation. -/
theorem rationalMinimalEval_representation (f : rationalMinimalInduced i ν h)
    (g x : rationalPoints G) :
    rationalMinimalEval h ((rationalMinimalInduced i ν h).representation g f) x =
      rationalMinimalEval h f (x * g) :=
  rfl

theorem rationalMinimalInducing_apply (p : standardParabolicPoints i ν ∅) (z : ℂ) :
    rationalMinimalInducing h p z =
      ((NNReal.sqrt (rationalMinimalModulus i ν p : ℝ≥0) : ℝ) : ℂ) * z := by
  change ((HaarModulus.closedHalfCharacter _ _ _ _ p : ℂˣ) : ℂ) •
    (((1 : standardLeviPoints i ν ∅ →* ℂˣ) (h.projection p) : ℂ) • z) = _
  simp only [MonoidHom.one_apply, Units.val_one, smul_eq_mul, one_mul,
    HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply]
  rfl

variable {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

/-- The function `e_K(p k) = δ₀(p)^{1/2}` as a smooth induced function. -/
def rationalSphericalFunction :
    Induction.SmoothFunctions (standardParabolicPoints i ν ∅) (rationalMinimalInducing h) :=
  Induction.smoothFunctionOf (standardParabolicPoints i ν ∅) (rationalMinimalInducing h)
    (fun g => ((iwasawaWeight hPK (rationalMinimalModulus i ν) g : ℝ) : ℂ))
    (by
      intro p x
      show ((iwasawaWeight hPK (rationalMinimalModulus i ν) ((p : rationalPoints G) * x) : ℝ) :
          ℂ) =
        rationalMinimalInducing h p ((iwasawaWeight hPK (rationalMinimalModulus i ν) x : ℝ) : ℂ)
      rw [rationalMinimalInducing_apply, iwasawaWeight_mul_left
        (fun q hq => rationalMinimalModulus_eq_one i ν hKo hKc q hq) p x, Complex.ofReal_mul])
    ⟨K, hKo⟩
    (by
      intro k x
      rw [iwasawaWeight_mul_right (fun q hq => rationalMinimalModulus_eq_one i ν hKo hKc q hq)
        x k.2])

/-- **Waldspurger's `K`-fixed vector `e`** (II.1) of `I_{P₀}^G 1`: the function
`e_K(p k) = δ₀(p)^{1/2}` (`iwasawaWeight`), which is right `K`-invariant with `e_K(1) = 1`. -/
def rationalSphericalVector : rationalMinimalInduced i ν h :=
  normalizedInducedOfSmoothFunctions h (isClosed_standardUnipotentPoints i ν ∅) _
    (rationalSphericalFunction h hKo hKc hPK)

theorem rationalMinimalEval_sphericalVector (g : rationalPoints G) :
    rationalMinimalEval h (rationalSphericalVector h hKo hKc hPK) g =
      ((iwasawaWeight hPK (rationalMinimalModulus i ν) g : ℝ) : ℂ) :=
  rfl

/-- `e_K(1) = 1`. -/
theorem rationalMinimalEval_sphericalVector_one :
    rationalMinimalEval h (rationalSphericalVector h hKo hKc hPK) 1 = 1 := by
  rw [rationalMinimalEval_sphericalVector,
    iwasawaWeight_of_mem (fun q hq => rationalMinimalModulus_eq_one i ν hKo hKc q hq) K.one_mem]
  simp

theorem continuous_rationalMinimalEval (f : rationalMinimalInduced i ν h) :
    Continuous (rationalMinimalEval h f) :=
  IsLocallyConstant.continuous (Induction.eval_isLocallyConstant _ _ f)

include hKc in
theorem integrable_rationalMinimalEval (f : rationalMinimalInduced i ν h) :
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    Integrable (fun k : K => rationalMinimalEval h f k) (normalizedHaar K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact ((continuous_rationalMinimalEval h f).comp
    continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The linear functional `ℓ_K(f) = ∫_K f(k) dk` on `I_{P₀}^G 1`, for the Haar probability
measure of `K`. -/
def rationalSphericalLinearFunctional : Module.Dual ℂ (rationalMinimalInduced i ν h) :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  { toFun := fun f => ∫ k : K, rationalMinimalEval h f k ∂(normalizedHaar K)
    map_add' := fun f₁ f₂ => by
      change ∫ k : K, (rationalMinimalEval h f₁ k + rationalMinimalEval h f₂ k)
          ∂(normalizedHaar K) = _
      exact integral_add (integrable_rationalMinimalEval h hKc f₁)
        (integrable_rationalMinimalEval h hKc f₂)
    map_smul' := fun c f => by
      change ∫ k : K, c • rationalMinimalEval h f k ∂(normalizedHaar K) = _
      rw [integral_smul]
      rfl }

theorem rationalSphericalLinearFunctional_apply (f : rationalMinimalInduced i ν h) :
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    rationalSphericalLinearFunctional h hKc f =
      ∫ k : K, rationalMinimalEval h f k ∂(normalizedHaar K) :=
  rfl

/-- `ℓ_K` is fixed by `K` under the contragredient action, by right invariance of the Haar
measure of the compact group `K`. -/
theorem rationalSphericalLinearFunctional_mem_fixedVectors :
    rationalSphericalLinearFunctional h hKc ∈
      fixedVectors (rationalMinimalInduced i ν h).representation.dual K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  intro k
  apply LinearMap.ext
  intro f
  change rationalSphericalLinearFunctional h hKc
    ((rationalMinimalInduced i ν h).representation (k : rationalPoints G)⁻¹ f) =
      rationalSphericalLinearFunctional h hKc f
  rw [rationalSphericalLinearFunctional_apply, rationalSphericalLinearFunctional_apply]
  have hk : (k : rationalPoints G)⁻¹ ∈ K := K.inv_mem k.2
  exact integral_mul_right_eq_self (fun k' : K => rationalMinimalEval h f k') ⟨_, hk⟩

/-- **`ℓ_K` is a smooth functional** on `I_{P₀}^G 1`. -/
def rationalSphericalFunctional :
    SmoothDual (rationalMinimalInduced i ν h).representation :=
  ⟨rationalSphericalLinearFunctional h hKc, ⟨⟨K, hKo⟩,
    rationalSphericalLinearFunctional_mem_fixedVectors h hKc⟩⟩

/-- **Waldspurger, II.1: `Ξ(g) = ⟨π(g)e, e⟩`.** For every `g ∈ G(F)`,
`Ξ(g) = ℓ_K(π(g) e_K)`, where `π = I_{P₀}^G 1`. -/
theorem rationalXi_eq_sphericalCoefficient (g : rationalPoints G) :
    ((rationalXi hKc hPK g : ℝ) : ℂ) =
      smoothDualPairing (rationalMinimalInduced i ν h).representation
        (rationalSphericalFunctional h hKo hKc)
        ((rationalMinimalInduced i ν h).representation g
          (rationalSphericalVector h hKo hKc hPK)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  change _ = ∫ k : K, rationalMinimalEval h
    ((rationalMinimalInduced i ν h).representation g (rationalSphericalVector h hKo hKc hPK)) k
      ∂(normalizedHaar K)
  unfold rationalXi xi
  rw [← integral_complex_ofReal]
  rfl

include hKo in
/-- **`Ξ ∈ A(I_{P₀}^G 1)`**: the complex-valued `Ξ` is a matrix coefficient of `I_{P₀}^G 1`. -/
theorem ofReal_rationalXi_mem_coefficientFunctionSpace :
    (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ)) ∈
      coefficientFunctionSpace (rationalMinimalInduced i ν h) := by
  have e : (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ)) =
      matrixCoefficient (rationalMinimalInduced i ν h).representation
        (rationalSphericalFunctional h hKo hKc).val (rationalSphericalVector h hKo hKc hPK) := by
    funext g
    exact rationalXi_eq_sphericalCoefficient h hKo hKc hPK g
  rw [e]
  exact matrixCoefficient_mem_coefficientFunctionSpace _ _ _

include hKc hPK in
/-- **`I_{P₀}^G 1` is admissible**, when the Levi projection of the decomposition is
continuous: `P₀(F) \ G(F)` is compact since `G(F) = P₀(F) K`. -/
theorem rationalMinimalInduced_isAdmissible (hproj : Continuous h.projection) :
    (rationalMinimalInduced i ν h).IsAdmissible := by
  have := compactSpace_leftQuotient_of_isIwasawaPair hKc hPK
  refine Aubert.General.normalizedInductionFunctor_obj_isAdmissible h _ hproj _ ?_
  refine ⟨(trivialSmoothCharacter (G := standardLeviPoints i ν ∅)).toSmoothRep.property, ?_⟩
  intro H
  have : FiniteDimensional ℂ
      (trivialSmoothCharacter (G := standardLeviPoints i ν ∅)).toSmoothRep :=
    (inferInstance : FiniteDimensional ℂ ℂ)
  exact FiniteDimensional.finiteDimensional_submodule _

end Rational

section Reductive

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a connected reductive `G`, a maximal split torus and a generic cocharacter `ν`, the actual
minimal standard parabolic is `P₀(F) = M₀(F) ⋉ U₀(F)`: by the Library's `standardCocharacter`,
`P_∅, M_∅, U_∅` are the dynamic subgroups of `ν`, whose decomposition is
`dynamic_isSemidirectDecomposition`. -/
theorem isSemidirectDecomposition_minimalStandard (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) :
    Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardUnipotentPoints i ν ∅) := by
  have := hG.isSeparated
  have := hi.isSplitSubtorus.mono
  obtain ⟨-, hcompare⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hP, hM, hU⟩ := hcompare ν (isStandardCocharacter_empty_self i ν)
  change Aubert.General.IsSemidirectDecomposition
    ((standardParabolic i ν ∅).carrier (Over.mk (𝟙 _)))
    ((standardLevi i ν ∅).carrier (Over.mk (𝟙 _)))
    ((standardUnipotent i ν ∅).carrier (Over.mk (𝟙 _)))
  rw [hP, hM, hU]
  exact Aubert.General.dynamic_isSemidirectDecomposition _ _

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- For a connected reductive `G` and generic `ν`, the Levi projection of every decomposition
`P₀(F) = M₀(F) ⋉ U₀(F)` is continuous: it is the dynamic limit map of `ν`
(`continuous_dynamic_projection`). -/
theorem continuous_projection_minimalStandard (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν)
    (h : Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardUnipotentPoints i ν ∅)) :
    Continuous h.projection := by
  have := hG.isSeparated
  have := hi.isSplitSubtorus.mono
  obtain ⟨-, hcompare⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hP, hM, hU⟩ := hcompare ν (isStandardCocharacter_empty_self i ν)
  have hc := Aubert.General.continuous_dynamic_projection F G (CommGroupScheme.groupHom ν ≫ i)
  have transport (P M U : Subgroup (rationalPoints G))
      (hP' : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) = P)
      (hM' : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) = M)
      (hU' : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) = U)
      (h' : Aubert.General.IsSemidirectDecomposition P M U) : Continuous h'.projection := by
    subst hP' hM' hU'
    exact hc
  exact transport _ _ _ (by rw [← hP]) (by rw [← hM]) (by rw [← hU]) h

variable [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsTopologicalGroup rationalWeightsT2Field
  rationalWeightsLocallyCompact rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalXiReductiveNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

/-- **`Ξ` is a coefficient of an admissible representation** (connected reductive `G`, generic
`ν`): `Ξ ∈ A(I_{P₀}^G 1)` with `I_{P₀}^G 1` admissible, for the decomposition
`isSemidirectDecomposition_minimalStandard`. -/
theorem exists_admissible_ofReal_rationalXi_mem (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    ∃ A : SmoothRep.{0, u, u} ℂ (rationalPoints G), A.IsAdmissible ∧
      (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ)) ∈ coefficientFunctionSpace A := by
  let h := isSemidirectDecomposition_minimalStandard hG hi hν
  exact ⟨rationalMinimalInduced i ν h,
    rationalMinimalInduced_isAdmissible h hKc hPK
      (continuous_projection_minimalStandard hG hi hν h),
    ofReal_rationalXi_mem_coefficientFunctionSpace h hKo hKc hPK⟩

open Filter _root_.Topology in
/-- **The constant terms of `Ξ` along the actual dynamic parabolics** (Waldspurger's
Proposition I.6.2 applied to `Ξ ∈ A(G)`, in the dynamic form of `DynamicCasselmanConstantTerm`).
For connected reductive `G`, generic `ν`, every cocharacter `χ` of `G` and every unit `t` with
`tⁿ → 0`, `Ξ` has a constant term along the powers of `χ(t)`, and it lies in `A(M)` for
`M = Z(χ)(F)`. No structural hypothesis is used. -/
theorem rationalXi_hasDynamicConstantTerm (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) :
    haveI := hG.smooth
    Jacquet.HasDynamicConstantTerm χ t (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ)) ∧
      Jacquet.IsDynamicConstantTerm χ t (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ))
        (Jacquet.dynamicConstantTerm χ t (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ))) ∧
      ∃ B : SmoothRep.{0, u, u} ℂ (Jacquet.dynamicLeviPoints χ), IsAdmissible B.representation ∧
        Jacquet.dynamicConstantTerm χ t (fun g => ((rationalXi hKc hPK g : ℝ) : ℂ)) ∈
          coefficientFunctionSpace B := by
  have := hG.smooth
  let h := isSemidirectDecomposition_minimalStandard hG hi hν
  have hA := rationalMinimalInduced_isAdmissible h hKc hPK
    (continuous_projection_minimalStandard hG hi hν h)
  exact Jacquet.dynamicConstantTerm_spec χ t ht (rationalMinimalInduced i ν h).representation hA
    (ofReal_rationalXi_mem_coefficientFunctionSpace h hKo hKc hPK)

end Reductive

end Langlands.HarishChandraSchwartz
