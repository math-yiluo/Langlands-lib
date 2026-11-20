import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteCoefficientConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceStatements
import Langlands.Representation.CuspidalSupport.RationalCuspidalBlockVisibility

/-! # Radical integrability of discrete-series coefficients through the III.7 cutoff -/

noncomputable section

universe u uG uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.HarishChandraSchwartz.DiscreteCoefficientCutoff

/-! ### Cutoffs on the quotient by a normal subgroup -/

section Cutoff

variable {Γ : Type uG} [Group Γ] (N : Subgroup Γ)

/-- The indicator function of one coset `q` of `N`, as a function on `Γ ⧸ N`. -/
def cosetIndicator (q : Γ ⧸ N) : Γ ⧸ N → ℂ :=
  Set.indicator {q} fun _ => 1

@[simp] theorem cosetIndicator_self (q : Γ ⧸ N) : cosetIndicator N q q = 1 := by
  simp [cosetIndicator]

/-- Inserting an element of the normal subgroup `N` in the middle does not change the coset:
`x u y N = x y N` for `u ∈ N`. -/
theorem quotient_mk_mul_mul_of_mem [N.Normal] {u : Γ} (hu : u ∈ N) (x y : Γ) :
    (QuotientGroup.mk (x * u * y) : Γ ⧸ N) = QuotientGroup.mk (x * y) := by
  rw [QuotientGroup.eq]
  have h : (x * u * y)⁻¹ * (x * y) = y⁻¹ * u⁻¹ * y⁻¹⁻¹ := by group
  rw [h]
  exact ‹N.Normal›.conj_mem _ (N.inv_mem hu) y⁻¹

/-- For an open subgroup of a topological group, the quotient is discrete, so the indicator of
one coset has compact support. -/
theorem hasCompactSupport_cosetIndicator [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hN : IsOpen (N : Set Γ)) (q : Γ ⧸ N) : HasCompactSupport (cosetIndicator N q) := by
  have : DiscreteTopology (Γ ⧸ N) := QuotientGroup.discreteTopology hN
  unfold HasCompactSupport tsupport
  rw [closure_discrete]
  exact ((Set.finite_singleton q).subset Set.support_indicator_subset).isCompact

/-- Multiplying by the indicator of the coset `x y N` does not change `f` along the
translates `x u y` with `u ∈ N`. -/
theorem mul_cosetIndicator_translate [N.Normal] (f : Γ → ℂ) {u : Γ} (hu : u ∈ N) (x y : Γ) :
    f (x * u * y) * cosetIndicator N (QuotientGroup.mk (x * y)) (QuotientGroup.mk (x * u * y)) =
      f (x * u * y) := by
  rw [quotient_mk_mul_mul_of_mem N hu, cosetIndicator_self, mul_one]

end Cutoff

/-! ### Rational points -/

section Rational

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

omit [LocallyOfFiniteType G.X.hom] in
/-- The radical of a standard parabolic lies in `G¹`: it is exhausted by compact
subgroups. -/
theorem standardUnipotentPoints_le_rationalCommonNormKernel (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    standardUnipotentPoints i ν (rootSet i ν I) ≤ rationalCommonNormKernel G :=
  CuspidalSupport.limitOfCompactSubgroups_le_rationalCommonNormKernel G _
    (standardUnipotentPoints_isLimitOfCompactSubgroups i ν (rootSet i ν I) hG
      (standardCocharacter F G hG S i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1)

/-- **Radical integrability through the III.7 cutoff.** Let `A` be square integrable modulo
`A_G(F)`, and let `U ≤ G¹` carry a measure `muU`. Assume the structural data `K0` of
Corollary III.1.2 and that every Schwartz function of the realization `C(G)` (for `K`, `ρ`)
is `muU`-integrable along every two-sided translate of `U`. Then so is every element of the
coefficient space of `A`. The proof multiplies the coefficient by the indicator of the
`G¹`-coset of `x y`; the product is a Schwartz function by III.7 and agrees with the
coefficient on `x U y`. -/
theorem integrable_coefficientTensorMap_translate (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] (ρ : MatrixRepresentation G Idx)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
    ∀ (U : Subgroup (rationalPoints G)), U ≤ rationalCommonNormKernel G →
    ∀ (muU : Measure U),
      (∀ (φ : RationalSchwartzSpace hKc hPK ρ) (x y : rationalPoints G),
        Integrable (fun v : U => (φ : rationalPoints G → ℂ) (x * v * y)) muU) →
    ∀ (t : CoefficientTensor A) (x y : rationalPoints G),
      Integrable (fun v : U => (coefficientTensorMap A t : rationalPoints G → ℂ) (x * v * y))
        muU := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq U hU muU hconv t x y
  have hD := hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable hKo hKc hPK hG hi hν hK0c
    hbasis hcover ρ hs mu A hsq
  have hc := hasCompactSupport_cosetIndicator (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G) (QuotientGroup.mk (x * y))
  have hmem := mul_mem_rationalSchwartz hKo hKc hPK ρ hD
    (f := coefficientTensorMap A t) ⟨t, rfl⟩ hc
  refine (hconv (⟨_, hmem⟩ : schwartzSubmodule _ _) x y).congr
    (Filter.Eventually.of_forall fun v => ?_)
  exact mul_cosetIndicator_translate (rationalCommonNormKernel G)
    (coefficientTensorMap A t : rationalPoints G → ℂ) (hU v.2) x y

/-- The ordinary coefficients `u ↦ ℓ(A(u) v)` are integrable on a subgroup `U ≤ G¹`, under
the hypotheses of `integrable_coefficientTensorMap_translate`. -/
theorem integrable_coefficient (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] (ρ : MatrixRepresentation G Idx)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
    ∀ (U : Subgroup (rationalPoints G)), U ≤ rationalCommonNormKernel G →
    ∀ (muU : Measure U),
      (∀ (φ : RationalSchwartzSpace hKc hPK ρ) (x y : rationalPoints G),
        Integrable (fun v : U => (φ : rationalPoints G → ℂ) (x * v * y)) muU) →
    ∀ (v : A) (ℓ : SmoothDual A.representation),
      Integrable (fun u : U => ℓ.val (A.representation (u : rationalPoints G) v)) muU := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq U hU muU hconv v ℓ
  have h := integrable_coefficientTensorMap_translate hG hi hν hK0c hbasis hcover hKo hKc hPK ρ
    hs mu A hsq U hU muU hconv (v ⊗ₜ[ℂ] ℓ) 1 1
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  change ℓ.val (A.representation (1 * u * 1) v) = ℓ.val (A.representation u v)
  rw [one_mul, mul_one]

/-- **Discrete-series coefficients are cuspidal, given the III.7 premises.** For the radical
`U` of a proper standard parabolic, with a Haar measure `muU`, assume the structural data `K0`
of Corollary III.1.2 and radical convergence for the Schwartz realization (`K`, `ρ`). Then the
coefficient space of a representation square integrable modulo `A_G(F)` lies in the
integrable cuspidal kernel of `U`. -/
theorem coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] (ρ : MatrixRepresentation G Idx)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
    ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
    ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure],
      (∀ (φ : RationalSchwartzSpace hKc hPK ρ) (x y : rationalPoints G),
        Integrable (fun v : standardUnipotentPoints i ν (rootSet i ν I) =>
          (φ : rationalPoints G → ℂ) (x * v * y)) muU) →
      coefficientFunctionSpace A ≤ integrableUnipotentCuspidalSubmodule muU := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq I hI muU _ hconv
  exact DiscreteConstantTerm.coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule
    hG hi hν hs mu A hsq I hI muU
    (integrable_coefficient hG hi hν hK0c hbasis hcover hKo hKc hPK ρ hs mu A hsq _
      (standardUnipotentPoints_le_rationalCommonNormKernel hG hi hν I) muU hconv)

/-- The same conclusion for every proper standard radical and every Haar measure on it, with
radical convergence supplied by the published all-choice statement
`RationalSchwartzConstantTermConvergenceStatement`. -/
theorem coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule_of_convergence
    (hconv : RationalSchwartzConstantTermConvergenceStatement.{u})
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
    ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
    ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure],
      coefficientFunctionSpace A ≤ integrableUnipotentCuspidalSubmodule muU := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq I hI muU _
  exact coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule hG hi hν hK0c hbasis
    hcover K.isOpen hKc hPK ρ hs mu A hsq I hI muU
    (fun φ x y => hconv F G hG S i hi ν hν K hKc hPK N ρ hρ φ I hI muU x y)

end Rational

end Langlands.HarishChandraSchwartz.DiscreteCoefficientCutoff
