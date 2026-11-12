import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd

/-! # The constant term `C(G) → C(M_J)` on actual rational points (III.6, Proposition II.4.5)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P_J = M_J U_J`, this module proves the
hypotheses `ConstantTermData` and `IsConjModulus` of the Library's constant term for a Haar
measure on `U_J(F)` and the Haar modulus `δ_{U_J}`, proves that `Ξ^{M_J}` is positive, states
Proposition II.4.5 (for the opposite parabolic) on actual points
(`RationalConstantTermEstimateStatement`, conditional on Renard's structural inputs), and
defines the continuous constant term `f ↦ f^{(P_J)}` from the actual `C(G)` to the actual
`C(M_J)` from the estimate (`rationalConstantTerm`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **Cartan covering of an actual standard Levi subgroup** (the covering clause of Renard
V.5.1 (4) for `M_J`, part of V.5.1's "corresponding properties inside every standard Levi"): a
finite set `F₀` of points of the torus centralizer such that every point of `M_J(F)` lies in
some `(K0 ∩ M_J(F)) f a (K0 ∩ M_J(F))` with `f ∈ F₀` and `a` in the chamber `C_A^+` of the
simple roots `J` of `M_J`. For `J` the set of all simple roots it is `FiniteCartanCovering`. -/
abbrev StandardLeviCartanCovering (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))
    (K0 : Subgroup (rationalPoints G)) : Prop :=
  ∃ F0 : Finset (centralizerPoints i), ∀ m : rationalPoints G, m ∈ standardLeviPoints i ν J →
    ∃ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i) (a : rationalPoints S.toGrp),
      k₁ ∈ K0 ⊓ standardLeviPoints i ν J ∧ k₂ ∈ K0 ⊓ standardLeviPoints i ν J ∧ f ∈ F0 ∧
        a ∈ CocharacterUniformizer.CAplus F S J ∧
        m = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂

variable [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalConstantTermSecondCountable :
    SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalConstantTermT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalConstantTermNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

section Data

/-- **Modulus relation on `U_J(F)`**: for a Haar measure `ν_U` on `U_J(F)`, conjugation by
`m ∈ M_J(F)` scales `ν_U` by `δ_{U_J}(m)⁻¹` (the Library's `IsConjModulus`). -/
theorem rationalIsConjModulus (nuU : Measure (standardUnipotentPoints i ν J))
    [nuU.IsHaarMeasure] :
    IsConjModulus (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) nuU
      (standardUnipotentModulus i ν J) := by
  have hU := isClosed_standardUnipotentPoints i ν J
  have : LocallyCompactSpace (standardUnipotentPoints i ν J) := hU.locallyCompactSpace
  have : SecondCountableTopology (standardUnipotentPoints i ν J) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : TopologicalSpace.MetrizableSpace (standardUnipotentPoints i ν J) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  have : nuU.Regular := MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure nuU
  unfold standardUnipotentModulus
  rw [HaarModulus.closedRestrictCharacter_eq]
  exact isConjModulus_restrictCharacter _ nuU

/-- **The hypotheses `ConstantTermData`** of the Library's constant term for the actual
`P_J(F) = M_J(F) U_J(F)`, a Haar measure `ν_U` on `U_J(F)` and `δ_{U_J}`: `M_J(F)` is closed and
normalizes `U_J(F)`, and for `m` in a compact open subgroup, `δ_{U_J}(m) = 1` and conjugation
by `m` preserves `ν_U`. -/
theorem rationalConstantTermData (nuU : Measure (standardUnipotentPoints i ν J))
    [nuU.IsHaarMeasure] :
    ConstantTermData nuU (standardUnipotentModulus i ν J) := by
  have hU := isClosed_standardUnipotentPoints i ν J
  have : LocallyCompactSpace (standardUnipotentPoints i ν J) := hU.locallyCompactSpace
  have : SecondCountableTopology (standardUnipotentPoints i ν J) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : TopologicalSpace.MetrizableSpace (standardUnipotentPoints i ν J) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  have : nuU.Regular := MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure nuU
  unfold standardUnipotentModulus
  rw [HaarModulus.closedRestrictCharacter_eq]
  exact constantTermData_restrictCharacter _ (isClosed_standardLeviPoints i ν J) nuU

end Data

section Positivity

variable {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))

include hKo hKc in
/-- `δ₀^{M_J} = 1` on `P₀(F) ∩ M_J(F) ∩ K` for a compact open `K`: by `δ₀ = δ₀^{M_J} δ_{U_J}`,
since `δ₀` and `δ_{U_J}` are trivial on compact open subgroups. -/
theorem standardLeviMinimalModulusOf_eq_one (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (p : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (hp : ((p : standardLeviPoints i ν J) : rationalPoints G) ∈ K) :
    standardLeviMinimalModulusOf i ν J p = 1 := by
  have h := rationalMinimalModulus_eq_mul hG hi hν hJ
    ⟨((p : standardLeviPoints i ν J) : rationalPoints G),
      Subgroup.mem_inf.mpr ⟨p.2, (p : standardLeviPoints i ν J).2⟩⟩
  rw [rationalMinimalModulus_eq_one i ν hKo hKc _ hp,
    standardUnipotentModulus_eq_one i ν J hKo hKc _ hp, mul_one] at h
  rw [standardLeviMinimalModulusOf_apply]
  exact h.symm

include hKo in
/-- `Ξ^{M_J}` is positive. -/
theorem rationalLeviXi_pos (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (m : standardLeviPoints i ν J) : 0 < rationalLeviXi hKc hM m := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  exact xi_pos (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    (hKo.preimage continuous_subtype_val) m

end Positivity

/-- **Waldspurger, Proposition II.4.5** (printed pp. 262–263) on actual rational points, for the
opposite `P̄_J = M_J Ū_J` of a standard parabolic `P_J` (semi-standard, as allowed by the remark
on p. 263), in the form `ConstantTermEstimate` used by the Library's constant term (statement).
Let `F` be a nonarchimedean local field, `G` a connected reductive group with a maximal split
torus `i`, a generic cocharacter `ν` and `J ⊆ Δ`. Assume, for one compact open subgroup `K0`,
Renard's V.5.2 basis (`SimultaneousStandardBasisAt`) and the covering clauses of the Cartan
decompositions of `G` and of `M_J` (Renard V.5.1). Let `K` be compact open with
`G(F) = P₀(F) K` and `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`, `ρ` a closed matrix
representation and `ν_U` a Haar measure on `U_J(F)`. Then for every `d` there are `d'` and `c`
with `δ_{U_J}(m)^{1/2} ∫_{U_J} Ξ(m u) (1 + σ(m u))^{-d'} dν_U(u) ≤ c Ξ^{M_J}(m) (1 + σ(m))^{-d}`
for all `m ∈ M_J(F)`. -/
def RationalConstantTermEstimateStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 →
      StandardLeviCartanCovering F i ν J K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J)))
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure],
      ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
        (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
        (fun m => rationalHeight (F := F) ρ m)

/-- `RationalConstantTermEstimateStatement` applied to one group and one standard parabolic. -/
theorem RationalConstantTermEstimateStatement.constantTermEstimate
    (h : RationalConstantTermEstimateStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    (hLcover : StandardLeviCartanCovering F i ν J K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ)
    (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure] :
    ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m) :=
  h F G hG S i hi ν hν J hJ K0 hK0o hK0c hbasis hcover hLcover K hKo hKc hPK hM N ρ hρ nuU

section ConstantTerm

variable {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure]

include hKo in
/-- **The constant term `C(G) → C(M_J)`** (Waldspurger III.6, printed p. 272) on actual rational
points: `f ↦ f^{(P_J)}`, `f^{(P_J)}(m) = δ_{U_J}(m)^{1/2} ∫_{U_J(F)} f(m u) dν_U(u)`, as a
continuous linear map from `C(G)` (for `Ξ`, `σ`) to `C(M_J)` (for `Ξ^{M_J}` and `σ` restricted to
`M_J(F)`), given the estimate of Proposition II.4.5 (`hE`). -/
def rationalConstantTerm (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hE : ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m)) :
    RationalSchwartzSpace hKc hPK ρ →L[ℂ]
      Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) :=
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨⟨K, hKo⟩, hKc⟩⟩
  Space.constantTerm (rationalConstantTermData nuU) hE (rationalXi_pos hKo hKc hPK)
    (rationalHeight_nonneg ρ) (rationalLeviXi_pos hKo hKc hG hi hν hJ hM)
    (fun m => rationalHeight_nonneg ρ m)

/-- The value of the actual constant term: `f^{(P_J)}(m) = δ_{U_J}(m)^{1/2} ∫ f(m u) dν_U(u)`. -/
theorem coe_rationalConstantTerm (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hE : ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m))
    (f : RationalSchwartzSpace hKc hPK ρ) (m : standardLeviPoints i ν J) :
    (rationalConstantTerm hKo hKc hPK hM ρ nuU hG hi hν hJ hE f :
        standardLeviPoints i ν J → ℂ) m =
      ((NNReal.sqrt (standardUnipotentModulus i ν J m) : ℝ) : ℂ) *
        ∫ u : standardUnipotentPoints i ν J, (f : rationalPoints G → ℂ) ((m : rationalPoints G) * u)
          ∂nuU :=
  rfl

end ConstantTerm

end Langlands.HarishChandraSchwartz
