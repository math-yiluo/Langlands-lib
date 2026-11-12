import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLowerBound

/-! # The upper bound of Waldspurger's Lemma II.1.1 on actual rational points (statement)

`RationalXiUpperBoundStatement`: for a connected reductive group `G` over a nonarchimedean local
field `F`, the spherical function `Ξ = rationalXi` of `RationalWeights` satisfies, for all
`g₁, g₂ ∈ G(F)`, `Ξ(g₁ a g₂) ≤ C δ₀(a)^{1/2} (1 + σ(a))^d` on the weak chamber `C_A^+` of the
split component of `M₀`, with `d` independent of `g₁, g₂` (Lemma II.1.1, in the uniform form of
the proof of Lemma II.1.2). The statement is conditional on Renard's V.5.2 simultaneous standard
basis (`SimultaneousStandardBasisAt`), an external structural input.

`RationalXiUpperBoundStatement.xiUpperBound` restates its case `g₁ = g₂ = 1` as the Library's
abstract `XiUpperBound` for the weight `iwasawaWeight` of `δ₀`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- **Waldspurger, Lemme II.1.1, upper bound** (printed p. 251), in the uniform two-sided form
established in the proof of Lemme II.1.2, on actual rational points. Let `F` be a nonarchimedean
local field and `G` a connected reductive group over `F`, with a maximal split torus
`i : S → G`, a generic cocharacter `ν` (the minimal standard parabolic `P₀ = P_∅` and its
Levi `M₀`), a compatible split component `q : A → S` of `M₀`, a compact open subgroup `K` with
`G(F) = P₀(F) K`, and a closed matrix representation `ρ`. Assume Renard's V.5.2 basis property
at some subgroup `K0` (structural input). Then there is `d ∈ ℕ` such that for all
`g₁, g₂ ∈ G(F)` there is `C` with
`Ξ(g₁ a g₂) ≤ C δ₀(a)^{1/2} (1 + σ(a))^d` for every `a` in the weak chamber `C_A^+` of `A`,
where `Ξ = rationalXi`, `δ₀ = rationalMinimalModulus` and `σ = rationalHeight ρ`. -/
def RationalXiUpperBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), SimultaneousStandardBasisAt i ν K0 →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
      IsCompatibleStandardSplitComponent i ν ∅ A q →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∃ d : ℕ, ∀ g₁ g₂ : rationalPoints G, ∃ C : ℝ,
      ∀ (a : rationalPoints G) (ha : a ∈ standardParabolicPoints i ν ∅),
        a ∈ standardComponentCAplus i ν ∅ q →
          rationalXi hKc hPK (g₁ * a * g₂) ≤
            C * (NNReal.sqrt (rationalMinimalModulus i ν ⟨a, ha⟩ : ℝ≥0) : ℝ) *
              (1 + rationalHeight (F := F) ρ a) ^ d

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The weak chamber `C_A^+` of a compatible split component of `M_J` lies in `P_J(F)`. -/
theorem mem_standardParabolicPoints_of_mem_standardComponentCAplus
    {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q) {a : rationalPoints G}
    (ha : a ∈ standardComponentCAplus i ν J q) : a ∈ standardParabolicPoints i ν J := by
  obtain ⟨x, -, rfl⟩ := ha
  exact standardLevi_le_standardParabolic i ν J _ (hA.map_mem_standardLeviPoints i ν x)

/-- The case `g₁ = g₂ = 1` of `RationalXiUpperBoundStatement` in the Library's abstract form:
`XiUpperBound Ξ σ C_A^+ φ` for `φ(p k) = δ₀(p)^{1/2}` (`iwasawaWeight`), which is `δ₀(a)^{1/2}`
on `C_A^+ ⊆ P₀(F)`. -/
theorem RationalXiUpperBoundStatement.xiUpperBound (h : RationalXiUpperBoundStatement.{u})
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν ∅ A q)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ) :
    XiUpperBound (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      (standardComponentCAplus i ν ∅ q) (iwasawaWeight hPK (rationalMinimalModulus i ν)) := by
  obtain ⟨d, hd⟩ := h F G hG S i hi ν hν K0 hbasis A q hA K hKo hKc hPK N ρ hρ
  obtain ⟨C, hC⟩ := hd 1 1
  refine ⟨C, d, fun a haC => ?_⟩
  have ha := mem_standardParabolicPoints_of_mem_standardComponentCAplus hA haC
  have hw := iwasawaWeight_mul (hPK := hPK)
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) ha K.one_mem
  rw [mul_one] at hw
  have hb := hC a ha haC
  rw [one_mul, mul_one] at hb
  rw [hw, Real.rpow_natCast]
  exact hb

end Langlands.HarishChandraSchwartz
