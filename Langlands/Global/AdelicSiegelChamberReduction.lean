import Langlands.Global.AdelicSiegelCoverCriteria
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Global.SplitUnipotentRationalQuotientCompact
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization

/-! # Siegel coverage from Springer's compactness and chamber reduction theorems -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- Springer's compactness theorem, sufficiency direction: if a maximal split torus of a
connected reductive group over a number field is central, a compact subset of `G(𝔸_F)¹`
meets every left coset of the principal rational points, so `G(F) \ G(𝔸_F)¹` is compact. -/
def CentralSplitCompactQuotientStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (s : S.toGrp ⟶ G),
        IsMaximalSplitTorus s → IsCentral s →
          ∃ Ω : Set (normOneSubgroup F G), IsCompact Ω ∧
            ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
              rationalNormOne F G q * g ∈ Ω

/-- The chamber form of Springer's fundamental set theorem: for every actual algebraic Siegel
setup and every maximal compact `K` with `P(𝔸_F) K = G(𝔸_F)`, there is a positive threshold
`t` such that every norm-one point has a rational left translate `n m a k` with
`n ∈ N(𝔸_F)`, `m ∈ M(𝔸_F)¹`, `a` in the weak chamber `A_{T₀}(t)` and `k ∈ K`. -/
def AdelicSiegelChamberReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          ∀ K : Subgroup (AdelicGroupPoints F G),
            IsParabolicIwasawaCompact F G
                (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K →
              ∃ t : ℝ≥0ˣ, ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
                ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
                  (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
                  (a : PositiveRealTorus.intrinsicSubgroup F T₀),
                  a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧
                    ∃ k ∈ K,
                      map F _ G (Standard.unipotentHom i ν ∅) n *
                          map F _ G (Standard.leviHom i ν ∅) m *
                          positiveMap F G T i T₀ j a * k =
                        rational F G q * g

section Factors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- Springer's compactness theorem applies to the canonical minimal Levi `M`, in which the
lift of the maximal split torus is maximal split and central. -/
theorem exists_leviCompactCover_of_setup
    (hcomp : CentralSplitCompactQuotientStatement.{u})
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ Ω : Set (normOneSubgroup F (Standard.leviScheme i ν ∅)), IsCompact Ω ∧
      ∀ m : normOneSubgroup F (Standard.leviScheme i ν ∅),
        ∃ mu : RationalGroupPoints F (Standard.leviScheme i ν ∅),
          rationalNormOne F _ mu * m ∈ Ω := by
  obtain ⟨hi, -, -, hRL, -, hlevi, -⟩ := hS
  set M := Standard.leviScheme i ν ∅
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffineHom M.X.hom := hMc.isAffineHom
  have : LocallyOfFiniteType M.X.hom := by
    have : IsClosedImmersion (Standard.leviHom i ν ∅).hom.hom.left := hMc
    rw [← Over.w (Standard.leviHom i ν ∅).hom.hom]
    infer_instance
  have hmax : IsMaximalSplitTorus (torusToStandardLevi F G T i ν) :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
      (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral (torusToStandardLevi F G T i ν) := by
    apply isCentral_of_range_le_torusCentralizer
      (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi]
  exact hcomp F M hRL.isConnectedReductive T _ hmax hcent

omit [LocallyOfFiniteType G.X.hom] in
/-- The canonical unipotent group has a compact set meeting every rational coset, by the
published compactness of unipotent rational quotients. -/
theorem exists_unipotentCompactCover_of_setup
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    HasCompactRationalCover (F := F) (Standard.unipotentScheme i ν ∅) := by
  obtain ⟨-, -, -, -, hN, -⟩ := hS
  have hN := hN.1
  have : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
    isAffine_of_isClosedSubgroup F G _ (Standard.isClosedSubgroup_unipotentHom i ν ∅)
  exact exists_isCompact_rational_mul_mem_of_split perfectFieldUnipotentSplit
    splitUnipotentAffineTorsorStatement F _ hN.smooth hN.connectedSpace hN.isUnipotent

end Factors

/-- Compactness for the minimal Levi and the chamber reduction give, for every actual setup
and every maximal compact Iwasawa subgroup `K`, compact factors with compact subgroup `K`
and a threshold satisfying the actual Siegel cover predicate. -/
theorem exists_isSiegelCover_of_chamber
    (hcomp : CentralSplitCompactQuotientStatement.{u})
    (hchamber : AdelicSiegelChamberReductionStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    ∃ (C : CompactFactors F G
        (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ),
      C.compactSubgroup = K ∧ IsSiegelCover F G T i ν T₀ j C t := by
  obtain ⟨ΩN, hΩN, hcovN⟩ := exists_unipotentCompactCover_of_setup hS
  obtain ⟨ΩM, hΩM, hcovM⟩ := exists_leviCompactCover_of_setup hcomp hS
  obtain ⟨t, ht⟩ := hchamber F G hG T i ν T₀ j hS K hK
  let C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅) :=
    ⟨ΩN, ΩM, hΩN, hΩM, K, hK.1.1⟩
  refine ⟨C, t, rfl, (hS.isSiegelCover_iff_translate F G T i ν T₀ j C t).mpr ⟨hK, ?_⟩⟩
  intro g
  obtain ⟨q, n, m, a, ha, k, hk, heq⟩ := ht g
  obtain ⟨mu, hmu⟩ := hcovM m
  set ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  set ιM := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)
  set muG : RationalGroupPoints F G :=
    (Standard.leviScheme i ν ∅).affinePointsTarget (Standard.leviHom i ν ∅)
      (CommAlgCat.of F F) mu
  have hmuG : ιM (rational F _ mu) = rational F G muG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.leviScheme i ν ∅)
      (Standard.leviHom i ν ∅)) mu).symm
  have hconj : rational F G muG * ιN n * (rational F G muG)⁻¹ ∈
      standardUnipotentImage F G T i ν := by
    have hp : rational F G muG ∈ standardParabolicImage F G T i ν :=
      standardLeviImage_le_parabolic F G T i ν ⟨rational F _ mu, hmuG⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (standardParabolicImage_le_normalizer F G T i ν hp) (ιN n)).mp ⟨n, rfl⟩
  obtain ⟨n'', hn''⟩ := hconj
  obtain ⟨_, ⟨ρ, rfl⟩, hρ⟩ := hcovN n''
  set ρG : RationalGroupPoints F G :=
    (Standard.unipotentScheme i ν ∅).affinePointsTarget (Standard.unipotentHom i ν ∅)
      (CommAlgCat.of F F) ρ
  have hρG : ιN (rational F _ ρ) = rational F G ρG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.unipotentScheme i ν ∅)
      (Standard.unipotentHom i ν ∅)) ρ).symm
  refine ⟨ρG * muG * q, ?_⟩
  refine (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ _).mpr
    ⟨rational F _ ρ * n'', hρ, rationalNormOne F _ mu * m, hmu, a, ha, k, hk, ?_⟩
  change ιN (rational F _ ρ * n'') * ιM ((rationalNormOne F _ mu * m :
      normOneSubgroup F (Standard.leviScheme i ν ∅)) : AdelicGroupPoints F _) *
    positiveMap F G T i T₀ j a * k = rational F G (ρG * muG * q) * g
  have hn''' : ιN n'' = rational F G muG * ιN n * (rational F G muG)⁻¹ := hn''
  rw [Subgroup.coe_mul, rationalNormOne_val, map_mul, map_mul, hρG, hmuG, hn''', map_mul,
    map_mul, mul_assoc (rational F G ρG * rational F G muG), ← heq]
  group

end Langlands.Global.AdelicSiegelFactors
