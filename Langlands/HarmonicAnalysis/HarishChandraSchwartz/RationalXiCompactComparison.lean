import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactModularComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme

/-! # Compact subgroup comparison of actual ambient and Levi spherical functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

/-- The actual spherical functions for two compact open Iwasawa factors are comparable. -/
theorem exists_rationalXi_le_mul_rationalXi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K L : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hLo : IsOpen (L : Set (rationalPoints G))) (hLc : IsCompact (L : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) L) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      rationalXi hKc hPK g ≤ C * rationalXi hLc hPL g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  have hP := isClosed_standardParabolicPoints_empty hG hi hν
  have : LocallyCompactSpace (standardParabolicPoints i ν ∅) := hP.locallyCompactSpace
  exact exists_xi_le_mul_xi (rationalPoints_modularCharacter_eq_one hG) hP hKo hLo
    (rationalMinimalModulus_eq_modularCharacter hG hi hν)

/-- Intrinsic Levi transport gives the same comparison for the actual Levi spherical functions. -/
theorem exists_rationalLeviXi_le_mul_rationalLeviXi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {K L : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hLo : IsOpen (L : Set (rationalPoints G))) (hLc : IsCompact (L : Set (rationalPoints G)))
    (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (hML : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (L.subgroupOf (standardLeviPoints i ν J))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : standardLeviPoints i ν J,
      rationalLeviXi hKc hMK m ≤ C * rationalLeviXi hLc hML m := by
  let := leviScheme_isAffineHom i ν J
  let := leviScheme_locallyOfFiniteType i ν J
  obtain ⟨C, hC, h⟩ := exists_rationalXi_le_mul_rationalXi
    (Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (isGenericCocharacter_leviTorusHom hν)
    (isOpen_leviSchemeCompact hKo) (isCompact_leviSchemeCompact hKc)
    (isOpen_leviSchemeCompact hLo) (isCompact_leviSchemeCompact hLc)
    (isIwasawaPair_leviSchemeCompact hG hi hν hJ hMK)
    (isIwasawaPair_leviSchemeCompact hG hi hν hJ hML)
  refine ⟨C, hC, fun m => ?_⟩
  have hm := h ((leviSchemePointsEquiv i ν J).symm m)
  rw [rationalXi_leviScheme hG hi hν hJ hKo hKc hMK,
    rationalXi_leviScheme hG hi hν hJ hLo hLc hML,
    ContinuousMulEquiv.apply_symm_apply] at hm
  exact hm

/-- Uniform comparison of ambient and standard Levi spherical functions on actual points. -/
def RationalXiCompactComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ K L : Subgroup (rationalPoints G),
      IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G))),
      IsOpen (L : Set (rationalPoints G)) →
    ∀ (hLc : IsCompact (L : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) L)
      (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J)))
      (hML : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (L.subgroupOf (standardLeviPoints i ν J))),
      (∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
        rationalXi hKc hPK g ≤ C * rationalXi hLc hPL g) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ m : standardLeviPoints i ν J,
        rationalLeviXi hKc hMK m ≤ C * rationalLeviXi hLc hML m)

/-- The actual-point compact comparison, including the intrinsic standard Levi comparison. -/
theorem rationalXiCompactComparison : RationalXiCompactComparisonStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ K L hKo hKc hLo hLc hPK hPL hMK hML
  exact ⟨exists_rationalXi_le_mul_rationalXi hG hi hν hKo hKc hLo hLc hPK hPL,
    exists_rationalLeviXi_le_mul_rationalLeviXi hG hi hν hJ hKo hKc hLo hLc hMK hML⟩

end Langlands.HarishChandraSchwartz
