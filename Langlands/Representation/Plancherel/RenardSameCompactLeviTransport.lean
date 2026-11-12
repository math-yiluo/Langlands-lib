import Langlands.Representation.Plancherel.RenardStandardLeviParahoricData
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality

/-! # Direct Cartan transport to the fixed ambient compact Levi intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RenardCartan

section General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S) (x : B.Apartment)
  (K : Subgroup (rationalPoints G))

/-- Parahoric Cartan transports to a larger subgroup whose centralizer
intersection is the actual rational-character norm kernel. -/
theorem compactCartanComparison_of_parahoric_and_comap
    (hcartan : ParahoricCartanConclusions B ν x)
    (hPK : B.parahoricAt x ≤ K)
    (hNK : K.comap (rationalPoints.map B.centralizer.j) =
      rationalCommonNormKernel B.centralizer.Z) :
    (∀ g : rationalPoints G,
      ∃ z : dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective,
        DoubleCoset.mk K K (rationalPoints.map B.centralizer.j z.val) =
          DoubleCoset.mk K K g) ∧
    (∀ a b : dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective,
      DoubleCoset.mk K K (rationalPoints.map B.centralizer.j a.val) =
          DoubleCoset.mk K K (rationalPoints.map B.centralizer.j b.val) ↔
        b.val * a.val⁻¹ ∈ rationalCommonNormKernel B.centralizer.Z) := by
  let : B.normalizerZero.Normal := B.normal_normalizerZero
  let j := rationalPoints.map B.centralizer.j
  let N := rationalCommonNormKernel B.centralizer.Z
  let D := dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective
  have hNK' : ∀ z, j z ∈ K ↔ z ∈ N := by
    intro z
    change z ∈ K.comap j ↔ z ∈ N
    rw [hNK]
  have hNP : ∀ z ∈ N,
      j z ∈ Subgroup.normalizer (B.parahoricAt x : Set (rationalPoints G)) := by
    intro z hz
    apply B.normalizerStabilizer_mem_parahoric_normalizer {x}
      (B.centralizer.toNormalizer z)
    rw [B.mem_normalizerStabilizer]
    have hfix := B.isOmegaCompatible.smul_eq_self hz x
    simp only [Set.smul_set_singleton, hfix]
  have hcover : ∀ g : rationalPoints G, ∃ z : D,
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j z.val) =
        DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) g := by
    intro g
    have hg : g ∈ (B.parahoricAt x : Set (rationalPoints G)) *
        (j '' D) * (B.parahoricAt x : Set (rationalPoints G)) := by
      rw [← hcartan.1]
      exact Set.mem_univ g
    obtain ⟨_, ⟨p, hp, _, ⟨z, hz, rfl⟩, rfl⟩, q, hq, heq⟩ := hg
    exact ⟨⟨z, hz⟩, DoubleCoset.eq.mpr ⟨p, hp, q, hq, heq.symm⟩⟩
  have hclass : ∀ a b : D,
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j a.val) =
          DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j b.val) →
        b.val * a.val⁻¹ ∈ N := by
    intro a b hab
    exact B.zeroDatum.centralizerZero_le_rationalCommonNormKernel
      ((hcartan.2.1 a b).mp (DoubleCoset.eq''.mp hab))
  exact compactComparison_of_parahoric j (B.parahoricAt x) K N D hPK hNK' hNP
    (dominantCentralizer_mul_normKernel B ν) hcover hclass

end General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
  (hν : IsGenericCocharacter B.i ν) (J : Set (characterLattice B.S))
  (hJ : J ⊆ simpleRelativeRoots B.i ν)

local instance renardSameCompactLeviTransportInstance1 : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom

local instance renardSameCompactLeviTransportInstance2 : Mono (Standard.leviTorusHom B.i ν J).hom.hom.left :=
  mono_of_isMaximalSplitTorus
    (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)

variable (DM : KPApartmentData (Standard.leviTorusHom B.i ν J) (localFieldOrder F))
  (hres : ∀ yM : DM.Apartment, ∃ y : B.Apartment,
    Langlands.BruhatTits.SpecialCompact.IsLeviRestriction
      (Standard.leviHom B.i ν J) y yM)
  (x : B.Apartment) (xM : DM.Apartment)

local notation "BM" => standardLeviParahoricData B ν hν J hJ DM hres
local notation "KM" => B.apartment.specialCompactLeviSubgroup ν J x
local notation "CM" => standardLeviCentralizerDatum B.i B.centralizer ν J

/-- Levi parahoric Cartan, inclusion in the fixed ambient compact intersection,
and ambient compactness give the exact same-compact comparison directly. -/
theorem sameCompactLeviCartanComparison_of_parahoric
    (hcartan : ParahoricCartanConclusions BM ν xM)
    (hPK : (BM).parahoricAt xM ≤ KM)
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    SameCompactLeviCartanComparison B.apartment x ν J
      (CM).j B.centralizer.s B.centralizer.bijective := by
  exact compactCartanComparison_of_parahoric_and_comap BM ν xM KM hcartan hPK
    (specialCompactLeviCentralizer_comap B ν J x hK)

/-- The actual Levi valuation chamber parametrizes double cosets for the fixed
ambient compact intersection under the direct parahoric transport hypotheses. -/
def sameCompactLeviChamberEquiv_of_parahoric
    (hcartan : ParahoricCartanConclusions BM ν xM)
    (hPK : (BM).parahoricAt xM ≤ KM)
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    dominantValuationImage (Standard.leviTorusHom B.i ν J) ν
        B.centralizer.s B.centralizer.bijective ≃
      DoubleCoset.Quotient (KM : Set (rationalPoints (Standard.leviScheme B.i ν J))) KM :=
  sameCompactLeviChamberEquiv B.apartment x ν J (CM).j B.centralizer.s
    B.centralizer.bijective
    (sameCompactLeviCartanComparison_of_parahoric B ν hν J hJ DM hres x xM
      hcartan hPK hK)

theorem sameCompactLeviChamberEquiv_of_parahoric_value
    (hcartan : ParahoricCartanConclusions BM ν xM)
    (hPK : (BM).parahoricAt xM ≤ KM)
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G)))
    (z : dominantCentralizer (Standard.leviTorusHom B.i ν J) ν
      B.centralizer.s B.centralizer.bijective) :
    sameCompactLeviChamberEquiv_of_parahoric B ν hν J hJ DM hres x xM hcartan hPK hK
        ⟨(centralizerValuation B.centralizer.s B.centralizer.bijective).rangeRestrict z.val,
          z.property⟩ =
      DoubleCoset.mk KM KM (rationalPoints.map (CM).j z.val) :=
  sameCompactLeviChamberEquiv_value B.apartment x ν J (CM).j B.centralizer.s
    B.centralizer.bijective
    (sameCompactLeviCartanComparison_of_parahoric B ν hν J hJ DM hres x xM
      hcartan hPK hK) z

end Langlands.Plancherel.RenardCartan
