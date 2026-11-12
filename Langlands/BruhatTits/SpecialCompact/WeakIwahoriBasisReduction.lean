import Langlands.BruhatTits.SpecialCompact.StrictChamberPowerBasis
import Langlands.BruhatTits.SpecialCompact.UniformChamberConsequences
import Langlands.BruhatTits.SpecialCompact.CompatibleComponent
import Langlands.BruhatTits.SpecialCompact.InheritedNormalBasis
import Langlands.Representation.Jacquet.StandardCentralContraction

/-! # The remaining common normal weak-Iwahori basis construction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- One actual compatible split component for each standard face, before
any compact open subgroup is chosen. -/
structure StandardSplitComponentFamily where
  torus : ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    CommGroupScheme (Spec (CommRingCat.of F))
  hom : ∀ J hJ, (torus J hJ).toGrp ⟶ S.toGrp
  compatible : ∀ J hJ, IsCompatibleStandardSplitComponent i ν J (torus J hJ) (hom J hJ)

/-- Choose compatible components independently of every compact-open basis
member, using the published standard-Levi split-component construction. -/
def standardSplitComponentFamily
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : StandardSplitComponentFamily i ν where
  torus J hJ := (exists_compatibleStandardSplitComponent hG i hi ν hν J hJ).choose
  hom J hJ := (exists_compatibleStandardSplitComponent hG i hi ν hν J hJ).choose_spec.choose
  compatible J hJ :=
    (exists_compatibleStandardSplitComponent hG i hi ν hν J hJ).choose_spec.choose_spec

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

local instance weakIwahoriBasisReductionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance weakIwahoriBasisReductionTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Actual component points fix every Levi element under conjugation, so
they normalize every literal Levi intersection. -/
theorem IsCompatibleStandardSplitComponent.leviIntersectionNormalization
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (K : Subgroup (rationalPoints G)) :
    LeviIntersectionNormalization K (standardLeviPoints i ν J)
      (standardComponentCA i q : Set (rationalPoints G)) := by
  rintro m ⟨t, _, rfl⟩
  have hfix (y : rationalPoints G) (hy : y ∈ standardLeviPoints i ν J) :
      rationalPoints.map (q ≫ i) t * y * (rationalPoints.map (q ≫ i) t)⁻¹ = y := by
    rw [← hA.map_commute_standardLeviPoints i ν t hy]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change rationalPoints.map (q ≫ i) t * y * (rationalPoints.map (q ≫ i) t)⁻¹ ∈
      (K ⊓ standardLeviPoints i ν J : Subgroup (rationalPoints G))
    rw [hfix y hy.2]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx.2⟩

/-- For compact open `K`, weak-chamber preservation is the only additional
contraction clause: normalization and all four power/uniform clauses follow. -/
theorem IsCompatibleStandardSplitComponent.contractionAndCofinality_of_weak
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (K : Subgroup (rationalPoints G))
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hweak : WeakChamberContraction K (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) (standardComponentCAplus i ν J q)) :
    ContractionAndCofinality K (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)
      (standardComponentCA i q : Set (rationalPoints G))
      (standardComponentCAplus i ν J q) (standardComponentCAstrict i ν J q)
      (standardComponentCAepsilon i ν J q) := by
  have hp := hA.strictChamber_power_basis_and_exhaustion i ν hG hi hν hJ K hKo hKc
  have hu := hA.uniform_containment_and_cofinality i ν hG hi hν hJ K hKo hKc
  exact ⟨hA.leviIntersectionNormalization i ν K, hweak, hp.1, hu.1, hp.2, hu.2⟩

/-- The actual family of compact open subgroups normal in the supplied `K0`
and satisfying just the remaining Iwahori and weak-chamber conditions for all
standard faces, at the components fixed before the family. -/
def weakIwahoriNormalFamily (C : StandardSplitComponentFamily i ν)
    (K0 : Subgroup (rationalPoints G)) : Set (Subgroup (rationalPoints G)) :=
  {K | (K ≤ K0 ∧ (K.subgroupOf K0).Normal ∧
      IsOpen (K : Set (rationalPoints G)) ∧ IsCompact (K : Set (rationalPoints G))) ∧
    ∀ J : Set (characterLattice S), ∀ hJ : J ⊆ simpleRelativeRoots i ν,
      HasIwahoriIntersectionDecomposition K (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J) ∧
      WeakChamberContraction K (standardUnipotentPoints i ν J)
        (standardOppositeUnipotentPoints i ν J)
        (standardComponentCAplus i ν J (C.hom J hJ))}

/-- A concrete cofinality construction for the remaining common normal
weak-Iwahori family suffices for the entire simultaneous-basis property.
The stated local construction remains a hypothesis of this reduction. -/
theorem simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (C : StandardSplitComponentFamily i ν)
    (K0 : Subgroup (rationalPoints G))
    (hsmall : ∀ W : Set (rationalPoints G), W ∈ 𝓝 (1 : rationalPoints G) →
      ∃ K ∈ weakIwahoriNormalFamily i ν C K0, (K : Set (rationalPoints G)) ⊆ W) :
    SimultaneousStandardBasisAt i ν K0 := by
  let B := weakIwahoriNormalFamily i ν C K0
  have hB : CompactOpenNormalBasis K0 B := by
    refine ⟨fun _ hK => hK.1, hasBasis_iff.mpr ?_⟩
    intro W
    constructor
    · exact hsmall W
    · rintro ⟨K, hK, hKW⟩
      exact mem_of_superset (hK.1.2.2.1.mem_nhds K.one_mem) hKW
  refine ⟨B, hB, ?_⟩
  intro J hJ
  have hLevi : IsClosed (standardLeviPoints i ν J : Set (rationalPoints G)) := by
    let : T2Space F := Langlands.BruhatTits.localField_t2Space F
    exact isClosed_rationalPoint_subgroup F _ (Standard.leviHom i ν J)
      (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)
  refine ⟨hB.inherited hLevi, C.torus J hJ, C.hom J hJ, C.compatible J hJ, ?_⟩
  intro K hK
  exact ⟨(hK.2 J hJ).1, (C.compatible J hJ).contractionAndCofinality_of_weak
    i ν hG hi hν hJ K hK.1.2.2.1 hK.1.2.2.2 (hK.2 J hJ).2⟩

end Langlands.BruhatTits.SpecialCompact
