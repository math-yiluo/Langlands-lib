import Langlands.BruhatTits.SpecialCompact.ContractingPowerBasis
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.GroupScheme.Rational.StandardLeviCentralImage
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators

/-! # Power bases for every actual strict component-chamber point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.Dynamic
open Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S A : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- The integral pairing is unchanged by the two actual component maps. -/
theorem componentCharacterRestriction_pairing
    (c : cocharacterLattice A) (α : characterLattice S) :
    latticePairing A (componentCharacterRestriction q α) c =
      latticePairing S α (cocharacterMapInt (Additive.ofMul q) c) := by
  change gmEndEquiv F (c ≫ (Additive.ofMul q ≫ α)) =
    gmEndEquiv F ((c ≫ Additive.ofMul q) ≫ α)
  rw [Category.assoc]

/-- Every component cocharacter annihilates the selected simple roots,
because its actual image is central in the standard Levi. -/
theorem IsCompatibleStandardSplitComponent.pairing_eq_zero
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hJ : J ⊆ simpleRelativeRoots i ν)
    (c : cocharacterLattice A) {α : characterLattice S} (hα : α ∈ J) :
    latticePairing S α (cocharacterMapInt (Additive.ofMul q) c) = 0 := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨_, M, j, a, hj, hjc, _, ha, hcompat⟩ := hA
  exact latticePairing_cocharacterMapInt_standardLevi_eq_zero
    dynamicLie i ν J hJ hjc hj a ha.1 (Additive.ofMul q) hcompat.symm c hα

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Every strict component-chamber point is the common-uniformizer value
of an actual standard cocharacter of the prescribed maximal torus. -/
theorem IsCompatibleStandardSplitComponent.exists_standardCocharacter_of_strictPoint
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hJ : J ⊆ simpleRelativeRoots i ν)
    {m : rationalPoints G} (hm : m ∈ standardComponentCAstrict i ν J q) :
    ∃ ζ : cocharacterLattice S,
      IsStandardCocharacter i ν J ζ ∧
      cocharPoint (CommGroupScheme.groupHom ζ ≫ i)
        (SplitTorusValuation.uniformizerUnit F) = m := by
  obtain ⟨x, ⟨⟨c, rfl⟩, hstrict⟩, rfl⟩ := hm
  let ζ := cocharacterMapInt (Additive.ofMul q) c.toAdd
  have hζ : IsStandardCocharacter i ν J ζ := by
    refine ⟨hJ, fun α hα => hA.pairing_eq_zero i ν hG hJ c.toAdd hα, ?_⟩
    intro α hα hαJ
    have hp := hstrict (componentCharacterRestriction q α)
      ⟨α, ⟨hα, hαJ⟩, rfl⟩
    change CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α)
      (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c.toAdd)) < 1 at hp
    rw [CocharacterUniformizer.characterNorm_latticeSection,
      componentCharacterRestriction_pairing] at hp
    have hq : (1 : ℝ) < LocalField.residueCardinality F := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    have hneg := (zpow_lt_one_iff_right₀ hq).mp hp
    change 0 < latticePairing S α
      (cocharacterMapInt (Additive.ofMul q) c.toAdd)
    omega
  refine ⟨ζ, hζ, ?_⟩
  rw [cocharPoint_eq]
  change (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
      (SplitTorusValuation.uniformizerUnit F) ≫
      ((CommGroupScheme.groupHom c.toAdd ≫ q) ≫ i).hom.hom =
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
      (SplitTorusValuation.uniformizerUnit F) ≫
      (CommGroupScheme.groupHom c.toAdd).hom.hom) ≫ (q ≫ i).hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]

/-- An actual standard cocharacter, with its sign and point-identification
proofs, associated to the supplied strict point. -/
def IsCompatibleStandardSplitComponent.standardCocharacterOfStrictPoint
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hJ : J ⊆ simpleRelativeRoots i ν)
    (m : rationalPoints G) (hm : m ∈ standardComponentCAstrict i ν J q) :
    {ζ : cocharacterLattice S //
      IsStandardCocharacter i ν J ζ ∧
      cocharPoint (CommGroupScheme.groupHom ζ ≫ i)
        (SplitTorusValuation.uniformizerUnit F) = m} :=
  ⟨(hA.exists_standardCocharacter_of_strictPoint i ν hG hJ hm).choose,
    (hA.exists_standardCocharacter_of_strictPoint i ν hG hJ hm).choose_spec⟩

local instance strictChamberPowerBasisAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance strictChamberPowerBasisTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Every strict chamber point gives both expanding-union identities and both
intrinsic power-neighborhood bases for any compact open ambient subgroup. -/
theorem IsCompatibleStandardSplitComponent.strictChamber_power_basis_and_exhaustion
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (K : Subgroup (rationalPoints G))
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    StrictChamberExhaustion K
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)
      (standardComponentCAstrict i ν J q) ∧
    StrictChamberNeighborhoodBases K
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)
      (standardComponentCAstrict i ν J q) := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : Smooth G.X.hom := hG.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hall : ∀ m ∈ standardComponentCAstrict i ν J q,
      StrictChamberExhaustion K
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J) {m} ∧
      StrictChamberNeighborhoodBases K
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J) {m} := by
    intro m hm
    obtain ⟨ζ, hζ, heval⟩ := hA.standardCocharacterOfStrictPoint i ν hG hJ m hm
    have hstd := (standardCocharacter F G hG S i hi ν hν J hJ).2 ζ hζ
    have hrev := standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν
      (relativeRootNegation F G hG S i hi) hζ
    have hU : standardUnipotentPoints i ν J =
        unipotentPoints (CommGroupScheme.groupHom ζ ≫ i) :=
      congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hstd.2.2
    have hO : standardOppositeUnipotentPoints i ν J =
        unipotentPoints (inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)) :=
      congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hrev.2.2
    rw [hU, hO, ← heval]
    exact dynamic_power_basis_and_exhaustion (CommGroupScheme.groupHom ζ ≫ i)
      (SplitTorusValuation.uniformizerUnit F)
      (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero F) K hKo hKc
  exact ⟨fun m hm => (hall m hm).1 m (mem_singleton m),
    fun m hm => (hall m hm).2 m (mem_singleton m)⟩

end Langlands.BruhatTits.SpecialCompact
