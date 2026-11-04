import Langlands.Representation.Aubert.General.RationalCartanLatticeModel

/-! # Weak-chamber membership of integral uniformizer powers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Every integral cocharacter annihilating the selected roots and nonnegative
on the other roots evaluates inside the supplied component's weak chamber. -/
theorem uniformizerPowers_mem_standardComponentCAplus (hi : IsMaximalSplitTorus i)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (q : A.toGrp ⟶ S.toGrp)
    (hcomp : IsCompatibleStandardSplitComponent i ν (rootSet i ν J) A q)
    (y : cocharacterLattice S)
    (hy : ∀ β ∈ J, simpleRootPairing i ν β y = 0)
    (hypos : ∀ β ∉ J, 0 ≤ simpleRootPairing i ν β y) :
    uniformizerPowers i (.ofAdd y) ∈ standardComponentCAplus i ν (rootSet i ν J) q := by
  obtain ⟨-, M, jM, a, hjM, hjMc, hMred, ha, haq⟩ := hcomp
  let t := standardLeviTorusFactor i ν (rootSet i ν J) hjM
  have : IsAffineHom M.X.hom := hMred.isAffineHom
  have : Mono t.hom.hom.left :=
    (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν _ hjM hjMc).isSplitSubtorus.mono
  have hf : CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S) ≫ t = a := by
    have : Mono jM.hom.hom := hjM.1
    apply Grp.hom_ext
    apply (cancel_mono jM.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc,
      standardLeviTorusFactor_comp, haq]
    rfl
  have hyc : y ∈ centralCocharacters t :=
    isCentral_standardLeviTorusFactor_of_annihilates i ν (rootSet i ν J) hjM hfinite
      hexists y (by rintro α ⟨β, hβ, rfl⟩; exact hy β hβ)
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters _ hf] at hyc
  obtain ⟨c, rfl⟩ := hyc
  refine ⟨CocharacterUniformizer.latticeSection F A (.ofAdd c), ⟨⟨.ofAdd c, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨β, ⟨hβs, hβJ⟩, rfl⟩
    rw [characterNorm_latticeSection, latticePairing_componentCharacterRestriction]
    have hβJ' : (⟨β, hβs⟩ : SimpleRoot i ν) ∉ J := fun h =>
      hβJ ((val_mem_rootSet i ν J ⟨β, hβs⟩).mpr h)
    have hq : (1 : ℝ) ≤ LocalField.residueCardinality F := by
      exact_mod_cast (LocalField.residueCardinality_gt_one F).le
    exact (zpow_le_zpow_right₀ hq (neg_nonpos.mpr (hypos ⟨β, hβs⟩ hβJ'))).trans_eq
      (zpow_zero _)
  · change rationalPoints.map i (rationalPoints.map
      (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
        (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    rfl

end Langlands.Aubert.General
