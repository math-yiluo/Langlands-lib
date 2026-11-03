import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly

/-! # Actual Levi transport from root association -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- Read the root-association witness as an actual scheme-normalizer action,
without changing its underlying ambient point. -/
theorem rootAssociation_character_image
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) :
    weylAction i ((normalizerEquiv i hN).symm ⟨n, Classical.choose hIJ⟩) ''
      rootSet i ν I = rootSet i ν J := by
  rw [← weylCharacterAction_point_mk i hN hZ]
  exact Classical.choose_spec hIJ

/-- The supplied standard-cocharacter statement already implies the exact
Levi membership law for every root-association representative. -/
theorem rootAssociation_levi_mem
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (x : RationalPoint k G.X) :
    x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I := by
  exact conjugationMembership_of_map_eq n
    (levi_map_conj_of_character_image i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      J I ((normalizerEquiv i hN).symm ⟨n, Classical.choose hIJ⟩)
      (rootAssociation_character_image i ν hN hZ hIJ)) x

/-- The actual inverse-conjugation equivalence furnished by root association
and the standard-cocharacter hypothesis already present in the support target. -/
def rootAssociationLeviEquiv
    [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) :
    levi i ν J ≃ₜ* levi i ν I :=
  conjugationEquiv n (rootAssociation_levi_mem i ν hN hZ hG hi hν hStandard hIJ)

@[simp] theorem rootAssociationLeviEquiv_apply
    [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (x : levi i ν J) :
    (rootAssociationLeviEquiv i ν hN hZ hG hi hν hStandard hIJ x : RationalPoint k G.X) =
      n⁻¹ * (x : RationalPoint k G.X) * n := rfl

private theorem setImage_symm_coe {α β : Type*} (f : α → β) (s : Set α)
    (hf : Function.Injective f) (x : f '' s) :
    f ((Equiv.Set.image f s hf).symm x : α) = (x : β) :=
  congrArg Subtype.val ((Equiv.Set.image f s hf).apply_symm_apply x)

/-- The finite-label equivalence has the actual character action as its value. -/
theorem rootAssociationEquiv_apply_character
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (a : I) :
    ((rootAssociationEquiv i ν hN hZ hIJ a : J) : characterLattice T) =
      weylCharacterAction i hN hZ
        (QuotientGroup.mk ⟨n, Classical.choose hIJ⟩) (a : characterLattice T) := by
  exact setImage_symm_coe Subtype.val (J : Set (SimpleRoot i ν))
    Subtype.val_injective _

/-- The induced equivalence on the literal finite subsets of associated Levis. -/
def rootAssociationFinsetEquiv
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) : Finset I ≃ Finset J :=
  (rootAssociationEquiv i ν hN hZ hIJ).finsetCongr

/-- Every descendant subset is associated by the original ambient representative. -/
theorem rootAssociation_leviIndex
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (K : Finset I) :
    rootAssociation i ν hN hZ (leviIndex I K)
      (leviIndex J (rootAssociationFinsetEquiv i ν hN hZ hIJ K)) n := by
  classical
  refine ⟨Classical.choose hIJ, ?_⟩
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    let c := rootAssociationEquiv i ν hN hZ hIJ b
    refine ⟨c.val, ?_, rootAssociationEquiv_apply_character i ν hN hZ hIJ b⟩
    apply Finset.mem_map.mpr
    refine ⟨c, ?_, rfl⟩
    exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
    refine ⟨(c : characterLattice T), ?_,
      (rootAssociationEquiv_apply_character i ν hN hZ hIJ c).symm⟩
    exact ⟨c.val, Finset.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩

/-- Proper descendant tests are paired by the induced finite-subset equivalence. -/
def rootAssociationProperFinsetEquiv
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) :
    {K : Finset I // K ≠ Finset.univ} ≃ {K : Finset J // K ≠ Finset.univ} := by
  let e := rootAssociationFinsetEquiv i ν hN hZ hIJ
  have hu : e Finset.univ = Finset.univ := by
    exact Finset.map_univ_equiv (rootAssociationEquiv i ν hN hZ hIJ)
  exact e.subtypeEquiv fun K => by
    constructor
    · intro hK heK
      exact hK (e.injective (heK.trans hu.symm))
    · intro hK heK
      exact hK (heK ▸ hu)

/-- The original actual Levi equivalence matches every descendant Levi test. -/
theorem rootAssociationLeviEquiv_descendant_mem
    [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (K : Finset I) (x : levi i ν J) :
    x ∈ (levi i ν (leviIndex J (rootAssociationFinsetEquiv i ν hN hZ hIJ K))).subgroupOf
        (levi i ν J) ↔
      rootAssociationLeviEquiv i ν hN hZ hG hi hν hStandard hIJ x ∈
        (levi i ν (leviIndex I K)).subgroupOf (levi i ν I) :=
  rootAssociation_levi_mem i ν hN hZ hG hi hν hStandard
    (rootAssociation_leviIndex i ν hN hZ hIJ K) x

end Langlands.Aubert.General.RationalPointFamily
