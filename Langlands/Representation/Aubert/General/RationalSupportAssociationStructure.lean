import Langlands.Representation.Aubert.General.RationalRootAssociationLeviTransport
import Langlands.Representation.Aubert.General.RootAssociationComposition
import Langlands.GroupScheme.Rational.NestedStandardTransport
import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation

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
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

theorem rootAssociation_character_image_of_mem {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (h : rootAssociation i ν hN hZ I J n)
    (hn : n ∈ Group.RelativeWeyl.normalizer (torusPoints i)) :
    weylAction i ((normalizerEquiv i hN).symm ⟨n, hn⟩) '' rootSet i ν I =
      rootSet i ν J := by
  exact rootAssociation_character_image i ν hN hZ h

theorem rootAssociationEquiv_character {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (h : rootAssociation i ν hN hZ I J n) (a : I) :
    (((rootAssociationEquiv i ν hN hZ h a : J) : SimpleRoot i ν) :
        characterLattice T) =
      weylCharacterAction i hN hZ (QuotientGroup.mk ⟨n, h.choose⟩)
        ((a : SimpleRoot i ν) : characterLattice T) := by
  let e := weylCharacterAction i hN hZ (QuotientGroup.mk ⟨n, h.choose⟩)
  let ej := Equiv.Set.image (Subtype.val : SimpleRoot i ν → characterLattice T)
    (J : Set (SimpleRoot i ν)) Subtype.val_injective
  let b : rootSet i ν J :=
    ⟨e ((a : SimpleRoot i ν) : characterLattice T),
      h.choose_spec ▸ Set.mem_image_of_mem e (Set.mem_image_of_mem Subtype.val a.property)⟩
  exact congrArg Subtype.val (ej.apply_symm_apply b)

omit [Mono i.hom.hom.left] in
theorem rootSet_leviIndex_eq (I : Finset (SimpleRoot i ν)) (K : Finset I) :
    rootSet i ν (leviIndex I K) =
      (fun a : I => ((a : SimpleRoot i ν) : characterLattice T)) '' (K : Set I) := by
  ext α
  simp only [rootSet, leviIndex, Finset.coe_map, Set.mem_image]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨a, ha, rfl⟩, rfl⟩

omit [Mono i.hom.hom.left] in
theorem rootSet_leviIndex_subset (I : Finset (SimpleRoot i ν)) (K : Finset I) :
    rootSet i ν (leviIndex I K) ⊆ rootSet i ν I := by
  rw [rootSet_leviIndex_eq]
  rintro α ⟨a, ha, rfl⟩
  exact Set.mem_image_of_mem _ a.property

/-- Every nested subset of the target has a proper preimage under association. -/
theorem exists_associated_nested_subset {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (h : rootAssociation i ν hN hZ I J n)
    (K' : Finset J) (hK' : K' ≠ Finset.univ) :
    ∃ K : Finset I, K ≠ Finset.univ ∧
      rootAssociation i ν hN hZ (leviIndex I K) (leviIndex J K') n := by
  classical
  let e := rootAssociationEquiv i ν hN hZ h
  let K := K'.map e.symm.toEmbedding
  have hK : K ≠ Finset.univ := by
    intro hKu
    apply hK'
    exact (Finset.map_injective e.symm.toEmbedding)
      (hKu.trans (Finset.map_univ_equiv e.symm).symm)
  refine ⟨K, hK, h.choose, ?_⟩
  rw [rootSet_leviIndex_eq, rootSet_leviIndex_eq]
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    refine ⟨b, hb, ?_⟩
    simpa [e] using (rootAssociationEquiv_character i ν hN hZ h (e.symm b))
  · rintro ⟨b, hb, rfl⟩
    refine ⟨((e.symm b : I) : SimpleRoot i ν), ?_, ?_⟩
    · exact ⟨e.symm b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩
    · simpa [e] using (rootAssociationEquiv_character i ν hN hZ h (e.symm b)).symm

/-- The displayed cocharacter premise already supplies actual Levi conjugation. -/
theorem rootAssociation_levi_membership
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (h : rootAssociation i ν hN hZ I J n) (x : RationalPoint k G.X) :
    x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I := by
  exact conjugationMembership_of_map_eq n
    (levi_map_conj_of_character_image i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      J I ((normalizerEquiv i hN).symm ⟨n, h.choose⟩)
      (rootAssociation_character_image_of_mem i ν hN hZ h h.choose)) x

/-- Inside associated outer Levis, the same representative carries the
radicals of associated nested faces. -/
theorem rootAssociation_nested_unipotent_membership
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (h : rootAssociation i ν hN hZ I J n)
    {K : Finset I} {K' : Finset J}
    (hKK' : rootAssociation i ν hN hZ (leviIndex I K) (leviIndex J K') n)
    (x : RationalPoint k G.X) (hx : x ∈ levi i ν J) :
    x ∈ unipotent i ν (leviIndex J K') ↔
      n⁻¹ * x * n ∈ unipotent i ν (leviIndex I K) := by
  let a := (normalizerEquiv i hN).symm ⟨n, h.choose⟩
  have hg :
      (n⁻¹ * x * n) ≫
          (G.innerIso (a : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
        (standardLevi i ν (rootSet i ν J)).carrier _ := by
    rw [comp_innerIso_hom, constantPoint_self]
    change n * (n⁻¹ * x * n) * n⁻¹ ∈ levi i ν J
    simpa [mul_assoc] using hx
  have hs := mem_standardUnipotent_conj_of_mem_standardLevi i ν hG hi hν hStandard
    hfinite (rootSet_subset i ν I) (rootSet_subset i ν J)
    (rootSet_leviIndex_subset i ν I K) (rootSet_leviIndex_subset i ν J K')
    a (rootAssociation_character_image_of_mem i ν hN hZ h h.choose)
    (rootAssociation_character_image_of_mem i ν hN hZ hKK' h.choose) hg
  rw [comp_innerIso_hom, constantPoint_self] at hs
  change n⁻¹ * x * n ∈ unipotent i ν (leviIndex I K) ↔
    n * (n⁻¹ * x * n) * n⁻¹ ∈ unipotent i ν (leviIndex J K') at hs
  simpa [mul_assoc] using hs.symm

end Langlands.Aubert.General.RationalPointFamily
