import Langlands.GroupScheme.Rational.OpenRootGenerationStatement
import Langlands.GroupScheme.Rational.OpenRootGenerationNeighborhoods
import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open root generation from the actual ordered root products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.RelativeRoot

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- An open neighborhood in a closed representative extends to an ambient open
neighborhood, with its intersection with the represented subgroup prescribed. -/
private theorem exists_open_restrict_represented
    {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (R : SubgroupFunctor G) (j : U ⟶ G) (hj : R.IsRepresentedBy j)
    (hc : IsClosedSubgroup j) :
    letI : IsClosedImmersion j.hom.hom.left := hc
    letI : IsAffine U.X.left := isAffine_of_isAffineHom j.hom.hom.left
    letI := rationalPointTopology F G.X
    letI := rationalPointTopology F U.X
    ∀ W : Set (rationalPoints U), IsOpen W → (1 : rationalPoints U) ∈ W →
      ∃ C : Set (rationalPoints G), IsOpen C ∧ 1 ∈ C ∧
        ∀ x ∈ C, x ∈ R.carrier (Over.mk (𝟙 _)) →
          ∃ y ∈ W, rationalPoints.map j y = x := by
  let : IsClosedImmersion j.hom.hom.left := hc
  let : IsAffine U.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let := rationalPointTopology F G.X
  let := rationalPointTopology F U.X
  intro W hW h1
  obtain ⟨C, hC, heq⟩ :=
    (isEmbedding_rationalPointMap F j.hom.hom).isInducing.isOpen_iff.mp hW
  refine ⟨C, hC, ?_, ?_⟩
  · have hmem : (1 : rationalPoints U) ≫ j.hom.hom ∈ C := by
      change (1 : rationalPoints U) ∈ (fun p => p ≫ j.hom.hom) ⁻¹' C
      rwa [heq]
    simpa only [MonObj.one_comp] using hmem
  · intro x hx hR
    have hrange : x ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
      rwa [hj.2]
    obtain ⟨y, hy⟩ := hrange
    change y ≫ j.hom.hom = x at hy
    refine ⟨y, ?_, hy⟩
    rw [← heq]
    change y ≫ j.hom.hom ∈ C
    rwa [hy]

/-- Identity-neighborhood control on both radicals and the dynamic centralizer
makes a subgroup open for the canonical rational-point topology. -/
private theorem isOpen_of_dynamic_neighborhoods
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI := rationalPointTopology F G.X
    ∀ (K : Subgroup (rationalPoints G))
      (A B C : Set (rationalPoints G)),
      IsOpen A → 1 ∈ A → IsOpen B → 1 ∈ B → IsOpen C → 1 ∈ C →
      (∀ x ∈ A, x ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ)).carrier
          (Over.mk (𝟙 _)) → x ∈ K) →
      (∀ x ∈ B, x ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) → x ∈ K) →
      (∀ x ∈ C, x ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) → x ∈ K) →
      IsOpen (K : Set (rationalPoints G)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro K A B C hA hA1 hB hB1 hC hC1 hAK hBK hCK
  apply K.isOpen_of_mem_nhds
  have htop := rationalPointTopology_eq_rationalSchemeTopology F G.X
  have hcell := Dynamic.opposite_cell_mem_nhds_one F G χ
  rw [← htop] at hcell
  apply Filter.mem_of_superset
    (hcell A (hA.mem_nhds hA1) B (hB.mem_nhds hB1) C (hC.mem_nhds hC1))
  rintro x ⟨a, ⟨haA, haU⟩, b, ⟨hbB, hbZ⟩, c, ⟨hcC, hcU⟩, rfl⟩
  exact K.mul_mem (K.mul_mem (hAK a haA haU) (hBK b hbB hbZ)) (hCK c hcC hcU)

private theorem openRootCentralizerGeneration_of_unipotent_neighborhoods
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (hN :
      letI := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI := rationalPointTopology F G.X
      ∀ (V : relativeRoots i → Subgroup (rationalPoints G))
        (K : Subgroup (rationalPoints G)),
        (∀ a : relativeRoots i, IsOpen ((V a).subgroupOf
          ((subgroup i (a : characterLattice S)).carrier (Over.mk (𝟙 _))) :
            Set ((subgroup i (a : characterLattice S)).carrier (Over.mk (𝟙 _))))) →
        (∀ a, V a ≤ K) →
        ∀ ν : cocharacterLattice S,
          ∃ C : Set (rationalPoints G), IsOpen C ∧ 1 ∈ C ∧
            ∀ x ∈ C, x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
              (Over.mk (𝟙 _)) → x ∈ K)
    (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
    (hj : (torusCentralizer i).IsRepresentedBy j) (hc : IsClosedSubgroup j) :
    OpenRootCentralizerGeneration hG i j hc := by
  let := hG.isAffineHom
  let := hG.smooth
  let : IsSeparated G.X.hom := inferInstance
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion j.hom.hom.left := hc
  let : IsAffine Z.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let := rationalPointTopology F G.X
  let := rationalPointTopology F Z.X
  intro V Z' _hVle hVopen hZopen
  let K : Subgroup (rationalPoints G) :=
    Z'.map (rationalPoints.map j) ⊔ ⨆ a, V a
  have hVK : ∀ a, V a ≤ K := fun a =>
    le_trans (le_iSup V a) le_sup_right
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  obtain ⟨A, hA, hA1, hAK⟩ := hN V K hVopen hVK (-ν)
  obtain ⟨C, hC, hC1, hCK⟩ := hN V K hVopen hVK ν
  obtain ⟨B, hB, hB1, hBK⟩ :=
    exists_open_restrict_represented (torusCentralizer i) j hj hc
      (Z' : Set (rationalPoints Z)) hZopen Z'.one_mem
  have hcentralizer := genericCentralizer F G hG S i hi ν hν
  have hnegative :
      CommGroupScheme.groupHom (-ν) ≫ i =
        CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫
          (CommGroupScheme.groupHom ν ≫ i) := by
    have hn : Gm.powerHom _ (-1) ≫ ν = -ν := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (-ν) ≫ i =
      CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i
    rw [hn]
  apply isOpen_of_dynamic_neighborhoods G (CommGroupScheme.groupHom ν ≫ i)
    K A B C hA hA1 hB hB1 hC hC1
  · rwa [hnegative] at hAK
  · intro x hx hxZ
    rw [hcentralizer] at hxZ
    obtain ⟨y, hy, heq⟩ := hBK x hx hxZ
    exact (le_sup_left : Z'.map (rationalPoints.map j) ≤ K)
      (Subgroup.mem_map.mpr ⟨y, hy, heq⟩)
  · exact hCK

/-- The canonical-topology deduction of KP Corollary 8.2.6 from the actual
ordered root-product decompositions. The structural premise remains explicit. -/
def OpenRootGenerationFromOrderedProducts : Prop :=
  DynamicRootOrderedProductStatement.{u} → OpenRootCentralizerGenerationStatement.{u}

/-- Finite ordered root products and the opposite open cell give the openness
conclusion, for every local field and the unchanged actual-root index set. -/
theorem openRootCentralizerGeneration_of_dynamicRootOrderedProduct :
    OpenRootGenerationFromOrderedProducts.{u} := by
  intro hProduct F _ _ _ _ G hG S i hi Z j hj hc
  refine openRootCentralizerGeneration_of_unipotent_neighborhoods hG i hi ?_ Z j hj hc
  let := hG.isAffineHom
  let := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := rationalPointTopology F G.X
  intro V K hV hVK ν
  have hfin : (indivisiblePositiveRoots i ν).Finite :=
    (hi.isSplitSubtorus.1.finite_relativeRoots i).subset (fun _ ha => ha.1.1)
  obtain ⟨n, a, ha, hrange⟩ := hfin.fin_param
  have hamem (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν := by
    rw [← hrange]
    exact Set.mem_range_self r
  let aRoot (r : Fin n) : relativeRoots i := ⟨a r, (hamem r).1.1⟩
  obtain ⟨U, jU, H, jH, e, hU, hcU, -, -, -, -, hH, he⟩ :=
    hProduct F G hG S i hi ν n a ha hrange
  exact exists_open_restrict_orderedProduct F H (fun r => subgroup i (a r))
    jH (fun r => (hH r).1) _ jU hU hcU e he
    (fun r => V (aRoot r)) K (fun r => hV (aRoot r)) (fun r => hVK (aRoot r))

end Langlands.GroupScheme.RelativeRoot
