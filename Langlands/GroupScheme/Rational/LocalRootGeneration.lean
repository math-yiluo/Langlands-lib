import Langlands.GroupScheme.Rational.LocalRootProducts
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.SplitRootSubgroupOverDomain
import Langlands.GroupScheme.Dynamic.HenselianCellGeneration

/-! # Integral section generation by roots and a dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

/-- A product chart with its original ambient equation transfers containment
of all factor points to containment of all target points. -/
theorem range_le_of_orderedProductIso
    {B : Scheme.{u}} {G U : GroupScheme B} {n : ℕ}
    {H : Fin n → GroupScheme B} (j : ∀ r, H r ⟶ G) (jU : U ⟶ G)
    (e : (∏ᶜ H).X ≅ U.X)
    (he : e.hom ≫ jU.hom.hom = orderedMultiplication j)
    (T : Over B) (Q : Subgroup (T ⟶ G.X))
    (hQ : ∀ r, (SubgroupFunctor.range (j r)).carrier T ≤ Q) :
    (SubgroupFunctor.range jU).carrier T ≤ Q := by
  intro g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  change x ≫ jU.hom.hom ∈ Q
  have hx : x ≫ jU.hom.hom = (x ≫ e.inv) ≫ orderedMultiplication j := by
    simp only [← he, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hx, comp_orderedMultiplication]
  unfold orderedPoints
  apply Q.list_prod_mem
  intro y hy
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
  exact hQ r (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)

section LocalDomain

variable {R k : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field k] [Algebra R k]
    (I : Type u) [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance localRootGenerationAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

local instance localRootGenerationAbsoluteAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

set_option maxHeartbeats 1600000 in
/-- A subgroup containing each actual integral root functor selected by a
root on one field fibre contains all points of any dynamic radical.
The conclusion holds on every test scheme over the local domain. -/
theorem dynamicUnipotent_carrier_le_of_exponentRoots
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (hroot : HasRelativeRootSystem
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (ν : I → ℤ) (T : Over (Spec (CommRingCat.of R)))
    (Q : Subgroup (T ⟶ G.X))
    (hQ : ∀ m : I → ℤ,
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i) →
      (subgroup i (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m)).carrier T ≤ Q) :
    (Dynamic.unipotent (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier T ≤ Q := by
  classical
  let ik : (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap R k)).obj G :=
    splitTorus.baseChangeHom (K := k) G I i
  let νk := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν
  obtain ⟨n, a, hinj, ha⟩ := exists_fin_enumeration_indivisiblePositiveRoots ik νk
    (hroot.finite_relativeRoots ik (isSplitTorus_splitTorus I))
  let m (r : Fin n) : I → ℤ := splitTorus.characterLatticeEquiv k I (a r)
  have hmk (r : Fin n) :
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r) = a r := by
    rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact AddEquiv.symm_apply_apply _ _
  have ham (r : Fin n) : a r ∈ indivisiblePositiveRoots ik νk :=
    ha ▸ Set.mem_range_self r
  have hmR (r : Fin n) :
      splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r) ≠ 0 := by
    have hcoord : splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r) =
        (splitTorus.characterLatticeEquiv R I).symm (m r) :=
      (splitTorus.characterLatticeEquiv_symm_eq R I (m r)).symm
    intro hz
    have hmzero : m r = 0 := by
      apply (splitTorus.characterLatticeEquiv R I).symm.injective
      simpa only [map_zero] using hcoord.symm.trans hz
    have hakzero : a r = 0 := by
      rw [← hmk r, hmzero,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_zero]
    exact (ham r).1.1.1 hakzero
  have hrep (r : Fin n) := Domain.subgroup_has_smooth_geometricallyConnected_closed_representative
    (isSplitTorus_splitTorus I) i
    (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r)) (hmR r)
  choose H j hj hclosed haff hsm hconn using hrep
  let χ := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i
  let jU := Dynamic.Affine.unipotentHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hdisj : ∀ a ∈ indivisiblePositiveRoots ik νk,
      ∀ b ∈ indivisiblePositiveRoots ik νk, a ≠ b →
      Disjoint (cyclicTail a 1 : Set (characterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
        (cyclicTail b 1 : Set (characterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))) := by
    intro a ha b hb hne
    exact disjoint_cyclicTail_indivisibleRoots ik hroot (isSplitTorus_splitTorus I)
      ha.1 hb.1 hne
  obtain ⟨e, he⟩ := exists_orderedRootProductIso_localRing (k := k) I i ν
    hdisj m (by simpa only [hmk] using hinj)
    (by simpa only [hmk] using ha) hU j hj hsm
  rw [← hU.2]
  apply range_le_of_orderedProductIso j jU e he T Q
  intro r
  rw [(hj r).2]
  exact hQ (m r) (by rw [hmk]; exact (ham r).1.1)

end LocalDomain

private theorem geometricallyIrreducible_of_smooth_affine_connected
    {B : Scheme.{u}} (G : GroupScheme B)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom] :
    GeometricallyIrreducible G.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ b => ?_⟩
  let H := (GroupScheme.baseChange b).obj G
  have : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom H.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hG : GeometricallyConnected G.X.hom := inferInstance
  have : ConnectedSpace H.X.left :=
    pullback_of_geometrically hG.geometrically_connectedSpace k b
  have hI := smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  let : GeometricallyIntegral H.X.hom := hI
  exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.X.hom

section StrictHenselian

variable {R k : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field k] [Algebra R k]
    (I : Type u) [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- The subgroup generated by the actual integral roots selected on the
field fibre and the actual dynamic centralizer of the given cocharacter. -/
def exponentRootCentralizerSubgroup (ν : I → ℤ) : Subgroup (rationalPoints G) :=
  (⨆ m : {m : I → ℤ //
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i)},
    (subgroup i (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m.val)).carrier
      (𝟙_ (Over (Spec (CommRingCat.of R))))) ⊔
    (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier
        (𝟙_ (Over (Spec (CommRingCat.of R))))

set_option maxHeartbeats 1600000 in
/-- Over a strictly Henselian local domain, the actual integral root
functors and a dynamic centralizer generate the entire section group. -/
theorem eq_top_of_exponentRoots_and_dynamicCentralizer
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (hroot : HasRelativeRootSystem
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (ν : I → ℤ) (Q : Subgroup (rationalPoints G))
    (hQ : ∀ m : I → ℤ,
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i) →
      (subgroup i (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m)).carrier
        (𝟙_ (Over (Spec (CommRingCat.of R)))) ≤ Q)
    (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier
        (𝟙_ (Over (Spec (CommRingCat.of R)))) ≤ Q) :
    Q = ⊤ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : GeometricallyIrreducible G.X.hom :=
    geometricallyIrreducible_of_smooth_affine_connected G
  let χ := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i
  have hneg : CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ =
      CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-ν)) ≫ i := by
    have hc : Gm.powerHom (Spec (CommRingCat.of R)) (-1) ≫
        splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν =
        splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-ν) := by
      rw [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
      simp only [splitTorus.exponentCocharacter, Pi.neg_apply,
        neg_smul, Finset.sum_neg_distrib]
    change _ ≫ (_ ≫ i) = _
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫
      splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i = _
    rw [hc]
  apply Dynamic.eq_top_of_dynamic_section_ranges χ
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_centralizerHom _)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) Q
  · change (SubgroupFunctor.range (Dynamic.Affine.unipotentHom _)).carrier _ ≤ Q
    rw [(Dynamic.Affine.isRepresentedBy_unipotentHom _).2, hneg]
    exact dynamicUnipotent_carrier_le_of_exponentRoots (k := k) I i hroot (-ν) _ Q hQ
  · change (SubgroupFunctor.range (Dynamic.Affine.centralizerHom χ)).carrier _ ≤ Q
    rw [(Dynamic.Affine.isRepresentedBy_centralizerHom χ).2]
    exact hZ
  · change (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ)).carrier _ ≤ Q
    rw [(Dynamic.Affine.isRepresentedBy_unipotentHom χ).2]
    exact dynamicUnipotent_carrier_le_of_exponentRoots (k := k) I i hroot ν _ Q hQ

/-- The constructed subgroup of root and centralizer sections is the full
section group, under the actual field-fibre root-system hypotheses. -/
theorem exponentRootCentralizerSubgroup_eq_top
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (hroot : HasRelativeRootSystem
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i)) (ν : I → ℤ) :
    exponentRootCentralizerSubgroup (k := k) I i ν = ⊤ := by
  unfold exponentRootCentralizerSubgroup
  apply eq_top_of_exponentRoots_and_dynamicCentralizer (k := k) I i hroot ν
  · intro m hm
    apply le_sup_of_le_left
    exact le_iSup_of_le (⟨m, hm⟩ : {m : I → ℤ //
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i)}) le_rfl
  · exact le_sup_right

end StrictHenselian

end Langlands.GroupScheme.RelativeRoot
