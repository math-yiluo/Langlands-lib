import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Dynamic radical containment from disjoint positive root rays -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- At one actual maximal split torus and cocharacter, disjoint indivisible
positive rays suffice to put the complete radical in any subgroup containing
all actual relative root groups. -/
theorem dynamicUnipotent_le_of_disjoint_positive_rays
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G))
    (hroot : ∀ a : relativeRoots i,
      (subgroup i a.val).carrier (Over.mk (𝟙 _)) ≤ K) :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤ K := by
  have := hG.smooth
  have hfin : (indivisiblePositiveRoots i ν).Finite :=
    (hi.isSplitSubtorus.1.finite_relativeRoots i).subset (fun _ ha => ha.1.1)
  obtain ⟨n, a, hinj, ha⟩ := hfin.fin_param
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G hG.smooth inferInstance S hi.1.1 b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization hG.smooth hi.1.1 i ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)).trans hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hi.1.1 hUu n
      (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hrootmem (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hrootmem r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hrootmem r).2)
  have hfactor (r : Fin n) : (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k G hG.smooth inferInstance
      S hi.1.1 i (a r) (hrootmem r).1.1.1
    exact hcyclic ▸ hrep
  have hDynamic :
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) = semigroupSubgroup b A :=
    (dynamicSemigroupComparison k G hG.smooth inferInstance hG.connectedSpace S hi.1.1 i ν).2.2
  let := hIso
  intro g hg
  have hgA : g ∈ (semigroupSubgroup b A).carrier (Over.mk (𝟙 _)) := hDynamic ▸ hg
  let gU : rationalPoints U := (hjU.pointsEquiv _).symm ⟨g, hgA⟩
  let x : rationalPoints (∏ᶜ H) := gU ≫ inv (orderedMultiplication jH)
  have hx : x ≫ orderedMultiplication (fun r => jH r ≫ jU) = g := by
    rw [← orderedMultiplication_comp jH jU]
    simp only [x, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hjU.pointsEquiv_symm_comp _
  rw [← hx, comp_orderedMultiplication]
  unfold orderedPoints
  apply K.list_prod_mem
  intro y hy
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
  exact hroot ⟨a r, (hrootmem r).1.1⟩
    (((hfactor r).pointsEquiv _ (finiteProductPointsEquiv H _ x r)).property)

/-- The identity inclusion of the complete dynamic radical into a subgroup
containing all actual root groups, under the local ray-disjointness premise. -/
def dynamicRadicalRootInclusion
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G))
    (hroot : ∀ a : relativeRoots i,
      (subgroup i a.val).carrier (Over.mk (𝟙 _)) ≤ K) :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) →* K :=
  Subgroup.inclusion (dynamicUnipotent_le_of_disjoint_positive_rays hG hi ν hdisj K hroot)

@[simp] theorem dynamicRadicalRootInclusion_coe
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G))
    (hroot : ∀ a : relativeRoots i,
      (subgroup i a.val).carrier (Over.mk (𝟙 _)) ≤ K)
    (g : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    (dynamicRadicalRootInclusion hG hi ν hdisj K hroot g : rationalPoints G) = g := rfl

end Langlands.GroupScheme.RelativeRoot
