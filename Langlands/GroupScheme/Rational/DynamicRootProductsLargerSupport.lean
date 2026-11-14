import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayDecomposition

/-! # Dynamic root products indexed by a larger root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G₀ G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₀.X.hom] [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Actual ordered root representatives and their isomorphism onto a full
dynamic unipotent representative, for any supplied finite ray list. -/
structure DynamicRootProductData (j : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S) where
  unipotentGroup : GroupScheme (Spec (CommRingCat.of k))
  unipotentInclusion : unipotentGroup ⟶ G
  factors : Fin n → GroupScheme (Spec (CommRingCat.of k))
  factorInclusions : ∀ r, factors r ⟶ G
  productIso : (∏ᶜ factors).X ≅ unipotentGroup.X
  unipotentRep :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy unipotentInclusion
  unipotentClosed : IsClosedSubgroup unipotentInclusion
  unipotentSmooth : Smooth unipotentGroup.X.hom
  unipotentConnected : ConnectedSpace unipotentGroup.X.left
  unipotent : IsUnipotent unipotentGroup
  factorRep : ∀ r, (subgroup j (a r)).IsRepresentedBy (factorInclusions r)
  factorClosed : ∀ r, IsClosedSubgroup (factorInclusions r)
  factorSmooth : ∀ r, Smooth (factors r).X.hom
  factorConnected : ∀ r, ConnectedSpace (factors r).X.left
  product_comp :
    productIso.hom ≫ unipotentInclusion.hom.hom = orderedMultiplication factorInclusions

/-- Use the indivisible rays of a larger root support even when some initial
roots, or all weights of a ray, are absent from the target group. -/
def dynamicRootProductOfLargerSupport (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G₀) (j : S.toGrp ⟶ G)
    (hsub : relativeRoots j ⊆ relativeRoots i)
    (ν : cocharacterLattice S) (n : ℕ) (a : Fin n → characterLattice S)
    (hinj : Function.Injective a) (ha : Set.range a = indivisiblePositiveRoots i ν)
    (hdisj : ∀ b ∈ indivisiblePositiveRoots i ν,
      ∀ c ∈ indivisiblePositiveRoots i ν, b ≠ c →
        Disjoint (cyclicTail b 1 : Set (characterLattice S))
          (cyclicTail c 1 : Set (characterLattice S))) :
    DynamicRootProductData j ν a := by
  apply Classical.choice
  let b := AutomorphicAction.conjugation j
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G inferInstance inferInstance S hS b A
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
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots j ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization inferInstance hS j ν
  have hsupportSub : actionWeightSupport c ⊤ ⊆ positiveRelativeRoots i ν := by
    rw [hsupport]
    exact fun _ hχ => ⟨hsub hχ.1, hχ.2⟩
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock i (a r)) = positiveRelativeRoots i ν :=
    iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)
  obtain ⟨H, jH, hH, hIso⟩ :=
    (hasOrderedSemigroupProducts_of_unipotent c hS hUu).for_larger_support
      (positiveRelativeRoots i ν) hsupportSub n
      (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hfactor (r : Fin n) : (subgroup j (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hr : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
        (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k G inferInstance inferInstance S hS
      j (a r) (hroot r).1.1.1
    exact hcyclic ▸ hr
  have hDynamic :
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ j) = semigroupSubgroup b A :=
    dynamicUnipotentSemigroupComparison G S hS j ν
  let := hIso
  exact ⟨{
    unipotentGroup := U
    unipotentInclusion := jU
    factors := H
    factorInclusions := fun r => jH r ≫ jU
    productIso := asIso (orderedMultiplication jH)
    unipotentRep := hDynamic ▸ hjU
    unipotentClosed := hjUc
    unipotentSmooth := hUs
    unipotentConnected := hUc
    unipotent := hUu
    factorRep := hfactor
    factorClosed := fun r => (hH r).2.1.comp hjUc
    factorSmooth := fun r => (hH r).2.2.1
    factorConnected := fun r => (hH r).2.2.2
    product_comp := orderedMultiplication_comp jH jU
  }⟩

end Langlands.GroupScheme.RelativeRoot
