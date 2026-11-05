import Langlands.Geometry.Building.ChamberOrderedInjective
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs

/-! # Ordered root products from local opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Opposite factor pairs for this particular split subtorus suffice for
ordered multiplication of its indivisible positive root groups to be
injective on every test scheme. -/
theorem orderedRootSubgroupPoints_injective_of_hasOppositeFactorPairs
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective
      (fun x : ∀ r, (subgroup i (a r)).carrier T =>
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod) := by
  let b := AutomorphicAction.conjugation i
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
  have hequiv : ∀ (T' : Over (Spec (CommRingCat.of k))) (s : T' ⟶ S.X)
      (x : T' ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization
      inferInstance hS i ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha
    (fun _ hb _ hd hne =>
      hE.disjoint_cyclicTail_indivisibleRoots i hS hb.1 hd.1 hne)
  have hcover : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha
      (fun _ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)).trans
      hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hS hUu
      n (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hfactor (r : Fin n) : (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hcyclic : semigroupSubgroup b (cyclicTail (a r) 1) = subgroup i (a r) :=
      cyclicRootFunctorComparison k G inferInstance inferInstance S hS
        i (a r) (hroot r).1.1.1
    rw [← hcyclic, ← hsemigroup r]
    exact (hH r).1.comp hjU
  let : IsIso (orderedMultiplication jH) := hIso
  let : Mono jU.hom.hom := hjU.1
  have : Mono (orderedMultiplication (fun r => jH r ≫ jU)) := by
    rw [← orderedMultiplication_comp jH jU]
    infer_instance
  exact orderedSubgroupPoints_injective_of_mono
    (fun r => jH r ≫ jU) (fun r => subgroup i (a r)) hfactor T

/-- The actual ordered product on every test, as an embedding under the
local pair-existence premise. -/
def orderedRootSubgroupProductEmbeddingOfFactorPairs
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    (T : Over (Spec (CommRingCat.of k))) :
    (∀ r, (subgroup i (a r)).carrier T) ↪ (T ⟶ G.X) where
  toFun x := (List.ofFn fun r => (x r : T ⟶ G.X)).prod
  inj' := orderedRootSubgroupPoints_injective_of_hasOppositeFactorPairs
    i hS hE ν a hinj ha T

@[simp]
theorem orderedRootSubgroupProductEmbeddingOfFactorPairs_apply
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    (T : Over (Spec (CommRingCat.of k)))
    (x : ∀ r, (subgroup i (a r)).carrier T) :
    orderedRootSubgroupProductEmbeddingOfFactorPairs i hS hE ν a hinj ha T x =
      (List.ofFn fun r => (x r : T ⟶ G.X)).prod := rfl

end Langlands.GroupScheme.RelativeRoot
