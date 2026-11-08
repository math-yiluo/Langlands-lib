import Langlands.GroupScheme.Rational.RootSubgroupTorusProduct
import Langlands.GroupScheme.Rational.SemigroupProductRestriction

/-! # Selected-root coordinates detect smaller semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- Ordered multiplication with each actual root coordinate also in a supplied
semigroup subgroup, on any scheme test. -/
def rootPointsProductInSemigroup (i : T.toGrp ⟶ G) {n : ℕ}
    (a : Fin n → characterLattice T) (B : AddSubsemigroup (characterLattice T))
    (V : Over (Spec (CommRingCat.of k)))
    (x : ∀ r, ((subgroup i (a r)) ⊓
      semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V) : V ⟶ G.X :=
  (List.ofFn fun r => (x r).val).prod

variable [Smooth G.X.hom]

/-- A smaller selected subgroup admits coordinates in the larger selected
root groups, with each coordinate still in the smaller subgroup. -/
theorem exists_rootPointsProduct_in_semigroup_of_mem
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A)
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X)
    (hg : g ∈ (semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V) :
    ∃ x : ∀ r, (subgroup i (a r)).carrier V,
      rootPointsProduct i a V x = g ∧
        ∀ r, (x r).val ∈ (semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V := by
  let b := AutomorphicAction.conjugation i
  have hB : 0 ∉ B := fun hz => hA (hBA hz)
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G inferInstance inferInstance T hT b B
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hB
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (W : Over (Spec (CommRingCat.of k))) (t : W ⟶ T.X)
      (x : W ⟶ U.X), c.act t x ≫ jU.hom.hom = b.act t (x ≫ jU.hom.hom) :=
    fun _ t x => b.onRepresentedSubgroup_act_comp jU hjU hStable t x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b B := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = relativeRoots i ∩ (B : Set _) := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_semigroupSubgroup_eq_roots_inter hT i B hB
  have hsub : actionWeightSupport c ⊤ ⊆ relativeRoots i ∩ (A : Set _) := by
    rw [hsupport]
    exact fun _ h => ⟨h.1, hBA h.2⟩
  have hblocks := rootRayBlock_semigroup_pairwise i hT hE A a hinj ha
  obtain ⟨H, jH, hH, hIso⟩ :=
    (hasOrderedSemigroupProducts_of_unipotent c hT hUu).for_larger_support
      (relativeRoots i ∩ (A : Set _)) hsub n (fun r => rootRayBlock i (a r))
      (iUnion_rootRayBlock_semigroup i hT hE A a ha) hblocks.1 hblocks.2
  let := hIso
  rw [← hjU.2, SubgroupFunctor.mem_range] at hg
  obtain ⟨gU, hgU⟩ := hg
  let y := gU ≫ inv (orderedMultiplication jH)
  let Y := finiteProductPointsEquiv H V y
  have hroot (r : Fin n) : a r ∈ semigroupIndivisibleRoots i A :=
    ha ▸ Set.mem_range_self r
  have hcoord (r : Fin n) :
      Y r ≫ (jH r ≫ jU).hom.hom ∈ (subgroup i (a r)).carrier V := by
    have hm : Y r ≫ (jH r).hom.hom ∈
        (semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).carrier V := by
      rw [← (hH r).1.2]
      exact ⟨Y r, rfl⟩
    have hle := semigroupSubgroup_map_le jU hjUc c b hequiv
      (AddSubsemigroup.closure (rootRayBlock i (a r)))
    have hc : semigroupSubgroup b (AddSubsemigroup.closure (rootRayBlock i (a r))) =
        subgroup i (a r) := by
      rw [closure_rootRayBlock i (hroot r).1]
      exact weightFiltration_one_eq_subgroup hT i (a r) (hroot r).1.1
    rw [hc] at hle
    exact hle V ⟨Y r ≫ (jH r).hom.hom, hm, by
      change (Y r ≫ (jH r).hom.hom) ≫ jU.hom.hom =
        Y r ≫ (jH r ≫ jU).hom.hom
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  let x (r : Fin n) : (subgroup i (a r)).carrier V :=
    ⟨Y r ≫ (jH r ≫ jU).hom.hom, hcoord r⟩
  refine ⟨x, ?_, ?_⟩
  · change orderedPoints (fun r => jH r ≫ jU) Y = g
    rw [← comp_orderedMultiplication, ← orderedMultiplication_comp jH jU]
    dsimp only [y]
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hgU
  · intro r
    rw [← hjU.2]
    exact ⟨Y r ≫ (jH r).hom.hom, by
      change (Y r ≫ (jH r).hom.hom) ≫ jU.hom.hom =
        Y r ≫ (jH r ≫ jU).hom.hom
      simp only [Grp.comp_hom_hom, Category.assoc]⟩

/-- Membership of an ordered larger-root product in a smaller selected
subgroup is equivalent to membership of every individual coordinate. -/
theorem rootPointsProduct_mem_semigroup_iff
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A)
    (V : Over (Spec (CommRingCat.of k))) (x : ∀ r, (subgroup i (a r)).carrier V) :
    rootPointsProduct i a V x ∈
        (semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V ↔
      ∀ r, (x r).val ∈ (semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V := by
  constructor
  · intro hx
    obtain ⟨y, hy, hBy⟩ :=
      exists_rootPointsProduct_in_semigroup_of_mem i hT hE A B hA hBA a hinj ha V _ hx
    have hxA := semigroupSubgroup_mono (AutomorphicAction.conjugation i) hBA V hx
    obtain ⟨z, _, hzu⟩ :=
      (mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct i hT hE A hA
        a hinj ha V _).mp hxA
    have hxy : x = y := (hzu x rfl).trans (hzu y hy).symm
    simpa only [hxy] using hBy
  · intro hx
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hz
    exact hx r

/-- Every smaller selected-subgroup point has unique coordinates in the larger
root groups intersected with the smaller subgroup, on every scheme test. -/
theorem mem_semigroupSubgroup_iff_existsUnique_rootPointsProductInSemigroup
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A)
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) :
    g ∈ (semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V ↔
      ∃! x : ∀ r, ((subgroup i (a r)) ⊓
          semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V,
        rootPointsProductInSemigroup i a B V x = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, hBx⟩ :=
      exists_rootPointsProduct_in_semigroup_of_mem i hT hE A B hA hBA
        a hinj ha V g hg
    let X (r : Fin n) : ((subgroup i (a r)) ⊓
        semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier V :=
      ⟨(x r).val, ⟨(x r).property, hBx r⟩⟩
    refine ⟨X, hx, ?_⟩
    intro Y hY
    let y (r : Fin n) : (subgroup i (a r)).carrier V :=
      ⟨(Y r).val, (Y r).property.1⟩
    have hgA := semigroupSubgroup_mono (AutomorphicAction.conjugation i) hBA V hg
    obtain ⟨z, _, hzu⟩ :=
      (mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct i hT hE A hA
        a hinj ha V g).mp hgA
    have hyx : y = x := (hzu y hY).trans (hzu x hx).symm
    funext r
    apply Subtype.ext
    exact congrArg (fun v => (v r).val) hyx
  · rintro ⟨x, hx, _⟩
    rw [← hx]
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hz
    exact (x r).property.2

end Langlands.GroupScheme.RelativeRoot
