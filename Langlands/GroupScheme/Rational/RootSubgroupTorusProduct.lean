import Langlands.GroupScheme.Rational.SelectedRootSemigroupProduct
import Langlands.GroupScheme.Rational.RootSubgroupTorusRestriction
import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Actual root products after restriction between split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- Ordered multiplication of actual root-functor points on any test scheme. -/
def rootPointsProduct (i : T.toGrp ⟶ G) {n : ℕ}
    (a : Fin n → characterLattice T) (V : Over (Spec (CommRingCat.of k)))
    (x : ∀ r, (subgroup i (a r)).carrier V) : V ⟶ G.X :=
  (List.ofFn fun r => (x r).val).prod

section Selected

variable [Smooth G.X.hom]

/-- The actual selected-root product has unique coordinates on every test
scheme, expressed directly in the existing intrinsic root functors. -/
theorem mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A : AddSubsemigroup (characterLattice T)) (hzero : 0 ∉ A)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A)
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) :
    g ∈ (semigroupSubgroup (AutomorphicAction.conjugation i) A).carrier V ↔
      ∃! x : ∀ r, (subgroup i (a r)).carrier V, rootPointsProduct i a V x = g := by
  obtain ⟨U, jU, H, j, e, hjU, _, _, _, _, _, hfactor, he⟩ :=
    semigroup_orderedRootProduct i hT hE A hzero a hinj ha
  let lift (x : ∀ r, (subgroup i (a r)).carrier V) : V ⟶ (∏ᶜ H).X :=
    (finiteProductPointsEquiv H V).symm
      (fun r => ((hfactor r).1.pointsEquiv V).symm (x r))
  have hlift (x : ∀ r, (subgroup i (a r)).carrier V) :
      lift x ≫ orderedMultiplication j = rootPointsProduct i a V x := by
    rw [finiteProductPointsEquiv_symm_orderedMultiplication]
    unfold orderedPoints rootPointsProduct
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext r
    exact (hfactor r).1.pointsEquiv_symm_comp (x r)
  have hlift_inj : Function.Injective lift := by
    intro x y h
    have hxy := (finiteProductPointsEquiv H V).symm.injective h
    funext r
    exact ((hfactor r).1.pointsEquiv V).symm.injective (congrFun hxy r)
  have hproduct_inj : Function.Injective (rootPointsProduct i a V) := by
    intro x y hxy
    apply hlift_inj
    apply (cancel_mono e.hom).mp
    apply hjU.1.right_cancellation
    simpa only [Category.assoc, he, hlift] using hxy
  have hroot (r : Fin n) : a r ∈ semigroupIndivisibleRoots i A :=
    ha ▸ Set.mem_range_self r
  have hle (r : Fin n) :
      subgroup i (a r) ≤ semigroupSubgroup (AutomorphicAction.conjugation i) A := by
    rw [← weightFiltration_one_eq_subgroup hT i (a r) (hroot r).1.1]
    exact semigroupSubgroup_mono _ (cyclicTail_one_le_of_mem (hroot r).2.1)
  constructor
  · intro hg
    rw [← hjU.2, SubgroupFunctor.mem_range] at hg
    obtain ⟨y, hy⟩ := hg
    let z := y ≫ e.inv
    let x (r : Fin n) : (subgroup i (a r)).carrier V :=
      (hfactor r).1.pointsEquiv V (finiteProductPointsEquiv H V z r)
    have hx : rootPointsProduct i a V x = g := by
      change orderedPoints j (finiteProductPointsEquiv H V z) = g
      rw [← comp_orderedMultiplication, ← he]
      simpa only [z, Category.assoc, Iso.inv_hom_id_assoc] using hy
    exact ⟨x, hx, fun y hy => hproduct_inj (hy.trans hx.symm)⟩
  · rintro ⟨x, hx, _⟩
    rw [← hx]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    exact hle r V (x r).property

/-- Every selected subgroup is generated on every scheme test by its actual
selected root groups; the equality is of subgroups of the original points. -/
theorem semigroupSubgroup_carrier_eq_iSup_selectedRoots
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A : AddSubsemigroup (characterLattice T)) (hzero : 0 ∉ A)
    (V : Over (Spec (CommRingCat.of k))) :
    (semigroupSubgroup (AutomorphicAction.conjugation i) A).carrier V =
      ⨆ χ : {χ : characterLattice T | χ ∈ relativeRoots i ∧ χ ∈ A},
        (subgroup i χ.val).carrier V := by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, a, hinj, ha⟩ := exists_semigroupIndivisibleRoots_enumeration i hT A
    obtain ⟨x, hx, _⟩ :=
      (mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct i hT hE A hzero
        a hinj ha V g).mp hg
    rw [← hx]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    have hr : a r ∈ semigroupIndivisibleRoots i A := ha ▸ Set.mem_range_self r
    exact (le_iSup (fun χ : {χ : characterLattice T |
      χ ∈ relativeRoots i ∧ χ ∈ A} =>
      (subgroup i χ.val).carrier V) ⟨a r, hr.1, hr.2.1⟩) (x r).property
  · refine iSup_le fun χ => ?_
    have hle : subgroup i χ.val ≤
        semigroupSubgroup (AutomorphicAction.conjugation i) A := by
      rw [← weightFiltration_one_eq_subgroup hT i χ.val χ.property.1.1]
      exact semigroupSubgroup_mono _ (cyclicTail_one_le_of_mem χ.property.2)
    exact hle V

end Selected

section Restriction

/-- The inverse image of a positive ray under character restriction excludes
zero whenever its smaller-torus character is nonzero. -/
theorem zero_notMem_characterSemigroupPreimage_cyclicTail
    (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
    (α : characterLattice S) (hα : α ≠ 0) :
    0 ∉ characterSemigroupPreimage f (cyclicTail α 1) := by
  intro hz
  have hz' : (0 : characterLattice S) ∈ cyclicTail α 1 := by
    simpa only [mem_characterSemigroupPreimage, comp_zero] using hz
  obtain ⟨n, _, hn, hnα⟩ := hz'
  exact hS.nsmul_ne_zero hα (Nat.ne_of_gt hn) hnα

variable [Smooth G.X.hom]

/-- The smaller-torus intrinsic root functor is an actual ordered scheme
product of larger-torus root functors. -/
theorem subgroup_comp_torusHom_orderedRootProduct
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hE : HasOppositeFactorPairs i) (α : characterLattice S) (hα : α ≠ 0)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i
      (characterSemigroupPreimage f (cyclicTail α 1))) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G)
      (e : (∏ᶜ H).X ≅ U.X),
      (subgroup (CommGroupScheme.groupHom f ≫ i) α).IsRepresentedBy jU ∧
      IsClosedSubgroup jU ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsUnipotent U ∧ IsSplitUnipotent U ∧
      (∀ r, (subgroup i (a r)).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  rw [subgroup_comp_torusHom_eq_semigroupSubgroup hS hT f i α hα]
  exact semigroup_orderedRootProduct i hT hE _
    (zero_notMem_characterSemigroupPreimage_cyclicTail hS f α hα) a hinj ha

/-- Unique larger-torus root-point coordinates for each restricted root
point, on every scheme over the field. -/
theorem mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hE : HasOppositeFactorPairs i) (α : characterLattice S) (hα : α ≠ 0)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i
      (characterSemigroupPreimage f (cyclicTail α 1)))
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) :
    g ∈ (subgroup (CommGroupScheme.groupHom f ≫ i) α).carrier V ↔
      ∃! x : ∀ r, (subgroup i (a r)).carrier V, rootPointsProduct i a V x = g := by
  rw [subgroup_comp_torusHom_eq_semigroupSubgroup hS hT f i α hα]
  exact mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct i hT hE _
    (zero_notMem_characterSemigroupPreimage_cyclicTail hS f α hα) a hinj ha V g

/-- The exact restricted root group on every test scheme is generated by
all larger-torus root groups restricting to positive multiples of its root. -/
theorem subgroup_comp_torusHom_carrier_eq_iSup
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hE : HasOppositeFactorPairs i) (α : characterLattice S) (hα : α ≠ 0)
    (V : Over (Spec (CommRingCat.of k))) :
    (subgroup (CommGroupScheme.groupHom f ≫ i) α).carrier V =
      ⨆ χ : {χ : characterLattice T |
        χ ∈ relativeRoots i ∧ f ≫ χ ∈ cyclicTail α 1}, (subgroup i χ.val).carrier V := by
  rw [subgroup_comp_torusHom_eq_semigroupSubgroup hS hT f i α hα]
  exact semigroupSubgroup_carrier_eq_iSup_selectedRoots i hT hE _
    (zero_notMem_characterSemigroupPreimage_cyclicTail hS f α hα) V

end Restriction

end Langlands.GroupScheme.RelativeRoot
