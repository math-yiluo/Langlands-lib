import Langlands.GroupScheme.Rational.NonreductiveRootProducts
import Langlands.GroupScheme.Rational.SmoothTangentWeights
import Langlands.GroupScheme.Rational.SemigroupProductRestriction
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.KernelOrderedProductChart

/-! # Smooth quotient kernels in ordered root coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Coordinatewise kernel detection for ordered full root products under a
smooth homomorphism, with supplied disjoint positive root rays. -/
def SmoothQuotientRootCoordinatesStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom Q.X.hom] [Smooth Q.X.hom]
    (i : S.toGrp ⟶ G), IsSplitTorus S.toGrp →
    ∀ (ν : cocharacterLattice S) (q : G ⟶ Q), Smooth q.hom.hom.left →
    (∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S))) →
    ∀ (n : ℕ) (a : Fin n → characterLattice S), Function.Injective a →
      Set.range a = indivisiblePositiveRoots i ν →
    ∀ (T : Over (Spec (CommRingCat.of k))) (x : Fin n → (T ⟶ G.X)),
      (∀ r, x r ∈ (subgroup i (a r)).carrier T) →
      ((List.ofFn x).prod ≫ q.hom.hom = 1 ↔ ∀ r, x r ≫ q.hom.hom = 1)

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom Q.X.hom] [Smooth Q.X.hom]
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
    (ν : cocharacterLattice S) (q : G ⟶ Q)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom Q.X.hom] [Smooth Q.X.hom] in
private theorem smooth_quotient_conjugation_equivariant :
    ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ G.X),
      (AutomorphicAction.conjugation i).act s x ≫ q.hom.hom =
        (AutomorphicAction.conjugation (i ≫ q)).act s (x ≫ q.hom.hom) := by
  intro T s x
  simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

include hS in
/-- A smooth homomorphism cannot introduce a positive relative-root weight. -/
theorem positiveRelativeRoots_comp_subset_of_smooth
    (hq : Smooth q.hom.hom.left) :
    positiveRelativeRoots (i ≫ q) ν ⊆ positiveRelativeRoots i ν := by
  intro χ hχ
  refine ⟨⟨hχ.1.1, ?_⟩, hχ.2⟩
  intro hzero
  have hz : actionWeightSpace (AutomorphicAction.conjugation i) χ = ⊥ := by
    rwa [actionWeightSpace_conjugation]
  have ht := actionWeightSpace_eq_bot_of_smooth
    (AutomorphicAction.conjugation i) (AutomorphicAction.conjugation (i ≫ q))
    hS q (smooth_quotient_conjugation_equivariant i q) hq χ hz
  rw [actionWeightSpace_conjugation] at ht
  exact hχ.1.2 ht

include hS in
set_option maxHeartbeats 800000 in
private theorem exists_target_root_product_on_source_rays
    (hq : Smooth q.hom.hom.left)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    {n : ℕ} (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ Q)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (jH : ∀ r, H r ⟶ U),
      Mono jU.hom.hom ∧
      (∀ r, (subgroup (i ≫ q) (a r)).IsRepresentedBy (jH r ≫ jU)) ∧
      IsIso (orderedMultiplication jH) := by
  let b := AutomorphicAction.conjugation (i ≫ q)
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k Q inferInstance inferInstance S hS b A
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
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots (i ≫ q) ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization inferInstance hS (i ≫ q) ν
  have hsub : actionWeightSupport c ⊤ ⊆ positiveRelativeRoots i ν := by
    rw [hsupport]
    exact positiveRelativeRoots_comp_subset_of_smooth i hS ν q hq
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock i (a r)) = positiveRelativeRoots i ν :=
    iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)
  obtain ⟨H, jH, hH, hIso⟩ :=
    (hasOrderedSemigroupProducts_of_unipotent c hS hUu).for_larger_support
      (positiveRelativeRoots i ν) hsub n (fun r => rootRayBlock i (a r))
      hcover hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      (semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  refine ⟨U, jU, H, jH, hjU.1, fun r => ?_, hIso⟩
  have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
      (jH r ≫ jU) := by
    rw [← hsemigroup r]
    exact (hH r).1.comp hjU
  exact cyclicRootFunctorComparison k Q inferInstance inferInstance S hS
    (i ≫ q) (a r) (hroot r).1.1.1 ▸ hrep

include hS in
/-- For full positive-multiple root functors, a smooth homomorphism kills an
ordered product precisely when it kills every coordinate. -/
theorem root_product_comp_eq_one_iff_of_smooth
    (hq : Smooth q.hom.hom.left)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    {n : ℕ} (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    {T : Over (Spec (CommRingCat.of k))} (x : Fin n → (T ⟶ G.X))
    (hx : ∀ r, x r ∈ (subgroup i (a r)).carrier T) :
    (List.ofFn x).prod ≫ q.hom.hom = 1 ↔ ∀ r, x r ≫ q.hom.hom = 1 := by
  classical
  have hmap (l : List (T ⟶ G.X)) :
      l.prod ≫ q.hom.hom = (l.map (fun z => z ≫ q.hom.hom)).prod := by
    induction l with
    | nil => simp
    | cons z l ih => simp only [List.prod_cons, List.map_cons, MonObj.mul_comp, ih]
  rw [hmap, List.map_ofFn]
  constructor
  · intro hprod
    obtain ⟨U, jU, H, jH, hjU, hH, hIso⟩ :=
      exists_target_root_product_on_source_rays i hS ν q hq hdisj a hinj ha
    let y : ∀ r, T ⟶ (H r).X := fun r =>
      ((hH r).pointsEquiv T).symm
        ⟨x r ≫ q.hom.hom, comp_mem_subgroup i (a r) q (hx r)⟩
    have hy (r : Fin n) : y r ≫ (jH r ≫ jU).hom.hom = x r ≫ q.hom.hom :=
      (hH r).pointsEquiv_symm_comp _
    have hp : (finiteProductPointsEquiv H T).symm y ≫ orderedMultiplication jH = 1 := by
      apply (cancel_mono jU.hom.hom).mp
      rw [Category.assoc, orderedMultiplication_comp,
        finiteProductPointsEquiv_symm_orderedMultiplication, MonObj.one_comp]
      simpa only [orderedPoints, hy, Function.comp_def] using hprod
    have hz : (finiteProductPointsEquiv H T).symm y = 1 := by
      apply (cancel_mono (orderedMultiplication jH)).mp
      rw [hp, one_comp_orderedMultiplication]
    have hyone : y = 1 := by
      have h := congrArg (finiteProductPointsEquiv H T) hz
      simpa only [MulEquiv.apply_symm_apply, map_one] using h
    intro r
    rw [← hy r, hyone]
    exact MonObj.one_comp _
  · intro h
    simp only [Function.comp_def, h]
    simp

/-- Smooth homomorphisms detect kernels coordinatewise in the supplied
ordered positive-root chart. -/
theorem smoothQuotientRootCoordinates : SmoothQuotientRootCoordinatesStatement.{u} := by
  intro k _ S G Q _ _ _ _ i hS ν q hq hdisj n a hinj ha T x hx
  exact root_product_comp_eq_one_iff_of_smooth i hS ν q hq hdisj a hinj ha x hx

end Langlands.GroupScheme.RelativeRoot
