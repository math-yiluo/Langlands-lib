import Langlands.GroupScheme.Rational.NonreductiveRootProducts
import Langlands.GroupScheme.Rational.RootSmoothQuotient
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots

/-! # Ordered root coordinates in smooth quotient kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.RelativeRoot.SmoothQuotient

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Smooth G.X.hom] [Smooth Q.X.hom]
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
    (q : G ⟶ Q) (hq : Smooth q.hom.hom.left)

omit [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Smooth G.X.hom] [Smooth Q.X.hom] in
private theorem conjugation_equivariant_product :
    ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ G.X),
      (AutomorphicAction.conjugation i).act s x ≫ q.hom.hom =
        (AutomorphicAction.conjugation (i ≫ q)).act s (x ≫ q.hom.hom) := by
  intro T s x
  simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

include hS hq in
/-- Smoothness prevents any new nonzero conjugation weight in the target,
even when the original torus map or its composite is not a monomorphism. -/
theorem relativeRoots_comp_subset :
    relativeRoots (i ≫ q) ⊆ relativeRoots i := by
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro hz
  have hzero := actionWeightSpace_eq_bot_of_smooth
    (AutomorphicAction.conjugation i)
    (AutomorphicAction.conjugation (i ≫ q)) hS q
    (conjugation_equivariant_product i q) hq a
    (by simpa only [actionWeightSpace_conjugation] using hz)
  exact ha.2 (by simpa only [actionWeightSpace_conjugation] using hzero)

variable (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)

include hS hq hdisj hinj ha in
/-- The original source root rays still give an exact ordered chart of the
target dynamic radical. Vanishing target factors are retained. -/
theorem exists_target_rootProduct :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ Q)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ Q)
      (e : (∏ᶜ H).X ≅ U.X),
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i ≫ q)).IsRepresentedBy jU ∧
      (∀ r, (subgroup (i ≫ q) (a r)).IsRepresentedBy (j r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
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
    exact actionWeightSupport_positiveSemigroup semigroupRealization inferInstance
      hS (i ≫ q) ν
  have hsub : actionWeightSupport c ⊤ ⊆ positiveRelativeRoots i ν := by
    rw [hsupport]
    intro χ hχ
    exact ⟨relativeRoots_comp_subset i hS q hq hχ.1, hχ.2⟩
  have hcover : (⋃ r, rootRayBlock i (a r)) = positiveRelativeRoots i ν :=
    iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
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
    exact semigroupSubgroup_mono b
      (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hfactor (r : Fin n) :
      (subgroup (i ≫ q) (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
        (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k Q inferInstance inferInstance
      S hS (i ≫ q) (a r) (hroot r).1.1.1
    exact hcyclic ▸ hrep
  let := hIso
  refine ⟨U, jU, H, (fun r => jH r ≫ jU), asIso (orderedMultiplication jH),
    ?_, hfactor, orderedMultiplication_comp jH jU⟩
  rw [dynamicUnipotentSemigroupComparison_of_semigroupRealization
    semigroupRealization Q S hS (i ≫ q) ν]
  exact hjU

/-- A target dynamic root-product chart indexed by the original source roots.
Factors whose target root functor vanishes are kept in the product. -/
structure TargetRootProductChart where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ Q
  factors : Fin n → GroupScheme (Spec (CommRingCat.of k))
  rootInclusion : ∀ r, factors r ⟶ Q
  productIso : (∏ᶜ factors).X ≅ group.X
  representsUnipotent :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i ≫ q)).IsRepresentedBy inclusion
  representsRoot : ∀ r, (subgroup (i ≫ q) (a r)).IsRepresentedBy (rootInclusion r)
  product_comp : productIso.hom ≫ inclusion.hom.hom = orderedMultiplication rootInclusion

/-- Choose the exact target chart furnished by smooth weight transport and
ordered semigroup products, with the original ordered source root indices. -/
def targetRootProductChart : TargetRootProductChart i q ν a := by
  classical
  exact Classical.choice (by
    obtain ⟨U, jU, H, j, e, hU, hj, he⟩ :=
      exists_target_rootProduct i hS q hq ν hdisj a hinj ha
    exact ⟨⟨U, jU, H, j, e, hU, hj, he⟩⟩)

include hS hq hdisj hinj ha in
/-- The full smooth quotient kernel is reflected separately in each original
ordered root coordinate, on every test scheme over the original field. -/
theorem orderedPoints_comp_eq_one_iff
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (subgroup i (a r)).IsRepresentedBy (j r))
    {T : Over (Spec (CommRingCat.of k))} (x : ∀ r, T ⟶ (H r).X) :
    orderedPoints j x ≫ q.hom.hom = 1 ↔
      ∀ r, x r ≫ (j r ≫ q).hom.hom = 1 := by
  obtain ⟨U, jU, R, l, e, hU, hl, he⟩ :=
    exists_target_rootProduct i hS q hq ν hdisj a hinj ha
  have : Mono jU.hom.hom := hU.1
  have : Mono (orderedMultiplication l) := by
    rw [← he]
    infer_instance
  let p (r : Fin n) := rootMap i q (a r) (j r) (l r) (hj r) (hl r)
  have hp (r : Fin n) : j r ≫ q = p r ≫ l r :=
    (rootMap_comp i q (a r) (j r) (l r) (hj r) (hl r)).symm
  rw [orderedPoints_map j l q p hp]
  constructor
  · intro hx
    have hpoints :
        (fun r => x r ≫ (p r).hom.hom) = (fun r => (1 : T ⟶ (R r).X)) := by
      apply (mono_orderedMultiplication_iff l).mp inferInstance T
      simpa only [orderedPoints, MonObj.one_comp, List.ofFn_const, List.prod_replicate,
        one_pow] using hx
    intro r
    rw [hp r]
    change (x r ≫ (p r).hom.hom) ≫ (l r).hom.hom = 1
    rw [congrFun hpoints r]
    simp
  · intro hx
    have hpoint (r : Fin n) : (x r ≫ (p r).hom.hom) ≫ (l r).hom.hom = 1 := by
      rw [Category.assoc]
      change x r ≫ (p r ≫ l r).hom.hom = 1
      rw [← hp r]
      exact hx r
    simp only [orderedPoints, hpoint, List.ofFn_const, List.prod_replicate, one_pow]

end Langlands.GroupScheme.RelativeRoot.SmoothQuotient
