import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.OrderedProductMaps

/-! # Ordered dynamic root products with supplied ray geometry -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Representatives

variable {B : Scheme.{u}} {G U V : GroupScheme B} {n : ℕ}
    {H R : Fin n → GroupScheme B}
    {F : SubgroupFunctor G} {Fr : Fin n → SubgroupFunctor G}
    {jU : U ⟶ G} {jV : V ⟶ G}
    {j : ∀ r, H r ⟶ G} {l : ∀ r, R r ⟶ G}

/-- Transport an ordered-product chart to specified representatives of all
its factors and of its image, over an arbitrary base. -/
def orderedProductIsoOfRepresentatives
    (hU : F.IsRepresentedBy jU) (hV : F.IsRepresentedBy jV)
    (hj : ∀ r, (Fr r).IsRepresentedBy (j r))
    (hl : ∀ r, (Fr r).IsRepresentedBy (l r))
    (e : (∏ᶜ H).X ≅ U.X) : (∏ᶜ R).X ≅ V.X := by
  let er : ∀ r, R r ≅ H r := fun r => (hl r).isoOfIsRepresentedBy (hj r)
  let p := productFactorMap (fun r => (er r).hom)
  have : IsIso p := by
    dsimp [p, productFactorMap]
    infer_instance
  exact asIso p ≪≫ e ≪≫
    (Grp.forget (Over B)).mapIso (hU.isoOfIsRepresentedBy hV)

/-- The transported chart has precisely the ordered multiplication of the
specified original factor inclusions as its ambient map. -/
theorem orderedProductIsoOfRepresentatives_hom_comp
    (hU : F.IsRepresentedBy jU) (hV : F.IsRepresentedBy jV)
    (hj : ∀ r, (Fr r).IsRepresentedBy (j r))
    (hl : ∀ r, (Fr r).IsRepresentedBy (l r))
    (e : (∏ᶜ H).X ≅ U.X)
    (he : e.hom ≫ jU.hom.hom = orderedMultiplication j) :
    (orderedProductIsoOfRepresentatives hU hV hj hl e).hom ≫ jV.hom.hom =
      orderedMultiplication l := by
  let er : ∀ r, R r ≅ H r := fun r => (hl r).isoOfIsRepresentedBy (hj r)
  let p := productFactorMap (fun r => (er r).hom)
  let eU := hU.isoOfIsRepresentedBy hV
  have hUcomp : eU.hom.hom.hom ≫ jV.hom.hom = jU.hom.hom :=
    congrArg (fun f => f.hom.hom) (hU.isoOfIsRepresentedBy_hom_comp hV)
  have hr (r : Fin n) : l r ≫ 𝟙 G = (er r).hom ≫ j r := by
    simpa only [Category.comp_id] using
      ((hl r).isoOfIsRepresentedBy_hom_comp (hj r)).symm
  change (p ≫ e.hom ≫ eU.hom.hom.hom) ≫ jV.hom.hom = _
  simp only [Category.assoc, hUcomp]
  rw [he]
  simpa only [Grp.id_hom_hom, Category.comp_id] using
    orderedMultiplication_map l j (𝟙 G) (fun r => (er r).hom) hr

end Representatives

section Field

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S)

include hS

set_option maxHeartbeats 800000 in
/-- Supplied disjoint positive rays suffice for exact dynamic root products
in a smooth connected affine field group, without a reductivity or
maximality premise. -/
theorem dynamicRootOrderedProduct_of_disjoint_positive_rays
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    {n : ℕ} (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G)
      (e : (∏ᶜ H).X ≅ U.X),
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy jU ∧
      IsClosedSubgroup jU ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsUnipotent U ∧ IsSplitUnipotent U ∧
      (∀ r, (subgroup i (a r)).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G inferInstance inferInstance S hS b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, hUsp⟩ := hUnip U jU hjU hzero
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
    exact actionWeightSupport_positiveSemigroup semigroupRealization inferInstance hS i ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)).trans hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ := hasOrderedSemigroupProducts_of_unipotent c hS hUu n
    (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      (semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hfactor (r : Fin n) :
      (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) ∧
        IsClosedSubgroup (jH r ≫ jU) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
        (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k G inferInstance inferInstance
      S hS i (a r) (hroot r).1.1.1
    obtain ⟨hHu, hHsp⟩ := (semigroupRealization k G inferInstance inferInstance S hS b
      (cyclicTail (a r) 1)).2.2.2.1 (H r) (jH r ≫ jU) hrep (fun hz =>
        hzero (cyclicTail_one_le_positiveSemigroup (hroot r).2 hz))
    exact ⟨hcyclic ▸ hrep, (hH r).2.1.comp hjUc, (hH r).2.2.1,
      (hH r).2.2.2, hHu, hHsp⟩
  let := hIso
  refine ⟨U, jU, H, (fun r => jH r ≫ jU), asIso (orderedMultiplication jH),
    ?_, hjUc, hUs, hUc, hUu, hUsp, hfactor, orderedMultiplication_comp jH jU⟩
  rw [(dynamicSemigroupComparison k G inferInstance inferInstance inferInstance S hS i ν).2.2]
  exact hjU

/-- The same root product holds for arbitrary specified representatives,
with their original inclusions into the ambient group. -/
theorem exists_dynamicRootProductIso_of_representatives
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    {n : ℕ} (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    {V : GroupScheme (Spec (CommRingCat.of k))} {jV : V ⟶ G}
    (hV : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy jV)
    {R : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (l : ∀ r, R r ⟶ G) (hl : ∀ r, (subgroup i (a r)).IsRepresentedBy (l r)) :
    ∃ e : (∏ᶜ R).X ≅ V.X, e.hom ≫ jV.hom.hom = orderedMultiplication l := by
  obtain ⟨U, jU, H, j, e, hU, _, _, _, _, _, hj, he⟩ :=
    dynamicRootOrderedProduct_of_disjoint_positive_rays i hS ν hdisj a hinj ha
  exact ⟨orderedProductIsoOfRepresentatives hU hV (fun r => (hj r).1) hl e,
    orderedProductIsoOfRepresentatives_hom_comp hU hV (fun r => (hj r).1) hl e he⟩

end Field

end Langlands.GroupScheme.RelativeRoot
