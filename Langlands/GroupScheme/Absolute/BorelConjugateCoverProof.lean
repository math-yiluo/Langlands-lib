import Langlands.GroupScheme.Absolute.BorelConjugateCoverStatement
import Langlands.GroupScheme.Absolute.BorelPointContainmentProof
import Langlands.GroupScheme.Absolute.BorelPointContainmentDensity
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.JacobsonSpace

/-! # Proof: the conjugates of a Borel subgroup cover the group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelConjugateCover

/-- In a Jacobson space, a constructible set without closed points is empty. -/
theorem eq_empty_of_isConstructible_of_inter_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {s : Set X} (hs : IsConstructible s) (h : s ∩ closedPoints X = ∅) :
    s = ∅ := by
  revert h
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro h
    by_contra hne
    have hlc : IsLocallyClosed (U \ V) :=
      hU.1.isLocallyClosed.inter hV.1.isClosed_compl.isLocallyClosed
    obtain ⟨y, hy⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.2 hne) hlc
    rw [h] at hy
    exact hy
  | sup s _ t _ hs' ht' =>
    intro h
    change (s ∪ t) ∩ closedPoints X = ∅ at h
    rw [Set.union_inter_distrib_right, Set.union_empty_iff] at h
    change s ∪ t = ∅
    rw [hs' h.1, ht' h.2, Set.union_empty]

variable {k : Type u} [Field k]

open BorelPointContainment in
/-- Every rational point of `G` is a conjugate `x i(b) x⁻¹` of a rational point `b` of a fixed
Borel subgroup `i : B ⟶ G`. -/
theorem exists_lift_conjugation_eq [IsAlgClosed k] {G B : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : B ⟶ G} (hi : IsBorelSubgroup i) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X), lift x b ≫ conjugation i = g := by
  obtain ⟨B', i', b', hi', hb'⟩ := borelPointContainment k G g
  obtain ⟨x, φ, hφ⟩ := (borelConjugacy k G).2 B B' i i' hi hi'
  refine ⟨x, b' ≫ φ.inv.hom.hom, ?_⟩
  have e := congrArg (fun f : B ⟶ G => (b' ≫ φ.inv.hom.hom) ≫ f.hom.hom) hφ
  simp only [Grp.comp_hom_hom] at e
  rw [← Category.assoc, comp_innerIso_hom, constantPoint_self] at e
  have h1 : φ.inv.hom.hom ≫ φ.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  rw [lift_conjugation, e, Category.assoc, reassoc_of% h1, hb']

end BorelConjugateCover

open BorelPointContainment BorelConjugateCover in
/-- **The conjugates of a Borel subgroup cover the group** (Milne, Theorem 17.33(b)). -/
theorem borelConjugateCover : BorelConjugateCoverStatement.{u} := by
  intro k _ _ G _ _ _ B i hi
  change Surjective (conjugation i).left
  have : Smooth B.X.hom := hi.smooth
  have : IsAffineHom B.X.hom := hi.isClosedSubgroup.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : LocallyOfFiniteType (G.X ⊗ B.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : QuasiCompact (G.X ⊗ B.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : CompactSpace (G.X ⊗ B.X).left :=
    QuasiCompact.compactSpace_of_compactSpace (G.X ⊗ B.X).hom
  have : LocallyOfFiniteType (conjugation i).left := by
    have : LocallyOfFiniteType ((conjugation i).left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hcons : IsConstructible (Set.range (conjugation i).left) := by
    rw [← Set.image_univ]
    exact (conjugation i).left.isConstructible_image .univ
  have hcl : (Set.range (conjugation i).left)ᶜ ∩ closedPoints G.X.left = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzc⟩
    obtain ⟨g, hg⟩ := exists_rationalPoint_of_isClosed z hzc
    obtain ⟨x, b, hxb⟩ := exists_lift_conjugation_eq hi g
    refine hz ⟨(lift x b).left (IsLocalRing.closedPoint k), ?_⟩
    rw [← hg, ← hxb, comp_left_apply]
  have h := eq_empty_of_isConstructible_of_inter_closedPoints hcons.compl hcl
  rw [Set.compl_empty_iff] at h
  exact ⟨Set.range_eq_univ.1 h⟩

end Langlands.GroupScheme
