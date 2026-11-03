import Langlands.GroupScheme.Absolute.CentralizerProductConjugacy
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.JacobsonSpace

/-! # Closedness of the centralizer product from rational closure points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralizerProduct

/-- Every nonempty constructible set in a Jacobson space contains a closed point. -/
theorem constructible_nonempty_inter_closedPoints
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {s : Set X} (hs : IsConstructible s) :
    s.Nonempty → (s ∩ closedPoints X).Nonempty := by
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    exact fun h ↦ nonempty_inter_closedPoints h
      (hU.1.isLocallyClosed.inter hV.1.isClosed_compl.isLocallyClosed)
  | sup s _ t _ hs ht =>
    intro h
    rcases h with ⟨x, hx | hx⟩
    · obtain ⟨y, hy, hyc⟩ := hs ⟨x, hx⟩
      exact ⟨y, Or.inl hy, hyc⟩
    · obtain ⟨y, hy, hyc⟩ := ht ⟨x, hx⟩
      exact ⟨y, Or.inr hy, hyc⟩

/-- A constructible set in a Noetherian Jacobson space is closed if it contains
every closed point of its closure. -/
theorem isClosed_of_constructible_of_closedPoints
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [JacobsonSpace X]
    {s : Set X} (hs : IsConstructible s)
    (hp : _root_.closure s ∩ closedPoints X ⊆ s) : IsClosed s := by
  have hc : IsConstructible (_root_.closure s) := by
    apply IsConstructible.of_compl
    exact (show IsRetrocompact (_root_.closure s)ᶜ from
      fun _ _ _ ↦ NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl
  apply isClosed_of_closure_subset
  intro x hx
  by_contra hxs
  obtain ⟨y, ⟨hy, hyn⟩, hyc⟩ :=
    constructible_nonempty_inter_closedPoints (hc.sdiff hs) ⟨x, hx, hxs⟩
  exact hyn (hp ⟨hy, hyc⟩)

section RationalPoints

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Chevalley and the Jacobson property turn rational closure-point factorization
into closedness of a finite-type morphism's image. -/
theorem isClosed_range_of_rational_closure_points
    {X Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] [CompactSpace X.left]
    [LocallyOfFiniteType Y.hom] [CompactSpace Y.left]
    (f : X ⟶ Y)
    (hp : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y,
      Set.range a.left ⊆ _root_.closure (Set.range f.left) →
        ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, p ≫ f = a) :
    IsClosed (Set.range f.left) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsNoetherian X.left := ⟨⟩
  let : IsNoetherian Y.left := ⟨⟩
  let : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hc : IsConstructible (Set.range f.left) := by
    simpa only [Set.image_univ] using
      f.left.isConstructible_image (s := Set.univ) IsConstructible.univ
  apply isClosed_of_constructible_of_closedPoints hc
  rintro y ⟨hy, hyc⟩
  change IsClosed {y} at hyc
  let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y :=
    Over.homMk (pointOfClosedPoint Y.hom y hyc) (pointOfClosedPoint_comp Y.hom y hyc)
  have ha : Set.range a.left ⊆ _root_.closure (Set.range f.left) := by
    rintro _ ⟨z, rfl⟩
    change pointOfClosedPoint Y.hom y hyc z ∈ _
    rw [pointOfClosedPoint_apply]
    exact hy
  obtain ⟨p, hp⟩ := hp a ha
  refine ⟨p.left (IsLocalRing.closedPoint k), ?_⟩
  have he := congrArg
    (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y =>
      q.left (IsLocalRing.closedPoint k)) hp
  exact he.trans (pointOfClosedPoint_apply Y.hom y hyc (IsLocalRing.closedPoint k))

end RationalPoints

section Centralizer

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {M B G D : GroupScheme (Spec (CommRingCat.of k))}

/-- Every rational point of the reduced product closure lifts to the actual product. -/
def HasRationalClosurePointLifts (j : M ⟶ G) (b : B ⟶ G) : Prop :=
  ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ imageClosure j b,
    ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X ⊗ B.X,
      p ≫ productHom j b = a ≫ closureInclusion j b

/-- Rational factorization of every point of the reduced image closure proves that
the actual centralizer-product image is closed. -/
theorem product_image_isClosed_of_closure_points
    [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType B.X.hom] [IsAffineHom B.X.hom]
    [LocallyOfFiniteType G.X.hom] [CompactSpace G.X.left]
    (j : M ⟶ G) (b : B ⟶ G)
    (hp : HasRationalClosurePointLifts j b) :
    IsClosed (Set.range (productHom j b).left) := by
  let : LocallyOfFiniteType (M.X ⊗ B.X).hom := by
    change LocallyOfFiniteType (pullback.fst M.X.hom B.X.hom ≫ M.X.hom)
    infer_instance
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : IsAffine (M.X ⊗ B.X).left := by
    change IsAffine (pullback M.X.hom B.X.hom)
    infer_instance
  let : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  apply isClosed_range_of_rational_closure_points (productHom j b)
  intro r hr
  obtain ⟨a, ha⟩ := factors_closure_of_range_subset j b r hr
  obtain ⟨p, hp⟩ := hp a
  exact ⟨p, hp.trans ha⟩

/-- The remaining same-projection conjugacy input implies closedness of the actual
centralizer-product image over an algebraically closed field. -/
theorem product_image_isClosed_of_same_projection
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G) [Mono b.hom.hom]
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    [LocallyOfFiniteType G.X.hom] [CompactSpace G.X.left]
    (q : B ⟶ D) (hD : IsSplitTorus D)
    (hc : ∀ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B,
      ψ ≫ q = Dynamic.restrictCocharacter b χ hχ ≫ q →
        HomConjugate ψ (Dynamic.restrictCocharacter b χ hχ)) :
    IsClosed (Set.range (productHom j b).left) :=
  product_image_isClosed_of_closure_points j b
    (closure_point_factors_of_same_projection χ j hrep b hb hχ q hD hc)

end Centralizer

end Langlands.GroupScheme.CentralizerProduct
