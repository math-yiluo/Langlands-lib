import Langlands.GroupScheme.Lie.SurjectiveDifferentialLifting
import Langlands.GroupScheme.Lie.SurjectiveDifferentialStatement
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.GeometricConnectedness

/-! # Smooth surjectivity from the actual identity differential -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
  (f : H ⟶ G)

/-- A rational point in the scheme image has a rational lift over an algebraically closed field. -/
theorem exists_rational_lift_of_mem_range
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g.left (IsLocalRing.closedPoint k) ∈ Set.range f.hom.hom.left) :
    ∃ h : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X, h ≫ f.hom.hom = g := by
  let : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hgb : g.left ≫ G.X.hom = 𝟙 _ := Over.w g
  have hgc : IsClosed ({g.left (IsLocalRing.closedPoint k)} : Set G.X.left) :=
    (pointEquivClosedPoint G.X.hom ⟨g.left, hgb⟩).property
  have hZ : IsClosed (f.hom.hom.left ⁻¹' {g.left (IsLocalRing.closedPoint k)}) :=
    hgc.preimage f.hom.hom.left.continuous
  obtain ⟨x, hx⟩ := hg
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints
    (⟨x, hx⟩ : (f.hom.hom.left ⁻¹' {g.left (IsLocalRing.closedPoint k)}).Nonempty)
    hZ.isLocallyClosed
  let h : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X :=
    Over.homMk (pointOfClosedPoint H.X.hom c hc) (by simp)
  refine ⟨h, Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq G.X.hom
  · rw [Over.comp_left, Category.assoc, Over.w f.hom.hom]
    exact pointOfClosedPoint_comp H.X.hom c hc
  · exact hgb
  · change f.hom.hom.left (pointOfClosedPoint H.X.hom c hc (IsLocalRing.closedPoint k)) = _
    rw [pointOfClosedPoint_apply]
    exact hcZ

/-- A smooth homomorphism into an irreducible finite-type group is onto on rational points. -/
theorem rationalPoints_surjective_of_smooth [IrreducibleSpace G.X.left]
    (hf : Smooth f.hom.hom.left) :
    Function.Surjective (fun h : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X =>
      h ≫ f.hom.hom) := by
  let := hf
  let : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  let U := Set.range f.hom.hom.left
  have hU : IsOpen U := f.hom.hom.left.isOpenMap.isOpen_range
  have hUne : U.Nonempty := ⟨_, ⟨(1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X).left
    (IsLocalRing.closedPoint k), rfl⟩⟩
  intro g
  let L := FiniteIndexTransfer.leftMul G g
  have : IsIso L.left := inferInstanceAs (IsIso ((Over.forget _).map L))
  have hL : IsOpen (L.left ⁻¹' U) := hU.preimage L.left.continuous
  have hLne : (L.left ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy⟩ := L.left.surjective x
    refine ⟨y, ?_⟩
    change L.left y ∈ U
    rw [hy]
    exact hx
  obtain ⟨c, ⟨hcU, hcL⟩, hc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hU hL hUne hLne) (hU.inter hL).isLocallyClosed
  let r : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom c hc) (by simp)
  have hr : r.left (IsLocalRing.closedPoint k) = c := pointOfClosedPoint_apply _ _ _ _
  obtain ⟨a, ha⟩ := exists_rational_lift_of_mem_range f r (by change r.left _ ∈ U; rw [hr]; exact hcU)
  have hgr : (g * r).left (IsLocalRing.closedPoint k) ∈ U := by
    have h : r ≫ L = g * r := by
      rw [FiniteIndexTransfer.comp_leftMul, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← h]
    change L.left (r.left (IsLocalRing.closedPoint k)) ∈ U
    rw [hr]
    exact hcL
  obtain ⟨b, hb⟩ := exists_rational_lift_of_mem_range f (g * r) hgr
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) ≫ f.hom.hom = g
  rw [MonObj.mul_comp, GrpObj.inv_comp, hb, ha, mul_inv_cancel_right]

/-- Rational surjectivity and generalization give surjectivity on all scheme points. -/
theorem surjective_of_smooth_of_irreducible [IrreducibleSpace G.X.left]
    (hf : Smooth f.hom.hom.left) : Surjective f.hom.hom.left := by
  let := hf
  let : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  refine ⟨fun w => ?_⟩
  obtain ⟨c, hcw, hc⟩ := nonempty_inter_closedPoints
    (⟨w, subset_closure (Set.mem_singleton w)⟩ : (closure ({w} : Set G.X.left)).Nonempty)
    (isClosed_closure (s := ({w} : Set G.X.left))).isLocallyClosed
  let r : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom c hc) (by simp)
  obtain ⟨h, hh⟩ := rationalPoints_surjective_of_smooth f hf r
  change h ≫ f.hom.hom = r at hh
  have hspec : w ⤳ f.hom.hom.left (h.left (IsLocalRing.closedPoint k)) := by
    rw [specializes_iff_mem_closure]
    have he : f.hom.hom.left (h.left (IsLocalRing.closedPoint k)) = c := by
      change (h ≫ f.hom.hom).left (IsLocalRing.closedPoint k) = c
      rw [hh]
      exact pointOfClosedPoint_apply _ _ _ _
    rw [he]
    exact hcw
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap f.hom.hom.left hspec
  exact ⟨z, hz⟩

end AlgebraicallyClosed

section Descent

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [Smooth G.X.hom]
  [IsAffineHom G.X.hom]
  [ConnectedSpace G.X.left]

/-- Scheme surjectivity descends from the algebraic closure for a smooth homomorphism
with smooth source and connected smooth affine target. -/
theorem surjective_of_smooth_of_connected (f : H ⟶ G)
    (hf : Smooth f.hom.hom.left) : Surjective f.hom.hom.left := by
  let b := toAlgebraicClosure k
  let Hb := (GroupScheme.baseChange b).obj H
  let Gb := (GroupScheme.baseChange b).obj G
  let fb := (GroupScheme.baseChange b).map f
  have houter : IsPullback
      (fb.hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst H.X.hom b) b (f.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom b).flip
  have hp := houter.of_right
    (show fb.hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst H.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip
  have hfb : Smooth fb.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Smooth) hp.flip hf
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have : IsIntegral Gb.X.left :=
    pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := G.X.hom))
      (AlgebraicClosure k) b
  have : Smooth Hb.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : Smooth Gb.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : Surjective fb.hom.hom.left := surjective_of_smooth_of_irreducible fb hfb
  have : Surjective b := inferInstance
  have : Surjective (fb.hom.hom.left ≫ pullback.fst G.X.hom b) := inferInstance
  have : Surjective (pullback.fst H.X.hom b ≫ f.hom.hom.left) := hp.w ▸ inferInstance
  exact Surjective.of_comp (pullback.fst H.X.hom b) f.hom.hom.left

end Descent

/-- The exact actual-differential criterion, at every universe. -/
theorem smoothSurjectiveOfSurjectiveDifferential :
    SmoothSurjectiveOfSurjectiveDifferentialStatement.{u} := by
  intro k _ H G hH hG hAffH hAffG hConnG f hf
  let := hH
  let := hG
  let := hAffH
  let := hAffG
  let := hConnG
  have hsm : Smooth f.hom.hom.left := smooth_of_surjective_differential f hH hf
  exact ⟨hsm, surjective_of_smooth_of_connected f hsm⟩

end Langlands.GroupScheme.Lie
