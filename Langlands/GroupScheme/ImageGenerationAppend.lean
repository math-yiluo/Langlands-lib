import Langlands.GroupScheme.ImageGenerationProducts
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! # Concatenated points and schematic dominance of image factorizations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ImageGeneration

section Points

variable {B : Scheme.{u}} {G : GroupScheme B} {V : Over B}

/-- The concatenation of an `a`-tuple and a `b`-tuple of points of `V`. -/
def appendPoint {T : Over B} {a b : ℕ} (x : T ⟶ finitePower V a)
    (y : T ⟶ finitePower V b) : T ⟶ finitePower V (a + b) :=
  Pi.lift (Fin.append (fun i => x ≫ Pi.π (fun _ : Fin a => V) i)
    (fun i => y ≫ Pi.π (fun _ : Fin b => V) i))

/-- The ordered product of a concatenation is the product of the ordered products. -/
theorem appendPoint_orderedPowerMap (f : V ⟶ G.X) {T : Over B} {a b : ℕ}
    (x : T ⟶ finitePower V a) (y : T ⟶ finitePower V b) :
    appendPoint x y ≫ orderedPowerMap f (a + b) =
      (x ≫ orderedPowerMap f a) * (y ≫ orderedPowerMap f b) := by
  rw [orderedPowerMap_points, orderedPowerMap_points, orderedPowerMap_points, List.ofFn_add,
    List.prod_append]
  simp [appendPoint]

/-- The constant `n`-tuple at a point `v`. -/
def constPoint {T : Over B} (v : T ⟶ V) (n : ℕ) : T ⟶ finitePower V n :=
  Pi.lift fun _ => v

theorem constPoint_orderedPowerMap (f : V ⟶ G.X) {T : Over B} (v : T ⟶ V) (hv : v ≫ f = 1)
    (n : ℕ) : constPoint v n ≫ orderedPowerMap f n = 1 := by
  rw [orderedPowerMap_points]
  simp [constPoint, hv]

/-- The diagonal identification of `V` with its first power. -/
def singlePoint (V : Over B) : V ⟶ finitePower V 1 := Pi.lift fun _ => 𝟙 V

theorem singlePoint_orderedPowerMap (f : V ⟶ G.X) :
    singlePoint V ≫ orderedPowerMap f 1 = f := by
  rw [orderedPowerMap_points]
  simp [singlePoint]

/-- Appending copies of a unit point does not change the ordered product. -/
def padMap (v : 𝟙_ (Over B) ⟶ V) (n m : ℕ) : finitePower V n ⟶ finitePower V (n + m) :=
  appendPoint (𝟙 _) (toUnit _ ≫ constPoint v m)

theorem padMap_orderedPowerMap (f : V ⟶ G.X) (v : 𝟙_ (Over B) ⟶ V) (hv : v ≫ f = 1)
    (n m : ℕ) : padMap v n m ≫ orderedPowerMap f (n + m) = orderedPowerMap f n := by
  rw [padMap, appendPoint_orderedPowerMap, Category.assoc,
    constPoint_orderedPowerMap f v hv, MonObj.comp_one, mul_one, Category.id_comp]

/-- A morphism factors through a closed immersion over the base when the kernel of the
closed immersion is contained in its kernel. -/
theorem exists_over_factor_of_ker_le {X Y Z : Over B} (i : X ⟶ Z) [IsClosedImmersion i.left]
    (g : Y ⟶ Z) (h : i.left.ker ≤ g.left.ker) : ∃ a : Y ⟶ X, a ≫ i = g := by
  let a := IsClosedImmersion.lift i.left g.left h
  have ha : a ≫ i.left = g.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← i.w, ← Category.assoc, ha]
  exact g.w

end Points

section Dominance

/-- The factorization through the scheme-theoretic image is schematically dominant when
the target is affine. -/
theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsAffine Y] : IsSchemeTheoreticallyDominant f.toImage := by
  have : IsAffine f.image := isAffine_of_isAffineHom f.imageι
  have hinj := f.toImage_app_injective ⟨⊤, isAffineOpen_top Y⟩
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [Scheme.Hom.ker_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj

variable {B : Scheme.{u}}

/-- Right whiskering by a flat object preserves quasi-compact schematic dominance. -/
theorem isSchemeTheoreticallyDominant_whiskerRight {X Y : Over B} (t : X ⟶ Y) (R : Over B)
    [IsSchemeTheoreticallyDominant t.left] [QuasiCompact t.left] [Flat R.hom] :
    IsSchemeTheoreticallyDominant (t ▷ R).left := by
  have outer : IsPullback ((t ▷ R).left ≫ pullback.snd Y.hom R.hom)
      (pullback.fst X.hom R.hom) R.hom (t.left ≫ Y.hom) := by
    rw [Over.whiskerRight_left_snd, Over.w t]
    exact (IsPullback.of_hasPullback X.hom R.hom).flip
  have H := IsPullback.of_right outer (Over.whiskerRight_left_fst t)
    (IsPullback.of_hasPullback Y.hom R.hom).flip
  exact IsSchemeTheoreticallyDominant.of_isPullback H.flip

/-- Left whiskering by a flat object preserves quasi-compact schematic dominance. -/
theorem isSchemeTheoreticallyDominant_whiskerLeft {X Y : Over B} (t : X ⟶ Y) (R : Over B)
    [IsSchemeTheoreticallyDominant t.left] [QuasiCompact t.left] [Flat R.hom] :
    IsSchemeTheoreticallyDominant (R ◁ t).left := by
  have outer : IsPullback ((R ◁ t).left ≫ pullback.fst R.hom Y.hom)
      (pullback.snd R.hom X.hom) R.hom (t.left ≫ Y.hom) := by
    rw [Over.whiskerLeft_left_fst, Over.w t]
    exact IsPullback.of_hasPullback R.hom X.hom
  have H := IsPullback.of_right outer (Over.whiskerLeft_left_snd t)
    (IsPullback.of_hasPullback R.hom Y.hom)
  exact IsSchemeTheoreticallyDominant.of_isPullback H.flip

/-- The tensor square of a quasi-compact schematically dominant morphism between flat
objects is schematically dominant. -/
theorem isSchemeTheoreticallyDominant_tensorHom {X Y : Over B} (t : X ⟶ Y)
    [IsSchemeTheoreticallyDominant t.left] [QuasiCompact t.left] [Flat X.hom] [Flat Y.hom] :
    IsSchemeTheoreticallyDominant (t ⊗ₘ t).left := by
  have := isSchemeTheoreticallyDominant_whiskerRight t X
  have := isSchemeTheoreticallyDominant_whiskerLeft t Y
  rw [tensorHom_def, Over.comp_left]
  infer_instance

end Dominance

section Geometric

variable {X Y S : Scheme.{u}} [Subsingleton S] [IsIntegral S] (p : X ⟶ Y) (g : Y ⟶ S)
  [IsSchemeTheoreticallyDominant p] [QuasiCompact p]

/-- A continuous map with dense range from an irreducible space has irreducible target. -/
theorem irreducibleSpace_of_denseRange {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {h : α → β} (hc : Continuous h) (hd : DenseRange h) [IrreducibleSpace α] :
    IrreducibleSpace β := by
  have hirr : IsIrreducible (closure (Set.range h)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ α).image h hc.continuousOn).closure
  rw [hd.closure_range] at hirr
  exact (irreducibleSpace_def β).2 hirr

include p in
/-- Over a one-point integral base, geometric reducedness descends along a quasi-compact
schematically dominant morphism. -/
theorem geometricallyReduced_of_isSchemeTheoreticallyDominant
    [GeometricallyReduced (p ≫ g)] : GeometricallyReduced g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : IsReduced (pullback (p ≫ g) x) :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K x
  have : IsReduced (pullback p (pullback.fst g x)) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso g x p).hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd p (pullback.fst g x))

include p in
/-- Over a one-point integral base, geometric irreducibility descends along a
quasi-compact schematically dominant morphism. -/
theorem geometricallyIrreducible_of_isSchemeTheoreticallyDominant
    [GeometricallyIrreducible (p ≫ g)] : GeometricallyIrreducible g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : IrreducibleSpace ↥(pullback (p ≫ g) x) :=
    pullback_of_geometrically GeometricallyIrreducible.geometrically_irreducibleSpace K x
  have : IrreducibleSpace ↥(pullback p (pullback.fst g x)) :=
    (pullbackRightPullbackFstIso g x p).hom.homeomorph.irreducibleSpace_iff.2 this
  exact irreducibleSpace_of_denseRange (pullback.snd p (pullback.fst g x)).continuous
    (pullback.snd p (pullback.fst g x)).denseRange

end Geometric

end Langlands.GroupScheme.ImageGeneration
