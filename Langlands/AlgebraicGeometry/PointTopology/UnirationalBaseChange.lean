import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual unirational parametrizations after field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A Cartesian square preserves dense image when its base-change
projection is an open map. -/
theorem denseRange_of_isPullback_of_isOpenMap
    {P X Y Z : Scheme.{u}} {pX : P ⟶ X} {pY : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback pX pY f g) (hf : DenseRange f) (hg : IsOpenMap g) :
    DenseRange pY := by
  have hrange : Set.range pY = g ⁻¹' Set.range f := by
    simpa using Scheme.image_preimage_eq_of_isPullback h Set.univ
  change Dense (Set.range pY)
  rw [hrange]
  exact hf.preimage hg

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The actual map from the scalar extension of an affine open into the
scalar extension of its parametrized scheme. -/
def affineOpenBaseChangeMap
    {ι : Type u} (U : (𝔸(ι; Spec (CommRingCat.of k))).Opens)
    {X : Over (Spec (CommRingCat.of k))}
    (f : Over.mk (U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))) ⟶ X) :
    Over.mk (((AffineSpace.map ι (Spec.algebraMap k K)) ⁻¹ᵁ U).ι ≫
        (𝔸(ι; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))) ⟶
      (Over.pullback (Spec.algebraMap k K)).obj X :=
  Over.homMk
    (pullback.lift
      ((AffineSpace.map ι (Spec.algebraMap k K)) ∣_ U ≫ f.left)
      (((AffineSpace.map ι (Spec.algebraMap k K)) ⁻¹ᵁ U).ι ≫
        (𝔸(ι; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)))
      (by
        have hw : f.left ≫ X.hom =
            U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
          Over.w f
        rw [Category.assoc, hw, ← Category.assoc, morphismRestrict_ι]
        simp only [Category.assoc, AffineSpace.map_over]))
    (pullback.lift_snd _ _ _)

/-- The map on parametrizations is Cartesian over the original morphism. -/
theorem isPullback_affineOpenBaseChangeMap
    {ι : Type u} (U : (𝔸(ι; Spec (CommRingCat.of k))).Opens)
    {X : Over (Spec (CommRingCat.of k))}
    (f : Over.mk (U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))) ⟶ X) :
    IsPullback
      ((AffineSpace.map ι (Spec.algebraMap k K)) ∣_ U)
      (affineOpenBaseChangeMap (K := K) U f).left
      f.left (pullback.fst X.hom (Spec.algebraMap k K)) := by
  have hU := (isPullback_morphismRestrict
    (AffineSpace.map ι (Spec.algebraMap k K)) U).paste_vert
      (AffineSpace.isPullback_map (n := ι) (Spec.algebraMap k K))
  have hU' : IsPullback
      ((AffineSpace.map ι (Spec.algebraMap k K)) ∣_ U)
      (((AffineSpace.map ι (Spec.algebraMap k K)) ⁻¹ᵁ U).ι ≫
        (𝔸(ι; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)))
      (f.left ≫ X.hom) (Spec.algebraMap k K) := by
    simpa only [Over.w f, Over.mk_hom] using hU
  have hsnd : (affineOpenBaseChangeMap (K := K) U f).left ≫
      pullback.snd X.hom (Spec.algebraMap k K) =
      ((AffineSpace.map ι (Spec.algebraMap k K)) ⁻¹ᵁ U).ι ≫
        (𝔸(ι; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
    pullback.lift_snd _ _ _
  have hfst : (AffineSpace.map ι (Spec.algebraMap k K)) ∣_ U ≫ f.left =
      (affineOpenBaseChangeMap (K := K) U f).left ≫
        pullback.fst X.hom (Spec.algebraMap k K) :=
    (pullback.lift_fst _ _ _).symm
  exact IsPullback.of_bot (by rw [hsnd]; exact hU') hfst
    (IsPullback.of_hasPullback X.hom (Spec.algebraMap k K))

/-- Dense image of the original parametrization gives dense image after
any extension of its ground field. -/
theorem denseRange_affineOpenBaseChangeMap
    {ι : Type u} (U : (𝔸(ι; Spec (CommRingCat.of k))).Opens)
    {X : Over (Spec (CommRingCat.of k))}
    (f : Over.mk (U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))) ⟶ X) (hf : DenseRange f.left) :
    DenseRange (affineOpenBaseChangeMap (K := K) U f).left :=
  denseRange_of_isPullback_of_isOpenMap
    (isPullback_affineOpenBaseChangeMap (K := K) U f) hf
    (pullback.fst X.hom (Spec.algebraMap k K)).isOpenMap

/-- An actual unirational parametrization survives every extension of
the ground field, with the same finite coordinate type. -/
theorem IsUnirational.baseChange
    {X : Over (Spec (CommRingCat.of k))} (hX : IsUnirational k X) :
    IsUnirational K ((Over.pullback (Spec.algebraMap k K)).obj X) := by
  obtain ⟨ι, hι, U, hU, f, hf⟩ := hX
  have hg : Surjective (Spec.algebraMap k K) :=
    ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hsurj : Surjective (AffineSpace.map ι (Spec.algebraMap k K)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (AffineSpace.isPullback_map (n := ι) (Spec.algebraMap k K)).flip hg
  refine ⟨ι, hι, (AffineSpace.map ι (Spec.algebraMap k K)) ⁻¹ᵁ U,
    ?_, affineOpenBaseChangeMap U f, denseRange_affineOpenBaseChangeMap U f hf⟩
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy⟩ :=
    (AffineSpace.map ι (Spec.algebraMap k K)).surjective x
  exact ⟨y, by simpa [hy] using hx⟩

end Langlands.AlgebraicGeometry.PointTopology
