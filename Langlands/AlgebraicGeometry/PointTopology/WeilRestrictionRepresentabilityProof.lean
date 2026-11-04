import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionRepresentabilityStatement
import Mathlib.AlgebraicGeometry.Gluing

/-! # Representability of affine Weil restriction on every test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- Transport the relative-spectrum comparison along the canonical affine
presentation of an arbitrary affine test scheme. -/
theorem affineWeilRestrictionComparison_bijective_of_isAffine
    (T : Over (Spec (CommRingCat.of A))) [IsAffine T.left] :
    Function.Bijective (affineWeilRestrictionComparison A B X T) := by
  let e := affineSchemeOverIso A T
  have hs : Function.Bijective
      (affineWeilRestrictionComparison A B X
        (ringTest A (AffineCoordinateRing A T))) := by
    have he : (affineWeilRestrictionAffineTestEquiv A B X
        (AffineCoordinateRing A T) : _ → _) =
        affineWeilRestrictionComparison A B X
          (ringTest A (AffineCoordinateRing A T)) :=
      funext (affineWeilRestrictionAffineTestEquiv_apply A B X _)
    rw [← he]
    exact (affineWeilRestrictionAffineTestEquiv A B X (AffineCoordinateRing A T)).bijective
  constructor
  · intro p q hpq
    apply (cancel_epi e.inv).mp
    apply hs.injective
    rw [affineWeilRestrictionComparison_natural,
      affineWeilRestrictionComparison_natural, hpq]
  · intro q
    obtain ⟨p, hp⟩ := hs.surjective
      ((Over.pullback (Spec.algebraMap A B)).map e.inv ≫ q)
    refine ⟨e.hom ≫ p, ?_⟩
    rw [affineWeilRestrictionComparison_natural, hp]
    change (Over.pullback (Spec.algebraMap A B)).map e.hom ≫
      ((Over.pullback (Spec.algebraMap A B)).map e.inv ≫ q) = q
    erw [← Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id,
      (Over.pullback (Spec.algebraMap A B)).map_id, Category.id_comp]

/-- Equality of canonical comparisons can be checked on an affine open cover. -/
theorem affineWeilRestrictionComparison_injective
    (T : Over (Spec (CommRingCat.of A))) :
    Function.Injective (affineWeilRestrictionComparison A B X T) := by
  intro p q hpq
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro i
  let U : Over (Spec (CommRingCat.of A)) :=
    Over.mk (T.left.affineCover.f i ≫ T.hom)
  let : IsAffine U.left := T.left.isAffine_affineCover i
  let j : U ⟶ T := Over.homMk (T.left.affineCover.f i)
  have h : j ≫ p = j ≫ q := by
    apply (affineWeilRestrictionComparison_bijective_of_isAffine A B X U).injective
    rw [affineWeilRestrictionComparison_natural,
      affineWeilRestrictionComparison_natural, hpq]
  exact congrArg (fun k => k.left) h

/-- Local inverse images of the canonical comparison glue on an arbitrary
test scheme. -/
theorem affineWeilRestrictionComparison_surjective
    (T : Over (Spec (CommRingCat.of A))) :
    Function.Surjective (affineWeilRestrictionComparison A B X T) := by
  intro q
  let F := Over.pullback (Spec.algebraMap A B)
  let 𝒰 := T.left.affineCover
  let U (i : 𝒰.I₀) : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ T.hom)
  let (i : 𝒰.I₀) : IsAffine (U i).left := T.left.isAffine_affineCover i
  let j (i : 𝒰.I₀) : U i ⟶ T := Over.homMk (𝒰.f i)
  choose p hp using fun i =>
    (affineWeilRestrictionComparison_bijective_of_isAffine A B X (U i)).surjective
      (F.map (j i) ≫ q)
  have hcompat (i k : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f k) ≫ (p i).left =
        pullback.snd (𝒰.f i) (𝒰.f k) ≫ (p k).left := by
    let V : Over (Spec (CommRingCat.of A)) :=
      Over.mk (pullback.fst (𝒰.f i) (𝒰.f k) ≫ (U i).hom)
    let a : V ⟶ U i := Over.homMk (pullback.fst (𝒰.f i) (𝒰.f k))
    let b : V ⟶ U k := Over.homMk (pullback.snd (𝒰.f i) (𝒰.f k))
      (by
        dsimp only [V, U, Over.mk_hom]
        rw [← Category.assoc, ← Category.assoc, pullback.condition])
    have hab : a ≫ j i = b ≫ j k := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have h : a ≫ p i = b ≫ p k := by
      apply affineWeilRestrictionComparison_injective A B X V
      rw [affineWeilRestrictionComparison_natural,
        affineWeilRestrictionComparison_natural, hp i, hp k]
      change F.map a ≫ (F.map (j i) ≫ q) =
        F.map b ≫ (F.map (j k) ≫ q)
      erw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, hab]
    exact congrArg (fun k => k.left) h
  let f := 𝒰.glueMorphisms (fun i => (p i).left) hcompat
  have hf : f ≫ (affineWeilRestriction A B X).hom = T.hom := by
    apply 𝒰.hom_ext
    intro i
    dsimp only [f]
    rw [← Category.assoc, 𝒰.ι_glueMorphisms]
    exact Over.w (p i)
  let p₀ : T ⟶ affineWeilRestriction A B X := Over.homMk f hf
  have hj (i : 𝒰.I₀) : j i ≫ p₀ = p i := by
    apply Over.OverMorphism.ext
    exact 𝒰.ι_glueMorphisms _ hcompat i
  refine ⟨p₀, ?_⟩
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (𝒰.pullbackCoverOfLeft T.hom (Spec.algebraMap A B))
  intro i
  change 𝒰.I₀ at i
  have h : F.map (j i) ≫ affineWeilRestrictionComparison A B X T p₀ =
      F.map (j i) ≫ q := by
    erw [← affineWeilRestrictionComparison_natural, hj i, hp i]
    rfl
  exact congrArg (fun k => k.left) h

/-- The actual finite-type affine Weil restriction represents the canonical
base-changed Hom functor on all schemes over the base. -/
theorem weilRestrictionRepresentabilityProperties :
    WeilRestrictionRepresentabilityProperties A B := by
  intro X _ _ T
  exact ⟨affineWeilRestrictionComparison_injective A B X T,
    affineWeilRestrictionComparison_surjective A B X T⟩

end Langlands.AlgebraicGeometry.PointTopology
