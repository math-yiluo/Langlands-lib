import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Mathlib.CategoryTheory.Comma.Basic

/-! # Actual Picard comparisons for affine infinitesimal squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {k A B C : Type u} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- An algebra homomorphism gives its actual contravariant affine-base arrow. -/
def affineBaseMap (a : A →ₐ[k] B) : affineBase k B ⟶ affineBase k A :=
  Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom (algebraMap k B))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun r : k →+* B ↦ Spec.map (CommRingCat.ofHom r))
      a.comp_algebraMap)

/-- The affine-base arrows retain actual composition. -/
lemma affineBaseMap_comp (a : A →ₐ[k] B) (b : B →ₐ[k] C) :
    affineBaseMap (b.comp a) = affineBaseMap b ≫ affineBaseMap a := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (b.comp a).toRingHom) =
    Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

namespace PicardGroupoid

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)

/-- Two actual bundles together with an actual isomorphism on the common restriction. -/
abbrev SquareGluingData := Comma (pullback i₁) (pullback i₂)

/-- Arrows of gluing data are compatible pairs of actual bundle isomorphisms. -/
instance squareGluingDataGroupoid : Groupoid (SquareGluingData i₁ i₂) :=
  Groupoid.ofIsIso (fun h ↦ by
    change IsIso (Comma.isoMk (asIso h.left) (asIso h.right) h.w).hom
    infer_instance)

variable (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (w : i₁ ≫ j₁ = i₂ ≫ j₂)

/-- The overlap isomorphism uses the ordinary coherent pullback comparisons. -/
def squarePullbackIso :
    pullback j₁ ⋙ pullback i₁ ≅ pullback j₂ ⋙ pullback i₂ :=
  pullbackComp i₁ j₁ ≪≫ eqToIso (congrArg pullback w) ≪≫
    (pullbackComp i₂ j₂).symm

/-- Restrict an actual bundle and its actual isomorphisms across a commuting square. -/
def squareGluingComparison : PicardGroupoid Y ⥤ SquareGluingData i₁ i₂ where
  obj L :=
    { left := (pullback j₁).obj L
      right := (pullback j₂).obj L
      hom := (squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L }
  map h :=
    { left := (pullback j₁).map h
      right := (pullback j₂).map h
      w := (squarePullbackIso i₁ i₂ j₁ j₂ w).hom.naturality h }
  map_id L := by
    apply Comma.hom_ext <;> simp
  map_comp a b := by
    apply Comma.hom_ext <;> simp

variable {S X : Scheme.{u}} (f : X ⟶ S)
  {T₀ T₁ T₂ T : Over S}
  (a : T₀ ⟶ T₁) (b : T₀ ⟶ T₂) (p : T₁ ⟶ T) (q : T₂ ⟶ T)
  (h : a ≫ p = b ≫ q)

/-- The actual base-changed square commutes on its total schemes. -/
lemma relativeSquare_comm (h : a ≫ p = b ≫ q) :
    (relativeSpace f).map a ≫ (relativeSpace f).map p =
      (relativeSpace f).map b ≫ (relativeSpace f).map q := by
  rw [← Functor.map_comp, h, Functor.map_comp]

/-- The actual Picard comparison on a square of test schemes. -/
def relativeSquareComparison :
    PicardGroupoid ((relativeSpace f).obj T) ⥤
      SquareGluingData ((relativeSpace f).map a) ((relativeSpace f).map b) :=
  squareGluingComparison _ _ _ _ (relativeSquare_comm f a b p q h)

section Affine

variable {R : Type u} [CommRing R] [Algebra k R]
  (f : X ⟶ Spec (CommRingCat.of k))
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

/-- A ring pullback square gives the actual commuting square of affine bases. -/
lemma affineSquare_comm
    (hR : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom)) :
    affineBaseMap a ≫ affineBaseMap p = affineBaseMap b ≫ affineBaseMap q := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom p.toRingHom) =
    Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      Spec.map (CommRingCat.ofHom q.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, hR.w]

/-- The canonical comparison for actual relative line bundles on a ring square. -/
def affineSquareComparison :
    PicardGroupoid ((relativeSpace f).obj (affineBase k R)) ⥤
      SquareGluingData ((relativeSpace f).map (affineBaseMap a))
        ((relativeSpace f).map (affineBaseMap b)) :=
  relativeSquareComparison f (affineBaseMap a) (affineBaseMap b)
    (affineBaseMap p) (affineBaseMap q) (affineSquare_comm p q a b h)

end Affine

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
