import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Flat tensor base change of actual commutative-ring pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalFlatBaseChange

variable {k S R A B C : Type u}
  [CommRing k] [CommRing S] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k S] [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]

/-- Tensoring by a flat algebra preserves the actual ring pullback square. -/
theorem isPullback_tensor [Module.Flat k S]
    (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
    (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom)) :
    IsPullback
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) q).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) a).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom) := by
  have hm : IsPullback (ModuleCat.ofHom p.toLinearMap) (ModuleCat.ofHom q.toLinearMap)
      (ModuleCat.ofHom a.toLinearMap) (ModuleCat.ofHom b.toLinearMap) := by
    let : ReflectsLimit
        (cospan (ModuleCat.ofHom a.toLinearMap) (ModuleCat.ofHom b.toLinearMap))
        (forget (ModuleCat k)) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    exact (h.map (forget CommRingCat)).of_map_of_faithful (forget (ModuleCat k))
  have ht := (hm.map (MonoidalCategory.tensorLeft (ModuleCat.of k S))).map
    (forget (ModuleCat k))
  let : ReflectsLimit
      (cospan
        (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) a).toRingHom)
        (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom))
      (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  exact ht

section Equivalence

variable [Module.Flat k S]
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

/-- The tensor of the given pullback ring is the actual categorical pullback
of the two tensor maps. -/
def tensorPullbackEquiv :
    S ⊗[k] R ≃+* ↥(pullback
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) a).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom)) :=
  (isPullback_tensor (S := S) p q a b h).isoPullback.commRingCatIsoToRingEquiv

@[simp]
theorem tensorPullbackEquiv_fst (z : S ⊗[k] R) :
    (pullback.fst
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) a).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom)).hom
      (tensorPullbackEquiv p q a b h z) =
      Algebra.TensorProduct.map (AlgHom.id k S) p z := by
  exact congrArg (fun f : CommRingCat.of (S ⊗[k] R) ⟶ CommRingCat.of (S ⊗[k] A) =>
    f.hom z) (isPullback_tensor (S := S) p q a b h).isoPullback_hom_fst

@[simp]
theorem tensorPullbackEquiv_snd (z : S ⊗[k] R) :
    (pullback.snd
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) a).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom)).hom
      (tensorPullbackEquiv p q a b h z) =
      Algebra.TensorProduct.map (AlgHom.id k S) q z := by
  exact congrArg (fun f : CommRingCat.of (S ⊗[k] R) ⟶ CommRingCat.of (S ⊗[k] B) =>
    f.hom z) (isPullback_tensor (S := S) p q a b h).isoPullback_hom_snd

end Equivalence

end Langlands.AlgebraicGeometry.Picard.InfinitesimalFlatBaseChange
