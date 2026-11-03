/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Worker 105 adapts the range-factorization and surjectivity arguments of
Langlands.TauCeti.RingTheory.WeilRestriction.Basic (upstream commit
8428d6217f74afa72531df0bc85d7b57ab72810f) to the finite-type construction,
then transfers surjectivity to the actual affine scheme map.
-/
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionClosedImmersionStatement

/-! # Proof of closed-immersion preservation for finite-type Weil restriction -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.WeilRestrictionFiniteType

variable {A B C T : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing T]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  [Algebra B C] [Algebra.FiniteType B C] [Algebra A T]

/-- A represented point factors through a subalgebra exactly when its
tensor-valued point factors through the tensor image of that subalgebra. -/
theorem range_le_iff_range_homEquiv_le
    {g : WeilRestrictionFiniteType A B C →ₐ[A] T} {S : Subalgebra A T} :
    g.range ≤ S ↔
      (homEquiv A B C T g).range ≤
        (Algebra.TensorProduct.lTensor (S := B) B S.val).range := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← AlgHom.val_comp_codRestrict g S fun x ↦ h ⟨x, rfl⟩, homEquiv_comp]
    exact AlgHom.range_comp_le_range _ _
  · have hinj : Function.Injective (Algebra.TensorProduct.lTensor (S := B) B S.val) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    let v : C →ₐ[B] B ⊗[A] S := (AlgEquiv.ofInjective _ hinj).symm.toAlgHom.comp
      ((homEquiv A B C T g).codRestrict _ fun c ↦ h ⟨c, rfl⟩)
    have hv : (Algebra.TensorProduct.lTensor (S := B) B S.val).comp v =
        homEquiv A B C T g := by
      ext c
      exact congrArg Subtype.val ((AlgEquiv.ofInjective _ hinj).apply_symm_apply _)
    have hg : S.val.comp ((homEquiv A B C S).symm v) = g :=
      (homEquiv A B C T).injective <| by
        rw [homEquiv_comp, Equiv.apply_symm_apply, hv]
    rw [← hg, AlgHom.range_comp]
    exact Subalgebra.map_le.2 fun x _ ↦ x.2

/-- Finite-type affine Weil restriction preserves surjections. -/
theorem map_surjective {D : Type*} [CommRing D] [Algebra B D]
    [Algebra.FiniteType B D] {φ : C →ₐ[B] D} (hφ : Function.Surjective φ) :
    Function.Surjective (map A B φ) := by
  have h := (range_le_iff_range_homEquiv_le (g := map A B φ)).1 le_rfl
  rw [homEquiv_map] at h
  rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← Algebra.range_id,
    range_le_iff_range_homEquiv_le]
  rintro _ ⟨d, rfl⟩
  obtain ⟨c, rfl⟩ := hφ d
  simpa using h ⟨c, rfl⟩

end Langlands.Algebra.WeilRestrictionFiniteType

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The constructed map of actual affine Weil restrictions is a closed
immersion when the original morphism is a closed immersion. -/
theorem affineWeilRestrictionMap_isClosedImmersion
    {X Y : Over (Spec (CommRingCat.of B))}
    [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (affineWeilRestrictionMap A B f).left := by
  have hs : Function.Surjective (affineCoordinatePullback B f) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom
      (WeilRestrictionFiniteType.map A B (affineCoordinatePullback B f)).toRingHom)
    (WeilRestrictionFiniteType.map_surjective hs)

theorem weilRestrictionClosedImmersionProperties_proof :
    WeilRestrictionClosedImmersionProperties A B := by
  constructor
  · intro C D _ _ _ _ _ _ φ hφ
    exact WeilRestrictionFiniteType.map_surjective hφ
  · intro X Y _ _ _ _ f hf
    exact affineWeilRestrictionMap_isClosedImmersion A B f

end Langlands.AlgebraicGeometry.PointTopology
