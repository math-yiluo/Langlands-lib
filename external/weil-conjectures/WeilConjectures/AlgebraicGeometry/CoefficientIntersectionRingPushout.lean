/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoefficientIntersectionRingData
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Affine coefficient intersection computation

Source: Stacks Project, Tags 0097, 01I9, 01IA and 02KG.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The coefficient intersection rings form the affine tensor pushout.
Source: Stacks Project, Tag 02KG, affine computation in Lemma 30.5.1.
(blueprint: aux-pc-coefficient-intersection-ring-pushout).

Proof: Lift the given cartesian square to Y = f inverse image U. Restrict it
to Z and B. The resulting cartesian square has upper left corner the open
I = W intersect f' inverse image B. All four corners are affine: U, Z and B
by hypothesis, and I by affine base change. Taking global sections gives a
pushout square of commutative rings. The appLE maps in the statement are its
maps. Naturality of appTop and cancellation of GammaSpecIso with the canonical
chart identify its A -> D map with coefficientBaseRingMap. Commutativity
provides both scalar towers; the affine ring pushout gives Algebra.IsPushout.
The argument also applies to empty affine opens (the zero ring). -/
theorem coefficientIntersection_ring_pushout
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    let A := Γ(U.toScheme, ⊤)
    let R := Γ(T', B)
    let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
    let S := Γ(X', W ⊓ f' ⁻¹ᵁ B)
    let : Algebra A R := (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let : Algebra A D := (coefficientBaseRingMap f U Z).toAlgebra
    let : Algebra D S := (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
    let : Algebra R S := (f'.appLE B (W ⊓ f' ⁻¹ᵁ B) inf_le_right).hom.toAlgebra
    let : Algebra A S := ((f'.appLE B (W ⊓ f' ⁻¹ᵁ B) inf_le_right).hom.comp
      (g.appLE ⊤ B (by simp)).hom).toAlgebra
    ∃ hD : IsScalarTower A D S, letI := hD
      ∃ hR : IsScalarTower A R S, letI := hR
        Algebra.IsPushout A R D S := by
  classical
  dsimp only
  let A := Γ(U.toScheme, ⊤)
  let R := Γ(T', B)
  let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
  let I := W ⊓ f' ⁻¹ᵁ B
  let S := Γ(X', I)
  let k := coefficientRestrictedLift f U g g' f' sq
  have hk : k ≫ (f ⁻¹ᵁ U).ι = g' :=
    ((isPullback_morphismRestrict f U).flip).lift_fst _ _ _
  have hs : IsPullback k f' (f ∣_ U) g :=
    sq.of_right' ((isPullback_morphismRestrict f U).flip)
  have he : k ⁻¹ᵁ Z = W := by
    rw [hW]
    conv_rhs => rw [← hk]
    change _ = k ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    rw [Scheme.Hom.preimage_image_eq]
  have hI : I = k ⁻¹ᵁ Z ⊓ f' ⁻¹ᵁ B := by rw [he]
  have htU : IsAffineOpen (⊤ : U.toScheme.Opens) := by
    let : IsAffine U.toScheme := hU
    exact isAffineOpen_top _
  have hp := (isIso_pushoutSection_iff hs (by simp : B ≤ g ⁻¹ᵁ ⊤)
    (by simp : Z ≤ (f ∣_ U) ⁻¹ᵁ ⊤) hI).mp
      (isIso_pushoutSection_of_isAffineOpen hs (by simp) (by simp) hI htU hB hZ)
  have ha : coefficientBaseRingMap f U Z =
      ((f ∣_ U).appLE ⊤ Z (by simp)).hom := by
    simp [coefficientBaseRingMap, Scheme.Hom.appTop, Scheme.Hom.appLE, RingHom.comp_assoc]
  let : Algebra A R := (g.appLE ⊤ B (by simp)).hom.toAlgebra
  let : Algebra A D := (coefficientBaseRingMap f U Z).toAlgebra
  let : Algebra D S :=
    (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
  let : Algebra R S := (f'.appLE B I inf_le_right).hom.toAlgebra
  let : Algebra A S := ((f'.appLE B I inf_le_right).hom.comp
    (g.appLE ⊤ B (by simp)).hom).toAlgebra
  have hD : IsScalarTower A D S := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change (f'.appLE B I inf_le_right).hom ((g.appLE ⊤ B (by simp)).hom a) =
      coefficientIntersectionRingMap f U Z g g' f' sq W hW B
        (coefficientBaseRingMap f U Z a)
    rw [ha]
    exact (ConcreteCategory.congr_hom hp.w a).symm
  have hR : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨hD, hR, ?_⟩
  apply CommRingCat.isPushout_iff_isPushout.mp
  convert hp.flip using 1 <;> first | rfl | exact congrArg CommRingCat.ofHom ha

end
end AlgebraicGeometry.Scheme.Modules
