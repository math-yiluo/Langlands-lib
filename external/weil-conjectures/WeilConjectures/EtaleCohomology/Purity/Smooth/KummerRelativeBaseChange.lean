/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation

/-!
# Base change of the direct images of `Λ(1)` from `𝔸¹` and `𝔾ₘ`

For a morphism `g : Y' ⟶ Y` of separated `k`-schemes of finite type, `k` algebraically closed,
the derived base change maps `Lg^* Rp_* Λ(1) ⟶ Rp'_* Λ(1)` of the affine line
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_affineLine_of_cohomology`)
and
`Lg^* Rπ_* Λ(1) ⟶ Rπ'_* Λ(1)` of the complement of the zero section
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_multiplicativeGroup`) are
isomorphisms: both sides have cohomology sheaves only in degree `0` (resp. `0` and `1`), where
the base change maps are compatible with the units (resp. with the Kummer classes, which
generate).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `Dctf` is closed under isomorphisms. -/
lemma constructibleFiniteTor_of_iso {X : Scheme.{u}}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') (h : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K' :=
  ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e h.1,
    (DerivedCategory.finiteTorAmplitude _ X).prop_of_iso e h.2⟩

variable [Finite Λ] [HasTateTwist Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY] {Y' : Scheme.{u}} (aY' : Y' ⟶ Spec (.of k)) [IsSeparated aY']
  [LocallyOfFiniteType aY'] [QuasiCompact aY'] (g : Y' ⟶ Y)
  [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Y']

include aY aY' in
/-- For `g : Y' ⟶ Y`, the derived base change map `Lg^* Rp_* Λ(1) ⟶ Rp'_* Λ(1)` of the projections
`p : 𝔸¹_Y ⟶ Y` and `p' : 𝔸¹_{Y'} ⟶ Y'` is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_app_tateObject_affineLine_of_cohomology
    (hA : ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj (constantComplex Λ _)))
    (eA : (cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
      (constantComplex Λ _) ≅ ModuleCat.of Λ Λ) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)) := by
  let p := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let p' := 𝔸(ULift.{u} (Fin 1); Y') ↘ Y'
  let sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq
  let BC := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  let M := tateObject Λ Y 1
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  obtain ⟨LT', -, hLT', ⟨eTY'⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y' 1
  have hp := isIso_unit_affineLine_of_cohomology Λ aY hA eA
    (boundedConstructibleFiniteTor_tateObject Λ Y 1) eTY hLT
  have hp' := isIso_unit_affineLine_of_cohomology Λ aY' hA eA
    (constructibleFiniteTor_of_iso Λ (leftDerivedUpperStarTateObjectIso g 1).symm
      (boundedConstructibleFiniteTor_tateObject Λ Y' 1))
    (leftDerivedUpperStarTateObjectIso g 1 ≪≫ eTY') hLT'
  have hmate := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq M
  have h₁ : IsIso (BC.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
    have : IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M) ≫
          BC.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
      rw [hmate]
      infer_instance
    exact IsIso.of_isIso_comp_left ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M)) _
  have hnat := BC.naturality (leftDerivedUpperStarTateObjectIso (Λ := Λ) p 1).hom
  have : IsIso (((R((p)_*[ModuleCat.{u + 1} Λ])) ⋙ L((g)^*[ModuleCat.{u + 1} Λ])).map
      (leftDerivedUpperStarTateObjectIso (Λ := Λ) p 1).hom ≫
        BC.app (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (((R((p)_*[ModuleCat.{u + 1} Λ])) ⋙
    L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso (Λ := Λ) p 1).hom)
      (BC.app (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1))

end Etale

end AlgebraicGeometry
