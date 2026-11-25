/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionPurityTransport
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantTransport

/-!
# Base change of the section invariant isomorphism `𝒞(g, s) ≅ Λ_B(c)[2c]`

For `g : V ⟶ B` smooth of relative dimension `c` with a closed section `s`, and the base change
`g' : V' ⟶ B'`, `s'` along an étale `eV : V' ⟶ V` (so that `eB ≫ s = s' ≫ eV` is cartesian), the
section invariant isomorphisms `𝒞(g, s) ≅ Λ_B(c)[2c]` and `𝒞(g', s') ≅ Λ_{B'}(c)[2c]`
(`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection`) correspond under
`LeB^* Ls^* ω_g ≅ Ls'^* LeV^* ω_g ≅ Ls'^* ω_{g'}` and `LeB^*(Λ_B(c)[2c]) ≅ Λ_{B'}(c)[2c]`
(`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection_baseChange`), given the
compatibility `hε` of the composition isomorphisms `Rs^! ω_g ≅ Λ_B`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`) with the
exceptional base change. The purity of the section is compatible with base change by
`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection_baseChange`, and the
section invariant construction by
`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_baseChange`.
This is the geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_sectionInvariantTwistShiftIsoOfSection`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section TwistShift

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- The pullback of `Λ_Y(m)[2m] = twistShift (Λ_Y)` along `e : X ⟶ Y`: through
`AlgebraicGeometry.Etale.twistShiftConstantComplexIso` it is the pullback identification
`Le^*(Λ_Y(m)[2m]) ≅ Λ_X(m)[2m]` of the shifted twisting objects. The geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.twistShiftConstantComplexIso`. -/
noncomputable def twistShiftConstantComplexBaseChangeIso {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (e : X ⟶ Y) (m : ℤ) :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ Y m).obj (constantComplex Λ Y)) ≅
      (twistShift Λ X m).obj (constantComplex Λ X) :=
  (L((e)^*[ModuleCat.{u + 1} Λ])).mapIso (twistShiftConstantComplexIso Λ Y m) ≪≫
    leftDerivedUpperStarTateShiftIso Λ e m ≪≫ (twistShiftConstantComplexIso Λ X m).symm

variable {V B V' B' : Scheme.{u}} {s : B ⟶ V} {s' : B' ⟶ V'} {eV : V' ⟶ V} {eB : B' ⟶ B}
  (hsq : CommSq eB s' s eV) [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ V']
  [HasInvertibleExponent Λ B] [HasInvertibleExponent Λ B']

/-- The pullback identifications `Le^*(Λ(m)[2m]) ≅ Λ(m)[2m]` are compatible with a commutative
square `eB ≫ s = s' ≫ eV`, through the square isomorphism `LeB^* Ls^* ≅ Ls'^* LeV^*`. -/
lemma leftDerivedUpperStarTateShiftIso_square (m : ℤ) :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateShiftIso Λ s m).hom ≫
        (leftDerivedUpperStarTateShiftIso Λ eB m).hom =
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq ((tateObject Λ V m)⟦2 * m⟧) ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateShiftIso Λ eV m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ s' m).hom := by
  have h₁ := leftDerivedUpperStarTateShiftIso_comp (Λ := Λ) eB s (eB ≫ s) rfl m
  have h₂ := leftDerivedUpperStarTateShiftIso_comp (Λ := Λ) s' eV (eB ≫ s) hsq.w m
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIsoInvApp, derivedSquareUpperStarIso, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Category.assoc, ← h₃, Iso.inv_hom_id_app_assoc]

end TwistShift

section Section

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]
  {V B V' B' : Scheme.{u}} (c : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension c g]
  [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
  (g' : V' ⟶ B') [SmoothOfRelativeDimension c g'] [HasCompactification g'] (s' : B' ⟶ V')
  [IsClosedImmersion s'] (hs' : s' ≫ g' = 𝟙 B')
  (eV : V' ⟶ V) [AlgebraicGeometry.Etale eV] {eB : B' ⟶ B} (hsq : IsPullback eB s' s eV)
  {k k' : Type u} [Field k] [Field k'] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] (aB' : B' ⟶ Spec (.of k')) [IsSeparated aB']
  [LocallyOfFiniteType aB'] [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ V']
  [HasInvertibleExponent Λ B] [HasInvertibleExponent Λ B']

/-- **The section invariant isomorphism `𝒞(g, s) ≅ Λ_B(c)[2c]` is compatible with étale base
change**, given the compatibility `hε` of the composition isomorphisms `Rs^! ω_g ≅ Λ_B` with the
exceptional base change (for `vω : LeV^* ω_g ≅ ω_{g'}`). The geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_sectionInvariantTwistShiftIsoOfSection`:
the purity of the section is compatible with base change
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection_baseChange`), and so is
the section invariant construction
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_baseChange`). -/
theorem sectionInvariantTwistShiftIsoOfSection_baseChange
    (vω : (L((eV)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) ≅ dualizingComplex Λ g')
    (hε : (L((eB)^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app (dualizingComplex Λ g) ≫
          (R(s')^![Λ]).map vω.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g' s' hs').hom) :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (sectionInvariantTwistShiftIsoOfSection Λ c g s hs aB).hom ≫
        (twistShiftConstantComplexBaseChangeIso Λ eB c).hom =
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) hsq.toCommSq (dualizingComplex Λ g) ≫
        (L((s')^*[ModuleCat.{u + 1} Λ])).map vω.hom ≫
        (sectionInvariantTwistShiftIsoOfSection Λ c g' s' hs' aB').hom := by
  have hθ := rightDerivedUpperShriekTateObjectIsoOfSection_baseChange Λ c g s hs g' s' hs' eV
    hsq aB aB'
  have hτ := leftDerivedUpperStarTateShiftIso_square Λ hsq.toCommSq (c : ℤ)
  have hL := leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso_baseChange Λ hsq vω
    (leftDerivedUpperStarTateShiftIso Λ eV c) (isInvertible_dualizingComplex Λ (d := c) g)
    ((isInvertible_tateObject Λ V c).shift (2 * (c : ℤ)))
    (isInvertible_dualizingComplex Λ (d := c) g')
    ((isInvertible_tateObject Λ V' c).shift (2 * (c : ℤ)))
    (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g s hs aB)
    (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs)
    (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g' s' hs' aB')
    (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g' s' hs') hθ hε
  simp only [sectionInvariantTwistShiftIsoOfSection, twistShiftConstantComplexBaseChangeIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (L((eB)^*[ModuleCat.{u + 1} Λ]))
      (twistShiftConstantComplexIso Λ B c).inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% hτ, reassoc_of% hL]

end Section

end AlgebraicGeometry.Etale
