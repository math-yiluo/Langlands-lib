/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenComplement
public import WeilConjectures.SixFunctors.Etale.DivisorComplementDirectImage

/-!
# Direct images from the complement of a regular divisor

Let `W` be smooth over an algebraically closed field `k`, `i : D ⟶ W` a regular closed immersion
of codimension one with `D` regular, and `j : U ⟶ W` the complementary open immersion. For a
prime `ℓ` invertible in `k`, the higher direct images of the constant sheaf `ℤ/ℓ` are, near every
point of `D`,

`j_* ℤ/ℓ = ℤ/ℓ`, `R¹j_* ℤ/ℓ = i_* ℤ/ℓ` (that is, `i_* ℤ/ℓ(-1)`, the twist being trivialized by a
primitive `ℓ`-th root of unity of `k`), and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`

(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`).

This follows from purity for the regular immersion `i`
(see
`Etale.nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion`:
`Ri^! (ℤ/ℓ(1)[2]) ≅ ℤ/ℓ` near every point of `D`) and the long exact sequence of cohomology
sheaves of the supported localization triangle `i_* Ri^! L ⟶ L ⟶ Rj_* j^* L ⟶`
(`AlgebraicGeometry.Etale.supportedLocalizationTriangle_mem_distTriang`). The twist is
trivialized because `Λ_W(1)` is pulled back from `Spec k`, on which every Tate twist is constant
(`AlgebraicGeometry.Etale.nonempty_tateObject_iso_unit`).

## Main statements

- `AlgebraicGeometry.Etale.exists_higherDirectImage_constantSheaf_of_isRegularImmersion`: the
  computation for a finite coefficient ring `Λ` whose exponent is invertible in `k`.
- `AlgebraicGeometry.Etale.exists_hasDivisorComplementDirectImages_of_isRegularImmersion`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` with `B` concentrated in degree `0` and `A`
concentrated in degree `2`, the object `C` has no cohomology in degrees `q ≥ 2`. -/
lemma isZero_homology_obj₃_of_two_le (T : Pretriangulated.Triangle (_root_.DerivedCategory C))
    (hT : T ∈ distTriang _)
    (h₁ : ∀ m : ℤ, m ≠ 2 → IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₁))
    (h₂ : ∀ m : ℤ, m ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₂))
    (q : ℤ) (hq : 2 ≤ q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor C q).obj T.obj₃) :=
  (_root_.DerivedCategory.HomologySequence.exact₃ T hT q (q + 1)).isZero_X₂
    ((h₂ q (by omega)).eq_of_src _ _) ((h₁ (q + 1) (by omega)).eq_of_tgt _ _)

/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` with `H⁰(A) = H¹(A) = 0`, the map
`H⁰(B) ⟶ H⁰(C)` is an isomorphism. -/
lemma isIso_homology_zero_map_mor₂ (T : Pretriangulated.Triangle (_root_.DerivedCategory C))
    (hT : T ∈ distTriang _)
    (h₀ : IsZero ((_root_.DerivedCategory.homologyFunctor C 0).obj T.obj₁))
    (h₁ : IsZero ((_root_.DerivedCategory.homologyFunctor C 1).obj T.obj₁)) :
    IsIso ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂) := by
  have : Mono ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.exact₂ T hT 0).mono_g (h₀.eq_of_src _ _)
  have : Epi ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.exact₃ T hT 0 1).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Triangle

section ClosedImmersion

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For a closed immersion `f`, the cohomology sheaves of `Rf_! K` are the direct images of
those of `K`: `Rf_! = Rf_* = f_*` is exact. -/
noncomputable def homologyRightDerivedLowerShriekIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [HasCompactification f] (q : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (_root_.DerivedCategory.homologyFunctor _ q).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≅
      ((f)_*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f
  (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ f).app K ≪≫
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app K) ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).symm.app K

end ClosedImmersion

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, via `lemma-class-of-point--1`.

**Direct images from the complement of a smooth divisor**, for a finite coefficient ring `Λ`
whose exponent is invertible in the algebraically closed field `k`. Let `W` be smooth over `k`,
`i : D ⟶ W` a regular closed immersion of codimension one with `D` regular and `j : U ⟶ W` the
complementary open immersion. Every point of `D` has an open neighbourhood `W₀` in `W` over
which, writing `j₀ : U ∩ W₀ ⟶ W₀` and `i₀ : D ∩ W₀ ⟶ W₀`,

`R⁰j₀_* Λ ≅ Λ`, `R¹j₀_* Λ ≅ i₀_* Λ` and `R^q j₀_* Λ = 0` for `q ≥ 2`.

On an affine neighbourhood `W₀` where `W` and `D` have constant relative dimensions, purity gives
`Ri₀^! (Λ(1)[2]) ≅ Λ`, and `Λ_{W₀}(1) ≅ Λ_{W₀}` is pulled back from `Spec k`, where the Tate
twist is trivial. Hence `Ri₀^! Λ ≅ Λ[-2]`, and the claim is the long exact cohomology sequence
of the supported localization triangle `i₀_* Ri₀^! Λ ⟶ Λ ⟶ Rj₀_* Λ ⟶`. -/
theorem exists_higherDirectImage_constantSheaf_of_isRegularImmersion (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)] {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {W D U : Scheme.{u}} (aW : W ⟶ Spec (.of k))
    [Smooth aW] (i : D ⟶ W) [IsRegularImmersion 1 i]
    (hD : ∀ x : D, IsRegularLocalRing (D.presheaf.stalk x)) (j : U ⟶ W) [IsOpenImmersion j]
    (hj : Set.range j = (Set.range i)ᶜ) (x : D) :
    ∃ (W₀ : W.Opens) (_ : i x ∈ W₀),
      (∀ q : ℕ, 2 ≤ q → IsZero (higherDirectImage Λ (pullback.snd j W₀.ι) q
        ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))) ∧
      Nonempty (higherDirectImage Λ (pullback.snd j W₀.ι) 0
          ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅
        (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ∧
      Nonempty (higherDirectImage Λ (pullback.snd j W₀.ι) 1
          ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅
        (pullback.snd i W₀.ι)_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) := by
  obtain ⟨W₀, hW₀, hxW₀, n, m, hmn, hn, hm⟩ :=
    IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension 1 i aW hD x
  refine ⟨W₀, hxW₀, ?_⟩
  -- the hypotheses of purity for `i₀ : D ∩ W₀ ⟶ W₀`
  have : IsAffine W₀ := hW₀
  have : HasInvertibleExponent Λ W₀ := .of_hom (W₀.ι ≫ aW)
  have : HasInvertibleExponent Λ (pullback i W₀.ι) :=
    .of_hom (pullback.snd i W₀.ι ≫ W₀.ι ≫ aW)
  have : IsRegularImmersion 1 (pullback.snd i W₀.ι) :=
    IsRegularImmersion.of_isPullback 1 (IsPullback.of_hasPullback i W₀.ι)
  have : HasCompactification (W₀.ι ≫ aW) := HasCompactification.of_isQuasiAffine _
  have : SmoothOfRelativeDimension m (pullback.snd i W₀.ι ≫ W₀.ι ≫ aW) := by
    rw [← Category.assoc, ← pullback.condition, ← pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, Category.assoc]
    have : SmoothOfRelativeDimension (0 + m)
        ((pullbackRestrictIsoRestrict i W₀).hom ≫ (i ⁻¹ᵁ W₀).ι ≫ i ≫ aW) := inferInstance
    rwa [zero_add] at this
  have : HasCompactification (pullback.snd i W₀.ι ≫ W₀.ι ≫ aW) :=
    HasCompactification.of_isQuasiAffine _
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion Λ 1 n
    m hmn (pullback.snd i W₀.ι) (W₀.ι ≫ aW)
  -- `Λ_{W₀}(1) ≅ Λ_{W₀}`, pulled back from `Spec k`
  obtain ⟨ψ⟩ := nonempty_tateObject_iso_unit Λ k ((1 : ℕ) : ℤ)
  let τ : tateObject Λ W₀ ((1 : ℕ) : ℤ) ≅ constantComplex Λ W₀ :=
    (leftDerivedUpperStarTateObjectIso (W₀.ι ≫ aW) ((1 : ℕ) : ℤ)).symm ≪≫
      (L((W₀.ι ≫ aW)^*[ModuleCat.{u + 1} Λ])).mapIso ψ ≪≫
      leftDerivedUpperStarConstantComplexIso Λ (W₀.ι ≫ aW)
  -- `Ri₀^! Λ ≅ Λ[-2]`
  let a : ℤ := 2 * ((1 : ℕ) : ℤ)
  let K := (R(pullback.snd i W₀.ι)^![Λ]).obj (constantComplex Λ W₀)
  let eK : K⟦a⟧ ≅ constantComplex Λ (pullback i W₀.ι) :=
    (((R(pullback.snd i W₀.ι)^![Λ]).commShiftIso a).app _).symm ≪≫
      (R(pullback.snd i W₀.ι)^![Λ]).mapIso ((shiftFunctor _ a).mapIso τ.symm) ≪≫
      e₂
  -- the supported localization triangle of `Λ_{W₀}`
  have hij : Set.range (pullback.snd i W₀.ι) = (Set.range (pullback.snd j W₀.ι))ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_compl, hj,
      compl_compl]
  let T := supportedLocalizationTriangle Λ (pullback.snd i W₀.ι)
    (pullback.snd j W₀.ι) (constantComplex Λ W₀)
    (supportedLocalizationBoundary _ _ _ hij (constantComplex Λ W₀))
  have hT : T ∈ distTriang _ := supportedLocalizationTriangle_mem_distTriang _ _ _ hij _
  -- the cohomology sheaves of `i₀_* Ri₀^! Λ = i₀_* Λ[-2]`
  let E (q p : ℤ) (h : a + q = p) : (_root_.DerivedCategory.homologyFunctor _ p).obj T.obj₁ ≅
      (pullback.snd i W₀.ι)_*[ModuleCat.{u + 1} Λ].obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj (constantComplex Λ (pullback i W₀.ι))) :=
    (((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso a q p h).app _).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((((R(pullback.snd i W₀.ι)_![ModuleCat.{u + 1} Λ]).commShiftIso a).app K).symm ≪≫
          (R(pullback.snd i W₀.ι)_![ModuleCat.{u + 1} Λ]).mapIso eK) ≪≫
      homologyRightDerivedLowerShriekIso Λ (pullback.snd i W₀.ι) q _
  have h₁ (p : ℤ) (hp : p ≠ 2) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj T.obj₁) :=
    (Functor.map_isZero _ (isZero_homology_constantComplex Λ _ (p - a) (by omega))).of_iso
      (E (p - a) p (by omega))
  have h₂ (p : ℤ) (hp : p ≠ 0) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj T.obj₂) :=
    isZero_homology_constantComplex Λ W₀ p hp
  -- the cohomology sheaves of `Rj₀_* Λ`
  let F (q : ℤ) : higherDirectImage Λ (pullback.snd j W₀.ι) q
        ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅
      (_root_.DerivedCategory.homologyFunctor _ q).obj T.obj₃ :=
    higherDirectImageIsoHomologyRightDerivedLowerStar Λ _ q _ ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((R((pullback.snd j W₀.ι)_*[ModuleCat.{u + 1} Λ])).mapIso
          ((unitIsoSingleFunctorConstantSheaf Λ _).symm ≪≫
            (leftDerivedUpperStarConstantComplexIso Λ (pullback.snd j W₀.ι)).symm))
  have := isIso_homology_zero_map_mor₂ T hT (h₁ 0 (by norm_num)) (h₁ 1 (by norm_num))
  have := isIso_homologySequenceδ_one_two T hT h₂
  refine ⟨fun q hq ↦ (isZero_homology_obj₃_of_two_le T hT h₁ h₂ q (by exact_mod_cast hq)).of_iso
      (F q), ⟨F 0 ≪≫ (asIso ((_root_.DerivedCategory.homologyFunctor _ 0).map T.mor₂)).symm ≪≫
      homologyZeroConstantComplexIso Λ W₀⟩, ⟨F 1 ≪≫
      asIso (_root_.DerivedCategory.HomologySequence.δ T 1 2 rfl) ≪≫ E 0 2 rfl ≪≫
      (pullback.snd i W₀.ι)_*[ModuleCat.{u + 1} Λ].mapIso
        (homologyZeroConstantComplexIso Λ (pullback i W₀.ι))⟩⟩

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, via `lemma-class-of-point--1`.

**Direct images from the complement of a smooth divisor.** Let `W` be smooth over an
algebraically closed field `k`, `i : D ⟶ W` a regular closed immersion of codimension one with
`D` regular and `j : U ⟶ W` the complementary open immersion. Every point of `D` has an open
neighbourhood `W₀` in `W` over which, writing `j₀ : U ∩ W₀ ⟶ W₀` and `i₀ : D ∩ W₀ ⟶ W₀`,

`R⁰j₀_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j₀_* ℤ/ℓ ≅ i₀_* ℤ/ℓ` and `R^q j₀_* ℤ/ℓ = 0` for `q ≥ 2`.

This is `AlgebraicGeometry.Etale.exists_higherDirectImage_constantSheaf_of_isRegularImmersion`
for `Λ = ℤ/ℓ`: it follows from purity `Ri^! (ℤ/ℓ(1)[2]) ≅ ℤ/ℓ` near the points of `D`,
the localization triangle `i_* Ri^! ℤ/ℓ ⟶ ℤ/ℓ ⟶ Rj_* ℤ/ℓ ⟶` and the trivialization
`ℤ/ℓ(1) ≅ ℤ/ℓ` over the algebraically closed field `k`. -/
theorem exists_hasDivisorComplementDirectImages_of_isRegularImmersion {k : Type u} [Field k]
    [IsAlgClosed k] {W D U : Scheme.{u}} (aW : W ⟶ Spec (.of k)) [Smooth aW] (i : D ⟶ W)
    [IsRegularImmersion 1 i] (hD : ∀ x : D, IsRegularLocalRing (D.presheaf.stalk x))
    (j : U ⟶ W) [IsOpenImmersion j] (hj : Set.range j = (Set.range i)ᶜ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (x : D) :
    ∃ (W₀ : W.Opens) (_ : i x ∈ W₀),
      HasDivisorComplementDirectImages ℓ (pullback.snd j W₀.ι) (pullback.snd i W₀.ι) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero (ringChar (ZModCoeff.{u} ℓ)) := ⟨by
    rw [ringChar.eq (ZModCoeff.{u} ℓ) ℓ]
    exact NeZero.ne ℓ⟩
  have : HasInvertibleExponent (ZModCoeff.{u} ℓ) (Spec (.of k)) :=
    ⟨ℓ, Nat.pos_of_ne_zero (NeZero.ne ℓ), ULift.ext (by simp),
      by simpa using (Ne.isUnit hℓ).map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  exact exists_higherDirectImage_constantSheaf_of_isRegularImmersion (ZModCoeff.{u} ℓ) aW i hD j
    hj x

end AlgebraicGeometry.Etale
