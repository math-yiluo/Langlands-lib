/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.AffinePerfectPlusShift
import WeilConjectures.AlgebraicGeometry.AffineSupportIteratedCones
import WeilConjectures.AlgebraicGeometry.AffineSupportPoweredGenerators
import WeilConjectures.AlgebraicGeometry.AffineBinomialProjectorCone
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Affine perfect support extension

Source: Stacks Project, Derived Categories of Schemes, Tag 08EK (Lemma 36.13.10)
(blueprint: lem-sc-affine-perfect-support-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exists_scalar_cone_chain (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (s : ℕ)
    (g : Fin s → RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E : schemeDerivedCategory X) :
    ∃ C : Fin (s + 1) → schemeDerivedCategory X, C 0 = E ∧
      ∃ (b : ∀ i : Fin s, C i.castSucc ⟶ C i.succ)
        (d : ∀ i : Fin s, C i.succ ⟶ (C i.castSucc)⟦(1 : ℤ)⟧),
        ∀ i : Fin s,
          CategoryTheory.Pretriangulated.Triangle.mk
            (schemeDerivedScalar X (g i) (𝟙 (C i.castSucc))) (b i) (d i) ∈
              CategoryTheory.Pretriangulated.distinguishedTriangles
                (C := schemeDerivedCategory X) := by
  classical
  let gN : ℕ → RingCat.sectionsSubring
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    fun n ↦ if hn : n < s then g ⟨n, hn⟩ else 0
  have h (n : ℕ) (K : schemeDerivedCategory X) :=
    CategoryTheory.Pretriangulated.distinguished_cocone_triangle
      (schemeDerivedScalar X (gN n) (𝟙 K))
  choose Z b d hZ using h
  let Cn : ℕ → schemeDerivedCategory X :=
    Nat.rec E (fun n K ↦ Z n K)
  refine ⟨fun i ↦ Cn i.val, rfl,
    (fun i ↦ b i.val (Cn i.val)), (fun i ↦ d i.val (Cn i.val)), ?_⟩
  intro i
  simpa [gN, i.isLt, Fin.castSucc] using hZ i.val (Cn i.val)

set_option backward.isDefEq.respectTransparency false in
/-- A perfect complex on a quasi-compact open of an affine scheme, supported on the
intersection with a closed set with quasi-compact complement, extends after adjoining
its shift to a perfect complex supported on that closed set.
Support is expressed by vanishing of every cohomology stalk off the closed subset.
Restriction uses the canonical equivalence from the localized site to the open subscheme.
Source: Stacks Project, Tag 08EK (blueprint: lem-sc-affine-perfect-support-extension).
Proof: write T as the vanishing set of finitely many functions. By
lem-sc-affine-perfect-plus-shift extend F plus F[1] to X; by
lem-sc-perfect-into-support-on-T replace the functions by powers annihilating F.
Take successive multiplication cones. By lem-sc-affine-support-iterated-cones the
result is perfect, supported on T, and restricts to a sum of shifts of F.
Apply lem-sc-affine-perfect-map-lift to the endomorphism that is zero on the unshifted
F summand and identity on the others. Its lifted source remains supported on T.
The cone of the lifted map is perfect and supported on T by two-of-three, and its
restriction cancels all the unwanted summands, leaving F plus F[1]. -/
theorem exists_perfect_supported_extension (X : Scheme.{u}) [IsAffine X]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (hFT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf x))) :
    ∃ E : schemeDerivedCategory X, IsPerfect X E ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ≅
          F ⊞ F⟦(1 : ℤ)⟧) := by
  classical
  let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  obtain ⟨E₀, hE₀, e₀⟩ :=
    exists_perfect_restrict_iso_directSum_shift X U hU F hF
  obtain ⟨s, g, g', hcover, hg', hzero⟩ :=
    exists_affine_support_powered_generators X T hT hTc U hU F hF hFT
  obtain ⟨C, hC₀, b, d, hcone⟩ := exists_scalar_cone_chain X s g E₀
  have hCperfect : IsPerfect X (C 0) := hC₀ ▸ hE₀
  have eC₀ : Nonempty (R.obj (C 0) ≅ F ⊞ F⟦(1 : ℤ)⟧) := hC₀ ▸ e₀
  obtain ⟨hA, hAsupport, eA⟩ :=
    affine_support_iterated_cones X s g C hCperfect U b d hcone
  let A := C (Fin.last s)
  have hAT : ∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj A).val.presheaf x)) :=
    fun n x hx ↦ hAsupport n x ((hcover x).mp hx)
  obtain ⟨α, hα⟩ :=
    exists_binomial_projector_cone_restrict X U s F A
      (eA hU F hF eC₀ g' hg' hzero)
  let Aq : schemeDerivedQCohCategory X :=
    ⟨A, schemeDerivedQCohProperty_of_isPerfect X A hA⟩
  obtain ⟨A', I, β, γ, hA', _, _, ⟨bU, _, hγ⟩, hA'support⟩ :=
    exists_perfect_map_lift_of_isAffine X U hU Aq A hA α
  have hA'T := hA'support T hT hAT
  let P := supportedProperty X T
  let : P.IsTriangulated := supported_qcoh_isTriangulated X T
  obtain ⟨E, hE, bE, dE, htri⟩ :=
    P.distinguished_cocone_triangle γ
      ⟨schemeDerivedQCohProperty_of_isPerfect X A' hA', hA'T⟩
      ⟨schemeDerivedQCohProperty_of_isPerfect X A hA, hAT⟩
  have hEperfect := (isPerfect_two_out_of_three X
    (CategoryTheory.Pretriangulated.Triangle.mk γ bE dE) htri).1 hA' hA
  exact ⟨E, hEperfect, hE.2, hα A' γ bU hγ E bE dE htri⟩

end AlgebraicGeometry.Scheme
