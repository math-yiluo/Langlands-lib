/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientFlatSequence
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeChain
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Division by a regular scalar on an injective module sheaf

Every module sheaf is a quotient of a flat one; on a flat module the regular quotient sequence
`0 → M → M → M ⊗ S → 0` is short exact, with the normalized coefficient unit as second map.
Lifting along the injective scalar on a flat cover shows that the scalar is an epimorphism on
every injective module sheaf.

Source: Stacks Tags 03D7, 06YS and 079P; the free lifted representable test for injectivity and the
elementary divisibility property of injectives for a regular scalar.
(blueprint: lem-sf-regular-scalar-injective-divisibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory

/-- Every module sheaf is a quotient of a flat module sheaf.
Source: Stacks Tag 06YS; degree zero of a K-flat resolution with flat terms and degreewise
epimorphic augmentation (blueprint: lem-sf-regular-scalar-injective-divisibility). -/
theorem exists_flat_epi (M : Modules R) :
    ∃ (X : Modules R) (p : X ⟶ M), Epi p ∧ exactFunctor _ _ (tensorRight X) := by
  obtain ⟨K, f, -, hflat, -, hepi⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)
  have := hepi 0
  exact ⟨K.X 0, f.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom,
    epi_comp _ _, hflat 0⟩

variable [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (φ : R ⟶ S) (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

/-- On a flat module the regular scalar is followed by a cokernel map to a restricted module,
through which every map to a restricted module factors.
Source: Stacks Tags 06YP and 06YY; the regular quotient sequence tensored with a flat module
and the normalized ordinary scalar-extension adjunction
(blueprint: lem-sf-regular-scalar-injective-divisibility). -/
theorem exists_scalar_shortExact_of_flat
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (X : Modules R) (hX : exactFunctor _ _ (tensorRight X)) :
    ∃ (Y : Modules S) (η : X ⟶ (restriction φ).obj Y)
      (hz : (scalar R t).app X ≫ η = 0),
      (ShortComplex.mk _ η hz).ShortExact ∧
        ∀ (N : Modules S) (g : X ⟶ (restriction φ).obj N),
          ∃ g' : Y ⟶ N, g = η ≫ (restriction φ).map g' := by
  obtain ⟨-, -, ho⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨o, ho⟩ := ho d.E d.obj_eq d.map_eq
  let η : X ⟶ (restriction φ).obj (changeOfRings φ X) :=
    o.unit.app X ≫ (restriction φ).map (eqToHom (d.obj_eq X))
  have hη (U : Cᵒᵖ) (x : X.val.obj U) : η.val.app U x =
      (toSheafify J (changeOfRingsPresheaf φ X).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    have h := ho X (changeOfRings φ X) (𝟙 _) U x
    simp only [Category.comp_id, Adjunction.homEquiv_unit] at h
    exact h
  have hz : (scalar R t).app X ≫ η = 0 := by
    have hn : η ≫ (scalar R t).app ((restriction φ).obj (changeOfRings φ X)) =
        (scalar R t).app X ≫ η := (scalar R t).naturality η
    rw [← hn, scalar_restriction_zero t φ ht, comp_zero]
  refine ⟨changeOfRings φ X, η, hz,
    coefficient_shortExact_of_flat φ t ht hexact X hX η hη hz, fun N g ↦ ?_⟩
  refine ⟨eqToHom (d.obj_eq X).symm ≫ (o.homEquiv X N).symm g, ?_⟩
  simp only [η, Category.assoc, ← Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- The regular scalar is an epimorphism on every injective module sheaf.
Source: Stacks Tags 03D7 and 079P; a flat cover lifts along the injective scalar on the cover
(blueprint: lem-sf-regular-scalar-injective-divisibility).

Proof: choose an epimorphism `p : X ⟶ M` from a flat module. The scalar on `X` is a
monomorphism, so injectivity of `M` extends `p` along it. Naturality of the scalar then
factors `p` through the scalar on `M`. -/
theorem epi_scalar_of_injective
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (M : Modules R) [Injective M] : Epi ((scalar R t).app M) := by
  obtain ⟨X, p, hp, hX⟩ := exists_flat_epi M
  obtain ⟨Y, η, hz, hs, -⟩ := exists_scalar_shortExact_of_flat φ t ht hexact d X hX
  have : Mono ((scalar R t).app X) := hs.mono_f
  let g := Injective.factorThru p ((scalar R t).app X)
  have hg : p = g ≫ (scalar R t).app M :=
    (Injective.comp_factorThru p ((scalar R t).app X)).symm.trans
      ((scalar R t).naturality g).symm
  rw [hg] at hp
  exact epi_of_epi g _

end SheafOfModules.RegularQuotientCone
