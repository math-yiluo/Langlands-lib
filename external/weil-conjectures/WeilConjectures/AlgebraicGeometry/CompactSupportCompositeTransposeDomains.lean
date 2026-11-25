/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.Tactic.IrreducibleDef

/-!
# Domains for the compact-support composite transpose

Source: latest blueprint file:
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`.
(blueprint node: `lem-pur-compact-support-composite-transpose-domains`).

The statement is made on the concrete finite-coefficient small pro-etale derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor MonoidalCategory
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] DerivedCategory.braidedCategory'

namespace AlgebraicGeometry.ProEtale

/-- The ordinary derived category on the small pro-etale site.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev CompactSupportD (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The derived pullback on compact-support coefficients.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev compactSupportPullback (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (a : V ⟶ T) : CompactSupportD A T ⥤ CompactSupportD A V :=
  L((a)^*[ModuleCat.{u + 1} A])

/-- The compact-support derived lower shriek.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev compactSupportLowerShriek (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (a : V ⟶ T) [HasCompactification a] :
    CompactSupportD A V ⥤ CompactSupportD A T :=
  rightDerivedLowerShriek (ModuleCat.{u + 1} A) a

/-- The compact-support derived upper shriek.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev compactSupportUpperShriek (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (a : V ⟶ T) [HasCompactification a] :
    CompactSupportD A T ⥤ CompactSupportD A V :=
  rightDerivedUpperShriek A a

/-- The constructible finite-Tor full subcategory.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev CompactSupportDctf (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}} :=
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T

/-- Tensor product in the ordinary derived category.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev compactSupportTensor (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    (P Q : CompactSupportD A T) : CompactSupportD A T := P ⊗ Q

/-- A derived-category morphism used in the two transposes.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev compactSupportHom (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    (P Q : CompactSupportD A T) := P ⟶ Q

/-- The upper-shriek image of the coefficient unit.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable abbrev W (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (a : V ⟶ T) [HasCompactification a] : CompactSupportD A V :=
  (compactSupportUpperShriek A a).obj (𝟙_ _)

/-- The inverse of the published projection map, conjugated by the canonical tensor symmetry.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable def canonicalProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (a : V ⟶ T) [HasCompactification a]
    (B : CompactSupportD A T) (M : CompactSupportD A V)
    (hB : CompactSupportDctf A B) (hM : CompactSupportDctf A M) :
    (compactSupportLowerShriek A a).obj
        ((compactSupportPullback A a).obj B ⊗ M) ≅
      B ⊗ (compactSupportLowerShriek A a).obj M := by
  let hPF := hasProjectionFormula_of_constructibleFiniteTor A a hM hB
  letI : IsIso (((projectionMap (ModuleCat.{u + 1} A) a).app M).app B) := hPF
  exact
    (asIso ((compactSupportLowerShriek A a).map (β_ _ _).hom)).symm ≪≫
      (asIso (((projectionMap (ModuleCat.{u + 1} A) a).app M).app B)).symm ≪≫
      (β_ _ _)

/-- The adjoint transpose of the inverse projection and the coefficient counit.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable def canonicalTheta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (a : V ⟶ T) [HasCompactification a]
    (B : CompactSupportD A T)
    (hB : CompactSupportDctf A B) (hM : CompactSupportDctf A (W A a))
    (hT : CompactSpace T)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V
      ((compactSupportPullback A a).obj B ⊗ (W A a)))
    (hBplus : DerivedCategory.TStructure.t.plus B)
    (hUnitplus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A T))) :
    (compactSupportPullback A a).obj B ⊗ (W A a) ⟶
      (compactSupportUpperShriek A a).obj B := by
  letI := hT
  exact
    (rightDerivedUpperShriekHomEquiv a hK hBplus)
      ((canonicalProjectionIso A a B (W A a) hB hM).hom ≫
        ((𝟙 B) ⊗ₘ rightDerivedUpperShriekCounit a (𝟙_ _) hUnitplus) ≫
        (ρ_ B).hom)

/-- The one-step tensor domain `U` for the composite transpose.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable abbrev U (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (K : CompactSupportD A Z) : CompactSupportD A Y :=
  (compactSupportPullback A g).obj K ⊗ W A g

/-- The two-step tensor domain `N` for the composite transpose.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable abbrev N (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] (K : CompactSupportD A Z) :
    CompactSupportD A X :=
  (compactSupportPullback A f).obj (U A g K) ⊗ W A f

/-- The full subcategory used to restrict the compact-support functors.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev CompactSupportCtfCategory (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}} :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).FullSubcategory

/-- Restriction of lower shriek to constructible finite-Tor objects.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev lowerLift (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K)) :
    CompactSupportCtfCategory A (T := X) ⥤ CompactSupportCtfCategory A (T := Y) :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y).lift
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι ⋙
      compactSupportLowerShriek A f)
    (fun K ↦ hf₁ K.obj K.property)

/-- Restriction of upper shriek to constructible finite-Tor objects.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
abbrev upperLift (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L)) :
    CompactSupportCtfCategory A (T := Y) ⥤ CompactSupportCtfCategory A (T := X) :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).lift
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y).ι ⋙
      compactSupportUpperShriek A f)
    (fun L ↦ hf₂ L.obj L.property)

/-- The bounded constructible finite-Tor adjunction.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`. -/
noncomputable def restrictedAdjF
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (hY : CompactSpace Y)
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K))
    (hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L)) :
    lowerLift A f hf₁ ⊣ upperLift A f hf₂ := by
  letI := hY
  exact rightDerivedUpperShriekAdjunction f _ _
    (fun _ hK ↦ hK.plusEtaleOrigin) (fun _ hL ↦ hL.plus) hf₁ hf₂

/-- The concrete pro-etale compact-support compositor transported from the etale compositor.

This is the explicit transport through `comparisonUpperStarPlusEtaleOrigin` and
`rightDerivedLowerShriekComparisonIso`; no choice of an arbitrary inhabiting isomorphism is made.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable irreducible_def canonicalEtaleOriginLowerShriekCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hfq : QuasiCompact f) (hgq : QuasiCompact g) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) g := by
  letI := hfq
  letI := hgq
  exact (originCompositionAmbient A f g).symm

/-- The finite-Tor compositor restricted to the constructible finite-Tor subcategories.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable irreducible_def canonicalAlpha
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (_hY : CompactSpace Y) (_hZ : CompactSpace Z)
    (hfq : QuasiCompact f) (hgq : QuasiCompact g)
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K))
    (_hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L))
    (hg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A g).obj K))
    (_hg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A g).obj L))
    (hfg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A (f ≫ g)).obj K))
    (_hfg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A (f ≫ g)).obj L)) :
    lowerLift A (f ≫ g) hfg₁ ≅ lowerLift A f hf₁ ⋙ lowerLift A g hg₁ := by
  letI := hfq
  letI := hgq
  let hPX : CompactSupportDctf A (T := X) ≤
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X :=
    fun _ hK ↦ hK.plusEtaleOrigin
  let e := canonicalEtaleOriginLowerShriekCompIso A f g hfq hgq
  let PZ := CompactSupportDctf A (T := Z)
  exact (PZ.fullyFaithfulι.whiskeringRight _).preimageIso
      (X := lowerLift A (f ≫ g) hfg₁)
      (Y := lowerLift A f hf₁ ⋙ lowerLift A g hg₁)
      (Functor.isoWhiskerLeft (ObjectProperty.ιOfLE hPX) e)

/-- The adjunction conjugate `c : G_h ≅ G_f G_g` of `canonicalAlpha` across the restricted
Brown adjunctions (statement dependency def-weil-pbc-adjunction-conjugate).
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable irreducible_def canonicalC
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hfq : QuasiCompact f) (hgq : QuasiCompact g)
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K))
    (hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L))
    (hg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A g).obj K))
    (hg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A g).obj L))
    (hfg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A (f ≫ g)).obj K))
    (hfg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A (f ≫ g)).obj L)) :
    upperLift A (f ≫ g) hfg₂ ≅ upperLift A g hg₂ ⋙ upperLift A f hf₂ := by
  letI := hfq
  letI := hgq
  exact (conjugateIsoEquiv
    ((restrictedAdjF A f hY hf₁ hf₂).comp (restrictedAdjF A g hZ hg₁ hg₂))
    (restrictedAdjF A (f ≫ g) hZ hfg₁ hfg₂)
    (canonicalAlpha A f g hY hZ hfq hgq hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂)).symm

/-- The component `c_{A_Z} : W_h ≅ G_f G_g A_Z` of the conjugate `c` at the coefficient unit.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable irreducible_def canonicalCUnit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hfq : QuasiCompact f) (hgq : QuasiCompact g)
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K))
    (hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L))
    (hg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A g).obj K))
    (hg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A g).obj L))
    (hfg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A (f ≫ g)).obj K))
    (hfg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A (f ≫ g)).obj L))
    (hunit : CompactSupportDctf A (𝟙_ (CompactSupportD A Z))) :
    W A (f ≫ g) ≅
      (compactSupportUpperShriek A f).obj ((compactSupportUpperShriek A g).obj (𝟙_ _)) := by
  letI := hfq
  letI := hgq
  let e := canonicalC A f g hY hZ hfq hgq hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂
  let i := e.app ⟨𝟙_ _, hunit⟩
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι.mapIso i

/-- The component at a constructible finite-Tor object of the compositor `canonicalAlpha`, as an
ambient derived morphism `P_h B ⟶ P_g P_f B`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable irreducible_def canonicalAlphaComponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hfq : QuasiCompact f) (hgq : QuasiCompact g)
    (hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A f).obj K))
    (hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A f).obj L))
    (hg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A g).obj K))
    (hg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A g).obj L))
    (hfg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
      ((compactSupportLowerShriek A (f ≫ g)).obj K))
    (hfg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
      ((compactSupportUpperShriek A (f ≫ g)).obj L))
    (B : CompactSupportD A X) (hB : CompactSupportDctf A B) :
    (compactSupportLowerShriek A (f ≫ g)).obj B ⟶
      (compactSupportLowerShriek A g).obj ((compactSupportLowerShriek A f).obj B) :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z).ι.map
    ((canonicalAlpha A f g hY hZ hfq hgq hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂).hom.app ⟨B, hB⟩)

/-- The identification of `N` with `S_h K ⊗ W_h` by monoidal pullback, reassociation, `q`, and the
inverse pullback compositor, used in `R_K`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
noncomputable def canonicalSourceIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : CompactSupportD A Z)
    (q : (compactSupportPullback A f).obj (W A g) ⊗ W A f ≅ W A (f ≫ g)) :
    N A f g K ≅
      (compactSupportPullback A (f ≫ g)).obj K ⊗ W A (f ≫ g) := by
  let r := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K
  exact
    (asIso ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
      ((compactSupportPullback A g).obj K) (W A g)).hom ▷ W A f)) ≪≫
      (asIso ((α_ _ _ _).hom)) ≪≫
      (asIso (𝟙 _ ⊗ₘ q.hom)) ≪≫
      (asIso (r.inv ⊗ₘ 𝟙 _))

/-- Concrete normalized data for the final compact-support transposition.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-cohomological-smoothness.md`,
proof, final composition paragraph
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
structure CompactSupportCompositeTransposeDomains
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d e : ℕ) (hf : SmoothOfRelativeDimension d f)
    (hg : SmoothOfRelativeDimension e g) where
  Wf_ctf : CompactSupportDctf A (W A f)
  Wg_ctf : CompactSupportDctf A (W A g)
  Wh_ctf : CompactSupportDctf A (W A (f ≫ g))
  unitZ_ctf : CompactSupportDctf A (𝟙_ (CompactSupportD A Z))
  U_ctf : ∀ K, CompactSupportDctf A K → CompactSupportDctf A (U A g K)
  N_ctf : ∀ K, CompactSupportDctf A K → CompactSupportDctf A (N A f g K)
  GgK_ctf : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
    ((compactSupportUpperShriek A g).obj K)
  GfGgK_ctf : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
    ((compactSupportUpperShriek A f).obj ((compactSupportUpperShriek A g).obj K))
  hf₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
    ((compactSupportLowerShriek A f).obj K)
  hf₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
    ((compactSupportUpperShriek A f).obj L)
  hg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
    ((compactSupportLowerShriek A g).obj K)
  hg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
    ((compactSupportUpperShriek A g).obj L)
  hfg₁ : ∀ K, CompactSupportDctf A K → CompactSupportDctf A
    ((compactSupportLowerShriek A (f ≫ g)).obj K)
  hfg₂ : ∀ L, CompactSupportDctf A L → CompactSupportDctf A
    ((compactSupportUpperShriek A (f ≫ g)).obj L)
  f_qc : QuasiCompact f
  g_qc : QuasiCompact g
  counit_comparison : ∀ (hY : CompactSpace Y) (hZ : CompactSpace Z),
    letI := hY
    letI := hZ
    ∀ K : CompactSupportCtfCategory A (T := Z),
      (canonicalAlpha A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂).hom.app
          ((upperLift A (f ≫ g) hfg₂).obj K) ≫
        (lowerLift A f hf₁ ⋙ lowerLift A g hg₁).map
          ((canonicalC A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂).hom.app K) ≫
        ((restrictedAdjF A f hY hf₁ hf₂).comp
          (restrictedAdjF A g hZ hg₁ hg₂)).counit.app K =
      (restrictedAdjF A (f ≫ g) hZ hfg₁ hfg₂).counit.app K
  q : (compactSupportPullback A f).obj (W A g) ⊗ W A f ≅ W A (f ≫ g)
  q_eq : ∀ (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (compactSupportTensor A ((compactSupportPullback A f).obj (W A g)) (W A f)))
    (hUnitplus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A Y))),
    q.hom = canonicalTheta A f (W A g) Wg_ctf Wf_ctf hY hK
      (Wg_ctf.plus) hUnitplus ≫
      (canonicalCUnit A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂
        (by exact unitZ_ctf)).inv
  unitY_plus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A Y))
  unitZ_plus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A Z))
  L : ∀ K, CompactSupportDctf A K → compactSupportHom A (N A f g K)
      ((compactSupportUpperShriek A f).obj ((compactSupportUpperShriek A g).obj K))
  L_eq : ∀ K hK (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hOriginG : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y
      (compactSupportTensor A ((compactSupportPullback A g).obj K) (W A g)))
    (hOriginF : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (compactSupportTensor A
        ((compactSupportPullback A f).obj ((compactSupportUpperShriek A g).obj K))
        (W A f))),
    L K hK =
      ((compactSupportPullback A f).map
        (canonicalTheta A g K hK Wg_ctf hZ hOriginG (hK.plus) unitZ_plus) ⊗ₘ 𝟙 _ ) ≫
      canonicalTheta A f ((compactSupportUpperShriek A g).obj K)
        (GgK_ctf K hK) Wf_ctf hY hOriginF
        ((GgK_ctf K hK).plus) unitY_plus
  R : ∀ K, CompactSupportDctf A K → compactSupportHom A (N A f g K)
      ((compactSupportUpperShriek A f).obj ((compactSupportUpperShriek A g).obj K))
  R_eq : ∀ K hK (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hOriginH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (compactSupportTensor A ((compactSupportPullback A (f ≫ g)).obj K)
        (W A (f ≫ g))))
    (hKplus : DerivedCategory.TStructure.t.plus K),
    R K hK =
      ((canonicalSourceIso A f g K q).hom ≫
        canonicalTheta A (f ≫ g) K hK Wh_ctf hZ hOriginH hKplus unitZ_plus) ≫
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι.map
        ((canonicalC A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂).hom.app ⟨K, hK⟩)
  projection_f : ∀ (B : CompactSupportD A Y) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A X) (_hM : CompactSupportDctf A M), IsIso
    (((projectionMap (ModuleCat.{u + 1} A) f).app M).app B)
  projection_g : ∀ (B : CompactSupportD A Z) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A Y) (_hM : CompactSupportDctf A M), IsIso
    (((projectionMap (ModuleCat.{u + 1} A) g).app M).app B)
  projection_h : ∀ (B : CompactSupportD A Z) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A X) (_hM : CompactSupportDctf A M), IsIso
    (((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app M).app B)
  pi_f : ∀ (B : CompactSupportD A Y) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A X) (_hM : CompactSupportDctf A M),
    (compactSupportLowerShriek A f).obj
        ((compactSupportPullback A f).obj B ⊗ M) ≅
      B ⊗ (compactSupportLowerShriek A f).obj M
  pi_g : ∀ (B : CompactSupportD A Z) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A Y) (_hM : CompactSupportDctf A M),
    (compactSupportLowerShriek A g).obj
        ((compactSupportPullback A g).obj B ⊗ M) ≅
      B ⊗ (compactSupportLowerShriek A g).obj M
  pi_h : ∀ (B : CompactSupportD A Z) (_hB : CompactSupportDctf A B)
    (M : CompactSupportD A X) (_hM : CompactSupportDctf A M),
    (compactSupportLowerShriek A (f ≫ g)).obj
        ((compactSupportPullback A (f ≫ g)).obj B ⊗ M) ≅
      B ⊗ (compactSupportLowerShriek A (f ≫ g)).obj M
  pi_f_eq : ∀ B hB M hM, pi_f B hB M hM = canonicalProjectionIso A f B M hB hM
  pi_g_eq : ∀ B hB M hM, pi_g B hB M hM = canonicalProjectionIso A g B M hB hM
  pi_h_eq : ∀ B hB M hM, pi_h B hB M hM = canonicalProjectionIso A (f ≫ g) B M hB hM
  projection_f_natural : ∀ (B B' : CompactSupportD A Y) (hB : CompactSupportDctf A B)
    (hB' : CompactSupportDctf A B') (M M' : CompactSupportD A X)
    (hM : CompactSupportDctf A M) (hM' : CompactSupportDctf A M')
    (u : B ⟶ B') (v : M ⟶ M'),
    (canonicalProjectionIso A f B M hB hM).hom ≫
        (u ⊗ₘ (compactSupportLowerShriek A f).map v) =
      (compactSupportLowerShriek A f).map
        ((compactSupportPullback A f).map u ⊗ₘ v) ≫
        (canonicalProjectionIso A f B' M' hB' hM').hom
  projection_g_natural : ∀ (B B' : CompactSupportD A Z) (hB : CompactSupportDctf A B)
    (hB' : CompactSupportDctf A B') (M M' : CompactSupportD A Y)
    (hM : CompactSupportDctf A M) (hM' : CompactSupportDctf A M')
    (u : B ⟶ B') (v : M ⟶ M'),
    (canonicalProjectionIso A g B M hB hM).hom ≫
        (u ⊗ₘ (compactSupportLowerShriek A g).map v) =
      (compactSupportLowerShriek A g).map
        ((compactSupportPullback A g).map u ⊗ₘ v) ≫
        (canonicalProjectionIso A g B' M' hB' hM').hom
  projection_h_natural : ∀ (B B' : CompactSupportD A Z) (hB : CompactSupportDctf A B)
    (hB' : CompactSupportDctf A B') (M M' : CompactSupportD A X)
    (hM : CompactSupportDctf A M) (hM' : CompactSupportDctf A M')
    (u : B ⟶ B') (v : M ⟶ M'),
    (canonicalProjectionIso A (f ≫ g) B M hB hM).hom ≫
        (u ⊗ₘ (compactSupportLowerShriek A (f ≫ g)).map v) =
      (compactSupportLowerShriek A (f ≫ g)).map
        ((compactSupportPullback A (f ≫ g)).map u ⊗ₘ v) ≫
        (canonicalProjectionIso A (f ≫ g) B' M' hB' hM').hom
  projection_f_unit : ∀ (M : CompactSupportD A X) (hM : CompactSupportDctf A M)
    (hUnit : CompactSupportDctf A (𝟙_ (CompactSupportD A Y))),
    (pi_f (𝟙_ _) hUnit M hM).hom ≫ (λ_ _).hom =
      (compactSupportLowerShriek A f).map
        ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom ⊗ₘ 𝟙 _) ≫
        (compactSupportLowerShriek A f).map (λ_ _).hom
  projection_g_unit : ∀ (M : CompactSupportD A Y) (hM : CompactSupportDctf A M)
    (hUnit : CompactSupportDctf A (𝟙_ (CompactSupportD A Z))),
    (pi_g (𝟙_ _) hUnit M hM).hom ≫ (λ_ _).hom =
      (compactSupportLowerShriek A g).map
        ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom ⊗ₘ 𝟙 _) ≫
        (compactSupportLowerShriek A g).map (λ_ _).hom
  projection_h_unit : ∀ (M : CompactSupportD A X) (hM : CompactSupportDctf A M)
    (hUnit : CompactSupportDctf A (𝟙_ (CompactSupportD A Z))),
    (pi_h (𝟙_ _) hUnit M hM).hom ≫ (λ_ _).hom =
      (compactSupportLowerShriek A (f ≫ g)).map
        ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) (f ≫ g)).hom ⊗ₘ 𝟙 _) ≫
        (compactSupportLowerShriek A (f ≫ g)).map (λ_ _).hom
  projection_f_associative : ∀ (B B' : CompactSupportD A Y)
    (hB : CompactSupportDctf A B) (hB' : CompactSupportDctf A B')
    (hBB' : CompactSupportDctf A (B ⊗ B')) (M : CompactSupportD A X)
    (hM : CompactSupportDctf A M)
    (hM' : CompactSupportDctf A ((compactSupportPullback A f).obj B' ⊗ M)),
    (pi_f (B ⊗ B') hBB' M hM).hom ≫ (α_ B B' _).hom =
      (compactSupportLowerShriek A f).map
          ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f B B').hom ▷ M ≫
            (α_ _ _ _).hom) ≫
        (pi_f B hB ((compactSupportPullback A f).obj B' ⊗ M)
          hM').hom ≫ B ◁ (pi_f B' hB' M hM).hom
  projection_g_associative : ∀ (B B' : CompactSupportD A Z)
    (hB : CompactSupportDctf A B) (hB' : CompactSupportDctf A B')
    (hBB' : CompactSupportDctf A (B ⊗ B')) (M : CompactSupportD A Y)
    (hM : CompactSupportDctf A M)
    (hM' : CompactSupportDctf A ((compactSupportPullback A g).obj B' ⊗ M)),
    (pi_g (B ⊗ B') hBB' M hM).hom ≫ (α_ B B' _).hom =
      (compactSupportLowerShriek A g).map
          ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g B B').hom ▷ M ≫
            (α_ _ _ _).hom) ≫
        (pi_g B hB ((compactSupportPullback A g).obj B' ⊗ M)
          hM').hom ≫ B ◁ (pi_g B' hB' M hM).hom
  projection_h_associative : ∀ (B B' : CompactSupportD A Z)
    (hB : CompactSupportDctf A B) (hB' : CompactSupportDctf A B')
    (hBB' : CompactSupportDctf A (B ⊗ B')) (M : CompactSupportD A X)
    (hM : CompactSupportDctf A M)
    (hM' : CompactSupportDctf A ((compactSupportPullback A (f ≫ g)).obj B' ⊗ M)),
    (pi_h (B ⊗ B') hBB' M hM).hom ≫ (α_ B B' _).hom =
      (compactSupportLowerShriek A (f ≫ g)).map
          ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (f ≫ g) B B').hom ▷ M ≫
            (α_ _ _ _).hom) ≫
        (pi_h B hB ((compactSupportPullback A (f ≫ g)).obj B' ⊗ M)
          hM').hom ≫ B ◁ (pi_h B' hB' M hM).hom
  projection_composition : ∀ (K : CompactSupportD A Z) (hK : CompactSupportDctf A K)
    (M : CompactSupportD A X) (hM : CompactSupportDctf A M)
    (hY : CompactSpace Y) (hZ : CompactSpace Z)
    (hSgK : CompactSupportDctf A ((compactSupportPullback A g).obj K))
    (hPfM : CompactSupportDctf A ((compactSupportLowerShriek A f).obj M))
    (hShM : CompactSupportDctf A
      ((compactSupportPullback A (f ≫ g)).obj K ⊗ M))
    (_hSfSgM : CompactSupportDctf A
      ((compactSupportPullback A f).obj ((compactSupportPullback A g).obj K) ⊗ M)),
    canonicalAlphaComponent A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂
        ((compactSupportPullback A (f ≫ g)).obj K ⊗ M) hShM ≫
      (compactSupportLowerShriek A f ⋙ compactSupportLowerShriek A g).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K ⊗ₘ 𝟙 _) ≫
      (compactSupportLowerShriek A g).map
          (pi_f ((compactSupportPullback A g).obj K) hSgK M hM).hom ≫
      (pi_g K hK ((compactSupportLowerShriek A f).obj M) hPfM).hom =
      (pi_h K hK M hM).hom ≫
        (𝟙 K ⊗ₘ canonicalAlphaComponent A f g hY hZ f_qc g_qc hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂ M hM)



/-- The concrete domain and normalization statement for smooth compact-support composition.
Proof steps:
(1) finite-Tor pullback and tensor stability put the coefficient objects, `U`, `N`, and all
reassociations used below in `Dctf`.
(2) Brown's restricted upper-shriek adjunctions and the constructible comparison provide the
bounded etale-origin witnesses and the compact-support images for each displayed input.
(3) The canonical lower-shriek compositor is transposed across those restricted adjunctions;
its mate `c` satisfies the pasted counit equation, and the coefficient map `q` is the mate of
`theta` at the unit.
(4) The inverse of the published finite-Tor projection map, with the tensor braiding, defines
`pi_f`, `pi_g`, and `pi_h`; their unit, inverse, naturality, and coefficient-associativity laws
are recorded for every input used by the two transposes.
(5) Pullback's monoidal compositor and the compositor `alpha` identify the composite projection
with the two successive projections, including the module input `P_f M`.
(6) The restricted adjunction Hom equivalences are bijections (hence injective); applying them
in the two orders gives the displayed `L` and `R` domains and the typed composite-projection
identity required before the final double-transpose calculation.
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
theorem compactSupportCompositeTransposeDomains
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] (_hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    {X Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e : ℕ)
    [IsSeparated f.left] [IsSeparated g.left]
    (hf : SmoothOfRelativeDimension d f.left)
    (hg : SmoothOfRelativeDimension e g.left)
    [HasCompactification f.left] [HasCompactification g.left]
    [HasCompactification (f.left ≫ g.left)]
    (theta_f_iso : ∀ (hWf : CompactSupportDctf A (W A f.left))
      (B : CompactSupportD A Y.left) (hB : CompactSupportDctf A B)
      (hY : CompactSpace Y.left)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X.left
        (compactSupportTensor A ((compactSupportPullback A f.left).obj B) (W A f.left)))
      (hBplus : DerivedCategory.TStructure.t.plus B)
      (hUnitplus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A Y.left))),
      IsIso (canonicalTheta A f.left B hB hWf hY hK hBplus hUnitplus))
    (theta_g_iso : ∀ (hWg : CompactSupportDctf A (W A g.left))
      (B : CompactSupportD A Z.left) (hB : CompactSupportDctf A B)
      (hZ : CompactSpace Z.left)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y.left
        (compactSupportTensor A ((compactSupportPullback A g.left).obj B) (W A g.left)))
      (hBplus : DerivedCategory.TStructure.t.plus B)
      (hUnitplus : DerivedCategory.TStructure.t.plus (𝟙_ (CompactSupportD A Z.left))),
      IsIso (canonicalTheta A g.left B hB hWg hZ hK hBplus hUnitplus)) :
    Nonempty (CompactSupportCompositeTransposeDomains A d e hf hg) := by
  sorry

end AlgebraicGeometry.ProEtale
