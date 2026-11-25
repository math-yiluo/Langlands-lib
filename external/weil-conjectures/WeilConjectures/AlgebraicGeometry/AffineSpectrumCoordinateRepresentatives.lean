/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumRepresentativeMap
import WeilConjectures.Algebra.Homology.KFlatPullback

/-! # Termwise representatives in affine spectrum coordinates

Source: Stacks Project, Tags 0DJ8 and 0D5S.
(blueprint: lem-pc-affine-spectrum-coordinate-representatives).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- Spectrum transport can be represented by the actual termwise tensor pullbacks.
This only constructs representatives; it asserts no stalk condition or comparison
invertibility and does not require a base-change square.

Proof: put j = X.isoSpec.inv and j' = X'.isoSpec.inv. Tensor pullback along
these isomorphisms is an exact equivalence: the inverse equivalence is pullback
along the corresponding hom, and the composition and identity isomorphisms
come from the pullback/pushforward adjunctions. In particular it preserves
quasi-isomorphisms, computes derived pullback on every complex, and preserves
K-flatness. Set P0 = j* c.P and N0 = j'* c.N termwise. The universal derived
counits on these exact functors, composed with derived pullback of c.e and c.e',
give isomorphisms Q(P0) to affineSpectrumDerivedObject X K and Q(N0) to
its primed analogue. Naturality of isoSpec identifies
Spec.map g'.appTop followed by j with j' followed by g'. The underived
composition comparison therefore gives a chain isomorphism between
(Spec.map g'.appTop)* P0 and j'* (g'* c.P). Follow it by j'* c.t to define t0.
K-flatness of P0 makes its counit for the spectrum map invertible. The defining
leftDerivedLift equation for both composition comparisons, together with
naturality of the counits and c.represents, shows that t0 represents precisely
(affineSpectrumDerivedPullbackIso g').hom.app K followed by j'^* of phi.
Thus these data are Coordinates for affineSpectrumDerivedMorphism, with the two
stated equalities of complexes. The construction also works for zero complexes
and empty schemes, and needs no boundedness or quasi-coherence.
Source: Stacks Project, Tag 0DJ8, affine reduction, and Tag 0D5S,
composition of derived pullback using termwise K-flat representatives.
(blueprint: lem-pc-affine-spectrum-coordinate-representatives). -/
private theorem exists_affineSpectrum_coordinate_representatives_aux
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ) :
    ∃ d : Coordinates (Spec.map g'.appTop)
        (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
        (affineSpectrumDerivedMorphism g' K K' φ),
      d.P = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P ∧
      d.N = ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N := by
  classical
  let P₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj c.P
  let N₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(X', ⊤)).toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj c.N
  have hP₀ : CochainComplex.IsKFlatTensor (R := (Spec Γ(X, ⊤)).sheaf) P₀ := by
    have h := CochainComplex.isKFlat_pullback X.isoSpec.inv.base
      (Spec Γ(X, ⊤)).sheaf X.sheaf ⟨X.isoSpec.inv.c⟩ c.P c.isKFlat
    convert h using 1
    with_unfolding_all rfl
  have hcP := isIso_counit_of_isIso X.isoSpec.inv c.P
  have hcN := isIso_counit_of_isIso X'.isoSpec.inv c.N
  let e : DerivedCategory.Q.obj P₀ ≅ affineSpectrumDerivedObject X K :=
    ((DerivedCategory.quotientCompQhIso _).app P₀).symm ≪≫
      (asIso ((counit X.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))).symm ≪≫
      (derivedPullback X.isoSpec.inv).mapIso
        ((DerivedCategory.quotientCompQhIso _).app c.P) ≪≫
      (derivedPullback X.isoSpec.inv).mapIso c.e
  let e' : DerivedCategory.Q.obj N₀ ≅ affineSpectrumDerivedObject X' K' :=
    ((DerivedCategory.quotientCompQhIso _).app N₀).symm ≪≫
      (asIso ((counit X'.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N))).symm ≪≫
      (derivedPullback X'.isoSpec.inv).mapIso
        ((DerivedCategory.quotientCompQhIso _).app c.N) ≪≫
      (derivedPullback X'.isoSpec.inv).mapIso c.e'
  let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
    (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
  let t : ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) ⟶
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N :=
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app c.P ≫
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex (.up ℤ)).map c.t
  have ht := affineSpectrum_representative_map_eq g' K K' φ c e e'
    (by simp [e]; rfl) (by simp [e']; rfl)
  let d : Coordinates (Spec.map g'.appTop)
      (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
      (affineSpectrumDerivedMorphism g' K K' φ) :=
    { P := P₀
      N := N₀
      e := e
      e' := e'
      isKFlat := hP₀
      counit_isIso := counit_isIso_kFlat (Spec.map g'.appTop) P₀ hP₀
      t := t
      represents := ht }
  exact ⟨d, rfl, rfl⟩


/-- Spectrum transport can be represented by the actual termwise tensor pullbacks.
This only constructs representatives; it asserts no stalk condition or comparison
invertibility and does not require a base-change square.

Proof: put j = X.isoSpec.inv and j' = X'.isoSpec.inv. Tensor pullback along
these isomorphisms is an exact equivalence: the inverse equivalence is pullback
along the corresponding hom, and the composition and identity isomorphisms
come from the pullback/pushforward adjunctions. In particular it preserves
quasi-isomorphisms, computes derived pullback on every complex, and preserves
K-flatness. Set P0 = j* c.P and N0 = j'* c.N termwise. The universal derived
counits on these exact functors, composed with derived pullback of c.e and c.e',
give isomorphisms Q(P0) to affineSpectrumDerivedObject X K and Q(N0) to
its primed analogue. Naturality of isoSpec identifies
Spec.map g'.appTop followed by j with j' followed by g'. The underived
composition comparison therefore gives a chain isomorphism between
(Spec.map g'.appTop)* P0 and j'* (g'* c.P). Follow it by j'* c.t to define t0.
K-flatness of P0 makes its counit for the spectrum map invertible. The defining
leftDerivedLift equation for both composition comparisons, together with
naturality of the counits and c.represents, shows that t0 represents precisely
(affineSpectrumDerivedPullbackIso g').hom.app K followed by j'^* of phi.
Thus these data are Coordinates for affineSpectrumDerivedMorphism, with the two
stated equalities of complexes. The construction also works for zero complexes
and empty schemes, and needs no boundedness or quasi-coherence.
Source: Stacks Project, Tag 0DJ8, affine reduction, and Tag 0D5S,
composition of derived pullback using termwise K-flat representatives.
(blueprint: lem-pc-affine-spectrum-coordinate-representatives). -/
theorem exists_affineSpectrum_coordinate_representatives
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ) :
    ∃ d : Coordinates (Spec.map g'.appTop)
        (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
        (affineSpectrumDerivedMorphism g' K K' φ),
      d.P = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P ∧
      d.N = ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N := by
  classical
  let P₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj c.P
  let N₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(X', ⊤)).toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj c.N
  have hP₀ : CochainComplex.IsKFlatTensor (R := (Spec Γ(X, ⊤)).sheaf) P₀ := by
    have h := CochainComplex.isKFlat_pullback X.isoSpec.inv.base
      (Spec Γ(X, ⊤)).sheaf X.sheaf ⟨X.isoSpec.inv.c⟩ c.P c.isKFlat
    convert h using 1
    with_unfolding_all rfl
  have hcP := isIso_counit_of_isIso X.isoSpec.inv c.P
  have hcN := isIso_counit_of_isIso X'.isoSpec.inv c.N
  let e : DerivedCategory.Q.obj P₀ ≅ affineSpectrumDerivedObject X K :=
    ((DerivedCategory.quotientCompQhIso _).app P₀).symm ≪≫
      (asIso ((counit X.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))).symm ≪≫
      (derivedPullback X.isoSpec.inv).mapIso
        ((DerivedCategory.quotientCompQhIso _).app c.P) ≪≫
      (derivedPullback X.isoSpec.inv).mapIso c.e
  let e' : DerivedCategory.Q.obj N₀ ≅ affineSpectrumDerivedObject X' K' :=
    ((DerivedCategory.quotientCompQhIso _).app N₀).symm ≪≫
      (asIso ((counit X'.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N))).symm ≪≫
      (derivedPullback X'.isoSpec.inv).mapIso
        ((DerivedCategory.quotientCompQhIso _).app c.N) ≪≫
      (derivedPullback X'.isoSpec.inv).mapIso c.e'
  let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
    (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
  let t : ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) ⟶
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N :=
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app c.P ≫
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex (.up ℤ)).map c.t
  have ht := affineSpectrum_representative_map_eq g' K K' φ c e e'
    (by simp [e]; rfl) (by simp [e']; rfl)
  let d : Coordinates (Spec.map g'.appTop)
      (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
      (affineSpectrumDerivedMorphism g' K K' φ) :=
    { P := P₀
      N := N₀
      e := e
      e' := e'
      isKFlat := hP₀
      counit_isIso := counit_isIso_kFlat (Spec.map g'.appTop) P₀ hP₀
      t := t
      represents := ht }
  exact ⟨d, rfl, rfl⟩

end AlgebraicGeometry.SingleComplexBaseChange
