/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerArbitraryScalarMaps
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerScalarOfSource
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionModulus

/-! # Scalar and modulus reduction of ordinary supported boundaries

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-supported-scalar-modulus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem compose_scalar_modulus
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {X' Y' Z' : D}
    (η : X ⟶ F.obj X') (θ : Y ⟶ F.obj Y') (e : Y' ⟶ Z')
    (c : Ext X Y 2) (d : Ext X' Y' 2) (d' : Ext X' Z' 2)
    (hd : d.comp (Ext.mk₀ e) (add_zero 2) = d')
    (h : (Ext.mk₀ η).comp (d.mapExactFunctor F) (zero_add 2) =
      c.comp (Ext.mk₀ θ) (add_zero 2)) :
    (Ext.mk₀ η).comp (d'.mapExactFunctor F) (zero_add 2) =
      c.comp (Ext.mk₀ (θ ≫ F.map e)) (add_zero 2) := by
  rw [← hd, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, h,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

-- Elaborating the fixed scalar/support maps requires a larger finite budget.
/-- Changing coefficients and then the Kummer modulus preserves the normalized
supported boundary, with its sectionwise coefficient and root maps.
Source: blueprint finite reduction Step 4; Stacks 03PL and 07A6
(blueprint: lem-pur-supported-scalar-modulus).
Proof: first keep the larger modulus and use the normalized scalar units on the
supported constant and root sheaves. The scalar boundary theorem gives their
Yoneda square. For the smaller modulus, the morphism of Kummer sequences is the
specified root projection, multiplication by M/N, and the identity on Gm.
Naturality gives the same connecting class. The generator equation for e gives
the same further root map; uniqueness of the relative boundary identifies its
Ext class. Reassociate Yoneda products to compose this equality with the scalar
square. All operations apply to arbitrary finite rings, including zero rings,
and to empty support, without a flatness assumption on the quotient. -/
theorem supportedKummerScalarModulus
    {R A : Type (u + 1)} [CommRing R] [Finite R] [CommRing A] [Finite A]
    (φ : R →+* A) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hdiv : N ∣ M)
    (hR : (M : R) = 0) (hAM : (M : A) = 0) (hAN : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hTM : IsUnit (M : Γ(T, ⊤))) (hTN : IsUnit (N : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (e : Scheme.finiteEtaleTateLine T M A hAM ≅
      Scheme.finiteEtaleTateLine T N A hAN)
    (hq : q ≫ kernel.ι (N • 𝟙 T.gmSheaf) = (M / N) • kernel.ι (M • 𝟙 T.gmSheaf))
    (he : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf M).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A M T hAM W a z) =
        Scheme.finiteEtaleTateOneGenerator A N T hAN W a (q.hom.app W z))
    (κR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T M R hR) 2)
    (κA : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hAN) 2)
    (hκR : SupportedKummerBoundary R M hR i hI hTM κR)
    (hκA : SupportedKummerBoundary A N hAN i hI hTN κA) :
    ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant A D))
      (θ : Scheme.finiteEtaleTateLine T M R hR ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
          (Scheme.finiteEtaleTateLine T N A hAN)),
      (∀ (W : D.Etaleᵒᵖ) (r : R),
        η.hom.app W ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app W r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W (φ r)) ∧
      (∀ (W : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf M).obj.obj W),
        θ.hom.app W (Scheme.finiteEtaleTateOneGenerator R M T hR W r z) =
          Scheme.finiteEtaleTateOneGenerator A N T hAN W (φ r) (q.hom.app W z)) ∧
      SupportedDerivedScalarUnit φ T
        ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
      (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (κA.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
        κR.comp (Ext.mk₀ θ) (add_zero 2) := by
  let κM := geoCartierEtaleClass A M hM hAM i hI hTM
  have hκM := (geoCartierEtaleClass_spec A M hM hAM i hI hTM).1
  obtain ⟨η, ηT, hη, hηT, hcomm, _⟩ := exists_supported_kummer_arbitrary_scalar_maps φ i
  have hunit := (supported_kummer_scalar_derived_units T R A φ i η ηT hη hηT).2.1
  rw [hcomm] at hunit
  simp only [Iso.refl_inv, NatTrans.id_app] at hunit
  have hs := supported_kummer_scalar_of_source φ T M hM hR hAM hTM i hI
    κM κR hκM hκR η hη hunit
  unfold SupportedKummerScalar at hs
  obtain ⟨η', θ, hη', hθ, hunit', _, hsquare⟩ := hs
  have hmod : κM.comp (Ext.mk₀ e.hom) (add_zero 2) = κA := by
    exact (supported_cartier_boundary_existsUnique T N hN A hAN hTN i hI).unique
      (boundary_modulus A M N hdiv hAM hAN i hI hTM hTN q e hq he κM hκM) hκA
  let V := Sheaf.restrictScalars T.smallEtaleTopology φ
  refine ⟨η', θ ≫ V.map e.hom, hη', ?_, hunit', ?_⟩
  · intro W r z
    change e.hom.hom.app W (θ.hom.app W _) = _
    rw [hθ, he]
  · exact compose_scalar_modulus
      (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
      (D := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
      V
      (X := (lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Y := Scheme.finiteEtaleTateLine T M R hR)
      (X' := (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Y' := Scheme.finiteEtaleTateLine T M A hAM)
      (Z' := Scheme.finiteEtaleTateLine T N A hAN)
      ((lowerStar (ModuleCat.{u + 1} R) i).map η') θ e.hom κR κM κA hmod hsquare

end AlgebraicGeometry.Etale
