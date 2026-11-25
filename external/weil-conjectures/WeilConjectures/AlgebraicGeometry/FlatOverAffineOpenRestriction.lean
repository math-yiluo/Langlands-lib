/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Relative flatness after restriction to an affine base chart

Source: Stacks Project, Tag 01U4, final assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem flatOver_morphismRestrict
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (hflat : Scheme.Modules.IsFlatOver G f) (V : S.Opens) :
    Scheme.Modules.IsFlatOver ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj G)
      (f ∣_ V) := by
  intro V0 U0 e
  let V1 : S.affineOpens := ⟨V.ι ''ᵁ V0.1, V0.2.image_of_isOpenImmersion V.ι⟩
  let U1 : X.affineOpens :=
    ⟨(f ⁻¹ᵁ V).ι ''ᵁ U0.1, U0.2.image_of_isOpenImmersion (f ⁻¹ᵁ V).ι⟩
  have e1 : U1.1 ≤ f ⁻¹ᵁ V1.1 :=
    ((f ⁻¹ᵁ V).ι.image_mono e).trans (image_morphismRestrict_preimage f V V0.1).le
  have hh := hflat V1 U1 e1
  rw [morphismRestrict_appLE]
  convert hh using 1 <;> try rfl
  ext r m
  change (G.smul (((f ⁻¹ᵁ V).ι.appIso U0.1).inv.hom
    ((f.appLE V1.1 U1.1 e1).hom r))).asHom.hom m =
      (G.smul ((f.appLE V1.1 U1.1 e1).hom r)).asHom.hom m
  rw [Scheme.Opens.ι_appIso]
  rfl

private theorem flatOver_postcomp_iso
    {X S T : Scheme.{u}} (f : X ⟶ S) (k : S ⟶ T) [IsIso k] (G : X.Modules)
    (hflat : Scheme.Modules.IsFlatOver G f) : Scheme.Modules.IsFlatOver G (f ≫ k) := by
  intro V U e
  let V1 : S.affineOpens := ⟨k ⁻¹ᵁ V.1, V.2.preimage_of_isIso k⟩
  have e1 : U.1 ≤ f ⁻¹ᵁ V1.1 := by simpa only [Scheme.Hom.comp_preimage] using e
  let φ := k.app V.1
  let ψ := f.appLE V1.1 U.1 e1
  let : Module Γ(S, V1.1) Γ(G, U.1) := Module.compHom _ ψ.hom
  have : Module.Flat Γ(S, V1.1) Γ(G, U.1) := hflat V1 U e1
  let : Algebra Γ(T, V.1) Γ(S, V1.1) := φ.hom.toAlgebra
  have : Module.Flat Γ(T, V.1) Γ(S, V1.1) :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso φ)
  let : Module Γ(T, V.1) Γ(G, U.1) := Module.compHom _ φ.hom
  have : IsScalarTower Γ(T, V.1) Γ(S, V1.1) Γ(G, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have hh := Module.Flat.trans Γ(T, V.1) Γ(S, V1.1) Γ(G, U.1)
  simpa only [Scheme.Hom.comp_appLE] using hh

/-- The explicitly restricted module remains flat over the spectrum chart of the base.
Source: Stacks Project, Lemma 29.26.2, Tag 01U4, final assertion.
(blueprint: lem-pc-flat-over-affine-open-restriction).

Proof: take an affine open V0 of Spec Gamma(S,V) and an affine open U0 of f^{-1}(V)
whose image lies in V0. The inverse chart V.isoSpec.inv maps V0 isomorphically onto
an affine open V1 of S contained in V. The open immersion f^{-1}(V) -> X maps U0
isomorphically onto an affine open U1 of X, and U1 lies in f^{-1}(V1).
Apply hflat to V1 and U1. The appIso of the two open immersions identifies the
base rings and the sections of the restricted module. Naturality of appLE identifies
the scalar actions under these isomorphisms. Transport flatness along the resulting
semilinear equivalence and base-ring isomorphism; this proves the required affine
local condition for every V0 and U0. schemeOpenRestriction agrees with ordinary
restriction by overFunctorEquiv. Empty source opens have zero sections, which are
flat; no nonemptiness or flatness over O_X is assumed. -/
theorem isFlatOver_affineOpenRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f) (V : S.affineOpens) :
    Scheme.Modules.IsFlatOver ((schemeOpenRestriction X (f ⁻¹ᵁ V.1)).obj G)
      ((f ∣_ V.1) ≫ V.2.isoSpec.hom) := by
  refine Scheme.Modules.IsFlatOver.of_iso
    ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V.1)).app G).symm ?_
  exact flatOver_postcomp_iso (f ∣_ V.1) V.2.isoSpec.hom _
    (flatOver_morphismRestrict f G hflat V.1)

end AlgebraicGeometry
