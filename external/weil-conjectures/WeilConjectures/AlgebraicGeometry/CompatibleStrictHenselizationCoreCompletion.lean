/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiber
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
set_option linter.unusedVariables.funArgs false in
/-- Functoriality between affine presentations of compatible strict henselizations.
Source: Stacks Project, Tag 04GU. (blueprint: compatible-strict-henselization-core-completion)

Proof: the equality of geometric points gives the functor from pointed etale neighbourhoods
of S to those of T by base change. Its maps to the two colimits induce the morphism from
strictLocalization t to strictLocalization s over g. Transport through eA and
eB, then use the fully faithful contravariant Spec functor to obtain the ring homomorphism.
On closed points this sends the selected geometric point to the selected geometric point;
the corresponding map of local rings is local. The colimit cone compatibility gives the
structural equality. -/
theorem Etale.exists_compatibleStrictHenselizationCoreCompletion
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω A B : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [CommRing B] [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g)
    (eA : Spec (.of A) ≅ strictLocalization s)
    (eB : Spec (.of B) ≅ strictLocalization t) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase s =
        eB.hom ≫ strictLocalizationToBase t ≫ g := by
  obtain ⟨f, hf⟩ := exists_strictHenselizationSchemeMap hst
  let F : Spec (.of B) ⟶ Spec (.of A) := eB.hom ≫ f ≫ eA.inv
  let φ : A →+* B := (Spec.preimage F).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = F := by
    exact Spec.map_preimage F
  have hw : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
      strictLocalizationToBase s =
      eB.hom ≫ strictLocalizationToBase t ≫ g := by
    rw [hφ]
    simp only [F, Category.assoc, Iso.inv_hom_id_assoc, hf]
  refine ⟨φ, ?_, hw⟩
  apply (IsLocalRing.isLocalHom_iff_comap_closedPoint φ).mpr
  change Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint B) = _
  apply (strictHenselizationStructuralMap_fiber_eq_closedPoint s eA _).mp
  have hb := (strictHenselizationStructuralMap_fiber_eq_closedPoint
    t eB (IsLocalRing.closedPoint B)).mpr rfl
  calc
    (eA.hom ≫ strictLocalizationToBase s)
        (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint B)) =
        (eB.hom ≫ strictLocalizationToBase t ≫ g)
          (IsLocalRing.closedPoint B) := by
            rw [← Scheme.Hom.comp_apply, hw]
    _ = g (t (IsLocalRing.closedPoint Ω)) := by
      rw [← Category.assoc, Scheme.Hom.comp_apply, hb]
    _ = s (IsLocalRing.closedPoint Ω) := by rw [hst, Scheme.Hom.comp_apply]
end AlgebraicGeometry
