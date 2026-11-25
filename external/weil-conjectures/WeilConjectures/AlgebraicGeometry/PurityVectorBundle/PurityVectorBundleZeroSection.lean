/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Vector bundles with chosen total spaces in the purity setting

The canonical relative spectrum, symmetric-algebra augmentation, and its zero section
are reused from `VectorBundleZeroSection`. The additional data here are an arbitrary
chosen total space and an isomorphism over the base to that relative spectrum.
The Noetherian instance required by that existing construction follows from finite type
over the fixed field; it is supplied by the existing theorem, never an extra hypothesis.

## References

* Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A rank-`c` vector bundle over a separated finite-type scheme over the fixed purity
field, including its chosen isomorphism `phi` to `Spec_Z Sym(𝓔)` over `Z`. -/
structure PurityVectorBundle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (hZ : Z ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] (c : ℕ) where
  E : Scheme.{u}
  p : E ⟶ Z
  𝓔 : Z.Modules
  [locallyFree : 𝓔.IsFiniteLocallyFreeOfRank c]
  phi : E ≅ @VectorBundleZeroSection.scheme Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree
  over_commutes : phi.hom ≫ @VectorBundleZeroSection.π Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree = p

namespace PurityVectorBundle

variable {P : WeilConjectures.PurityFiniteSetting.{u}}
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of P.field.k)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The zero section is the augmentation section of the canonical relative spectrum,
followed by the inverse of the chosen `phi`. The augmentation is the existing unique
algebra morphism killing `SymmetricAlgebraSheaf.inclusion`; its sectionwise composite
with `sectionMap` is `SymmetricAlgebra.algebraMapInv`. -/
def zeroSection (V : PurityVectorBundle P Z hZ c) : Z ⟶ V.E :=
  @VectorBundleZeroSection.zero Z (isNoetherian_of_locallyOfFiniteType hZ)
    c V.𝓔 V.locallyFree ≫ V.phi.inv

/-- The zero section is a section of the projection and a closed immersion. On every affine
open `U` its restriction, transported through `phi`, is the spectrum of the augmentation
`Sym(𝓔(U)) → 𝒪(U)` fixing constants and killing all degree-one generators. -/
theorem zeroSection_spec (V : PurityVectorBundle P Z hZ c) :
    V.zeroSection ≫ V.p = 𝟙 Z ∧ IsClosedImmersion V.zeroSection ∧
    ∀ U : Z.affineOpens,
      ∃ zU : U.1.toScheme ⟶
          ((@VectorBundleZeroSection.π Z (isNoetherian_of_locallyOfFiniteType hZ)
            c V.𝓔 V.locallyFree) ⁻¹ᵁ U.1).toScheme,
        zU ≫ ((@VectorBundleZeroSection.π Z (isNoetherian_of_locallyOfFiniteType hZ)
          c V.𝓔 V.locallyFree) ⁻¹ᵁ U.1).ι = U.1.ι ≫ V.zeroSection ≫ V.phi.hom ∧
        zU ≫ @VectorBundleZeroSection.affineChart Z
          (isNoetherian_of_locallyOfFiniteType hZ) c V.𝓔 V.locallyFree U =
          U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
            (SymmetricAlgebra.algebraMapInv (R := Z.presheaf.obj (op U.1))
              (M := V.𝓔.val.obj (op U.1))).toRingHom) := by
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType hZ
  let := V.locallyFree
  obtain ⟨hsection, hclosed⟩ := VectorBundleZeroSection.zero_spec Z c V.𝓔
  refine ⟨?_, ?_, ?_⟩
  · rw [zeroSection, ← V.over_commutes]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hsection
  · let := hclosed
    dsimp only [zeroSection]
    infer_instance
  · intro U
    refine ⟨VectorBundleZeroSection.zeroRestricted Z c V.𝓔 U.1, ?_,
      (VectorBundleZeroSection.affineChart_spec Z c V.𝓔 U).2.2⟩
    simp only [zeroSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Scheme.Hom.resLE_comp_ι _ _

end PurityVectorBundle
end AlgebraicGeometry
