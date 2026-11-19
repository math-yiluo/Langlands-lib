import Langlands.CommutativeAlgebra.IntegralClosureTransfer
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Normalization

/-! # Relative normalization of affine schemes -/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

open Langlands.CommutativeAlgebra.IntegralClosureTransfer

variable (D G : Type u) [CommRing D] [CommRing G] [Algebra D G]

local notation "f" => Spec.algebraMap D G
local notation "N" => integralClosure D G

private lemma gammaSpec_commutes (d : Γ(Spec (.of D), ⊤)) :
    (Scheme.ΓSpecIso (.of G)).hom ((f).appTop d) =
      algebraMap D G ((Scheme.ΓSpecIso (.of D)).hom d) := by
  exact congrArg (fun h : Γ(Spec (.of D), ⊤) ⟶ CommRingCat.of G => h d)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap D G)))

/-- The global ring of an affine relative normalization is the integral closure in
the ring defining the source. -/
def affineNormalizationGlobalSectionsIso : Γ((f).normalization, ⊤) ≅ CommRingCat.of N := by
  letI := ((f).app ⊤).hom.toAlgebra
  let eD := (Scheme.ΓSpecIso (.of D)).commRingCatIsoToRingEquiv
  let eG : Γ(Spec (.of G), f ⁻¹ᵁ ⊤) ≃+* G :=
    (Scheme.ΓSpecIso (.of G)).commRingCatIsoToRingEquiv
  let e := integralClosureEquiv eD eG (gammaSpec_commutes D G)
  exact (f).normalizationObjIso (isAffineOpen_top _) ≪≫ e.toCommRingCatIso

@[reassoc]
lemma fromNormalization_appTop_affineNormalizationGlobalSectionsIso :
    (f).fromNormalization.appTop ≫ (affineNormalizationGlobalSectionsIso D G).hom =
      (Scheme.ΓSpecIso (.of D)).hom ≫ CommRingCat.ofHom (algebraMap D N) := by
  let := ((f).app ⊤).hom.toAlgebra
  let hU : IsAffineOpen (⊤ : (Spec (.of D)).Opens) := isAffineOpen_top _
  let eD := (Scheme.ΓSpecIso (.of D)).commRingCatIsoToRingEquiv
  let eG : Γ(Spec (.of G), f ⁻¹ᵁ ⊤) ≃+* G :=
    (Scheme.ΓSpecIso (.of G)).commRingCatIsoToRingEquiv
  let e := integralClosureEquiv eD eG (gammaSpec_commutes D G)
  calc
    _ = (f).fromNormalization.app ⊤ ≫ ((f).normalizationObjIso hU).hom ≫
        e.toCommRingCatIso.hom := rfl
    _ = _ := by
      rw [(f).fromNormalization_app_assoc hU, Iso.inv_hom_id_assoc]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      exact integralClosureEquiv_algebraMap eD eG (gammaSpec_commutes D G) d

/-- The relative normalization of `Spec D` in `Spec G` is the spectrum of the
integral closure of `D` in `G`. -/
def affineNormalizationIso : (f).normalization ≅ Spec (.of N) := by
  have : IsAffine (f).normalization := isAffine_of_isAffineHom (f).fromNormalization
  exact (f).normalization.isoSpec ≪≫
    Scheme.Spec.mapIso (affineNormalizationGlobalSectionsIso D G).symm.op

@[reassoc]
lemma affineNormalizationIso_hom_comp :
    (affineNormalizationIso D G).hom ≫ Spec.algebraMap D N = (f).fromNormalization := by
  apply (cancel_mono (Spec (.of D)).toSpecΓ).mp
  rw [Scheme.toSpecΓ_naturality (f).fromNormalization]
  change ((f).normalization.toSpecΓ ≫
    Spec.map (affineNormalizationGlobalSectionsIso D G).inv) ≫ Spec.algebraMap D N ≫
      (Spec (.of D)).toSpecΓ = _
  rw [Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    ← Spec.map_comp, ← fromNormalization_appTop_affineNormalizationGlobalSectionsIso,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Finiteness of the relative normalization of affine schemes is the module
finiteness of the integral closure. -/
theorem isFinite_fromNormalization_iff :
    IsFinite (f).fromNormalization ↔ Module.Finite D N := by
  have hfin : IsFinite (Spec.algebraMap D N) ↔ Module.Finite D N :=
    (IsFinite.SpecMap_iff _).trans RingHom.finite_algebraMap
  constructor
  · intro h
    apply hfin.mp
    have : IsFinite ((affineNormalizationIso D G).inv ≫ (f).fromNormalization) :=
      inferInstance
    rwa [← affineNormalizationIso_hom_comp D G, Iso.inv_hom_id_assoc] at this
  · intro h
    have : IsFinite (Spec.algebraMap D N) := hfin.mpr h
    rw [← affineNormalizationIso_hom_comp D G]
    infer_instance

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
