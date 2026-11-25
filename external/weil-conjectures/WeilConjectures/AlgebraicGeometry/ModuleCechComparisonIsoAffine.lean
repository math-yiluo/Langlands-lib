/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso

/-! # The canonical Čech comparison for affine-intersection covers

Source: Stacks Project, Cohomology of Schemes, Tag 01XD, via Cohomology of Sheaves,
Tags 01ET and 01EQ (blueprint: lem-sc-cech-comparison-map-iso-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent module and an open cover whose nonempty finite intersections
are affine, the canonical Čech comparison is an isomorphism of global-section modules.
Thus this canonical map gives the identification of `lem-pc-cech-computes`.
Source: Stacks Project, Tags 01XD, 01ET and 01EQ
(blueprint: lem-sc-cech-comparison-map-iso-affine).
Proof: fix a degree p. The canonical comparison of
lem-sc-cech-comparison-map-naturality is defined by the alpha and beta maps of an
injective resolution and is independent of the resolution. Under the present affine
intersection and quasi-coherence hypotheses, lem-pc-cech-computes identifies Čech
cohomology with sheaf cohomology. Stacks 01ET identifies the isomorphism as the
canonical map of 01EQ: higher cohomology on the intersections vanishes by 01XB,
so the Čech-to-cohomology spectral sequence degenerates. Consequently the canonical
comparison in degree p is an isomorphism, giving precisely that identification. -/
theorem moduleCechComparison_isIso_of_affine (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] (p : ℕ)
    (c : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hc : IsModuleCechComparison U F p c) : IsIso c := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := injectiveResolution F
  have : QuasiIso (moduleCechBeta U I) :=
    moduleCechBeta_quasiIso_of_affine U hU F I
  have : IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) p) :=
    moduleCechAlpha_isIso U hcover I p
  have h := hc I
  have : IsIso (c ≫ (I.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫
        HomologicalComplex.homologyMap (moduleCechAlpha U I) p) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff c _).mp this

end AlgebraicGeometry.Scheme.Modules
