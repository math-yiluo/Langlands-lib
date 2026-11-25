/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # Affine ordinary tensor coordinates for quasi-coherent coefficients

Source: Stacks Project, Tags 08DX(2), 08DV, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-- Affine algebraic resolutions compute ordinary tensor homology of a supplied
K-flat resolution of a quasi-coherent sheaf, naturally for supplied augmented lifts.
This statement concerns only complexes and ordinary homology. It neither constructs
algebraic lifts nor compares any derived tensor objects.

Source: Stacks Project, Tags 08DX(2), 08DV, 06YB, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates).

Proof: Choose a K-flat resolution F -> N[0] using
CochainComplex.exists_isKFlatResolution. For each affine open U, take the explicitly
constructed tensorResolutionCoordinateSections for P_U, K and F. These are the
normalized coordinates from the exact affine sheaf comparison and the common
K-flat tensor zigzag. Apply tensorResolutionCoordinateSections_naturality directly
to each supplied b, a and k with their augmentation, coefficient and tensor
formulas. This gives the required restriction equation for that coordinate family.
No comparison witnesses or comparison-independence homotopy are needed. The same
construction covers unbounded K, n=0, zero coefficients and empty affine opens. -/
theorem exists_qcoh_ordinary_tensor_resolution_coordinates
    (Y : Scheme.{u}) (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj N)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
          (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)] Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∀ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) →
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) →
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) →
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  dsimp only
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf)
    ((CochainComplex.singleFunctor Y.Modules 0).obj N)
  let c := fun U : Y.affineOpens ↦
    tensorResolutionCoordinateSections Y M N U (MA U) (NA U)
      (sM U) (sN U) (P U) K F q s hK hF hq hs n
  refine ⟨c, ?_⟩
  intro V U h _hbasic b a k ha hb hk x
  exact tensorResolutionCoordinateSections_naturality Y M N MA NA sM sN P
    K F q s hK hF hq hs n V U h b a k ha hb hk x

end AlgebraicGeometry
