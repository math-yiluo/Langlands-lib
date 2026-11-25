/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import
  WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturalityFromSquare
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor

/-! # Affine tensor-homology naturality

Source: Stacks Project, Tags 08DX(2), 06YT and 01I9.
(blueprint: new-t3-qcoh-tensor-resolution-chart-homology-naturality).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance QCohTensorResolutionChartHomologyNaturality_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance QCohTensorResolutionChartHomologyNaturality_zero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance QCohTensorResolutionChartHomologyNaturality_objZero
    (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- Naturality of the affine tensor homology identification.

Source: Stacks Tags 08DX(2), 08DV and 01I9, the affine derived tensor calculation
and its functorial associated-sheaf identification.

Proof in words: extend the chain maps to cochain complexes, placing chain degree j
in degree -j. In these degrees the formula hk identifies the tensor comparison
with the tensor of the sheafified map a and the coefficient map b. To check this,
apply the associated-sheaf tensor isomorphism on pure tensors. The equation hb
identifies the sheafified coefficient map, conjugated by the two normalized
coefficient isomorphisms, with restriction of N. The pure tensors generate the
tensor product, so the two maps agree. In strictly positive cochain degrees both
extended complexes vanish, and the square follows from the zero-object property.
Taking homology gives the square for the chart tensor isomorphism. Use naturality
of exact associated-sheaf homology to move the tilde functor past homology; its
semilinear version is tensorResolutionSemilinearMap_homologyData. Finally use
extension homology in degree -n, with tensorResolutionExtendHomologyMapData, to
identify the induced map with H_n(k) followed by the restriction-of-scalars
homology isomorphism. Compose these three squares and cancel inverse isomorphisms.
This argument includes n = 0, zero modules, and the zero ring, and does not require
the ring restriction map to be flat.

(blueprint: new-t3-qcoh-tensor-resolution-chart-homology-naturality) -/
theorem tensorResolutionChartHomologyIso_naturality
    (Y : Scheme.{u}) (N : Y.Modules) [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (b : NA U →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] NA V)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (k : ((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj (P U).complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj
        (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex))
    (hb : ∀ y : NA U,
      sN V (b y) = N.val.map (homOfLE h).op (sN U y))
    (hk : ∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) :
    let φ := Y.presheaf.map (homOfLE h).op
    let LB := ((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex
    let t := HomologicalComplex.homologyMap k n ≫
      ((LB.sc n).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map
        (tensorResolutionChartHomologyIso N U (MA U) (NA U) (sN U) (P U) n).hom ≫
        (((CochainComplex.mapBifunctor (tensorResolutionChartComplex U (MA U) (P U))
          (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor Y.Modules 0).obj N))
          (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso
            (Scheme.Modules.restrictFunctor (Spec.map φ))).inv ≫
        HomologicalComplex.homologyMap
          (tensorResolutionRestrictionTensorMap (Spec.map φ)
            (tensorResolutionChartComplex U (MA U) (P U))
            (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
              ((CochainComplex.singleFunctor Y.Modules 0).obj N))
            (tensorResolutionChartComplex V (MA V) (P V))
            (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
              ((CochainComplex.singleFunctor Y.Modules 0).obj N))
            (tensorResolutionSemilinearComplexMap φ (.up ℤ)
              ((P U).complex.extend ComplexShape.embeddingDownNat)
              ((P V).complex.extend ComplexShape.embeddingDownNat)
              (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat
                (P U).complex (P V).complex a))
            (tensorResolutionChartRestrictionComplexIso Y V U h
              ((CochainComplex.singleFunctor Y.Modules 0).obj N)).hom) (-(n : ℤ)) =
      tensorResolutionSemilinearMap φ t ≫
        (tensorResolutionChartHomologyIso N V (MA V) (NA V) (sN V) (P V) n).hom := by
  dsimp only
  let φ := Y.presheaf.map (homOfLE h).op
  let b' : (NA U) ⟶ (ModuleCat.restrictScalars φ.hom).obj (NA V) :=
    ModuleCat.ofHom (X := NA U) (Y := (ModuleCat.restrictScalars φ.hom).obj (NA V))
      { toFun := b
        map_add' := b.map_add'
        map_smul' := b.map_smul' }
  have hb' : ∀ y : NA U,
      sN V (b' y) = N.val.map (homOfLE h).op (sN U y) := by
    intro y
    exact hb y
  have hk' : ∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (show NA V from b' y) := by
    intro j x y
    exact hk j x y
  let EA := tensorResolutionChartComplex U (MA U) (P U)
  let EB := tensorResolutionChartComplex V (MA V) (P V)
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
  let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
  let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
    ((P U).complex.extend ComplexShape.embeddingDownNat)
    ((P V).complex.extend ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat
      (P U).complex (P V).complex a)
  let l := tensorResolutionRestrictionTensorMap (Spec.map φ)
    EA (RU.obj N0) EB (RV.obj N0) a'
    (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom
  have hl := tensorResolutionChartTensorIso_naturality_of_pure_tensors
    N V U h (MA U) (NA U) (MA V) (NA V) (sN U) (sN V)
    (P U) (P V) b' a k hb' hk'
  exact tensorResolutionChartHomologyIso_naturality_of_square
    Y N V U h (MA U) (NA U) (MA V) (NA V) (sN U) (sN V)
    (P U) (P V) n k l hl

end AlgebraicGeometry
