/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueEvaluationHomologyNaturality
import WeilConjectures.AlgebraicGeometry.Affine.AffinePerfectResidueModelNaturality

/-! # Naturality of strictly perfect affine residue models

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-affine-residue-model-naturality)
-/

public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem affineResidueModel_map_square
    {D₀ D₁ D₂ : Type*} [Category D₀] [Category D₁] [Category D₂]
    (R : D₀ ⥤ D₁) (H : D₁ ⥤ D₂) (A : D₀ ⥤ D₂) (θ : R ⋙ H ≅ A)
    {E E' : D₀} (b : E ⟶ E') {K C : D₁}
    (m : R.obj E ≅ K) (m' : R.obj E' ≅ C) (f : K ⟶ C)
    (hf : f = m.inv ≫ R.map b ≫ m'.hom) :
    H.map f ≫ (H.mapIso m'.symm ≪≫ θ.app E').hom =
      (H.mapIso m.symm ≪≫ θ.app E).hom ≫ A.map b := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [hf, H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc m'.hom m'.inv, m'.hom_inv_id, H.map_id, Category.id_comp]
  exact congrArg (fun a ↦ H.map m.inv ≫ a) (θ.hom.naturality b)

variable
  [∀ Y : Scheme.{v},
    HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
  [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
    (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The comparison from the residue cycle homology of a strictly perfect affine model `K` of
`E` (via the model isomorphism `m`) to the degree-one derived fibre cohomology of `E`.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-affine-residue-model-naturality)

Construction: identify residue cycle homology with homology of the residue extension of
sections, apply `affinePerfectResidueModelIso`, transport along `m`, and use the open
factorization of derived fibre cohomology. -/
noncomputable def affineResidueModelEquiv
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (E : schemeDerivedCategory W)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (m : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    affineResidueCycleHomology W U p K ≃+ derivedFiberCohomology W E 1 w :=
  let q := Classical.choose (affine_residue_evaluation_homology_naturality W w U hwU hU p hp)
  let θ := Classical.choice (derived_fiber_open_factorization W w U hwU 1)
  let H := localDerivedFiberCohomologyFunctor W w U hwU 1
  let oK : H.obj (DerivedCategory.Q.obj K) ≅ (derivedFiberCohomologyFunctor W w 1).obj E :=
    H.mapIso m.symm ≪≫ θ.app E
  ((q K).trans
    ((affinePerfectResidueModelIso W w U hwU hU).app ⟨K, hK⟩).toLinearEquiv.toAddEquiv).trans
    oK.toLinearEquiv.toAddEquiv

-- The model isomorphisms compare multiple derived and residue-module structures.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical affine model comparisons are natural: if a chain map `φ : K ⟶ C` represents
`b : E ⟶ E'` through the model isomorphisms `m` and `m'`, then the residue cycle homology map
of `φ` corresponds to the derived fibre cohomology map of `b`.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-affine-residue-model-naturality)

Proof: naturality of `affinePerfectResidueModelIso` and of the evaluation comparison give the
square for `Q(φ)` in local derived fibre cohomology; substituting the hypothesis on `Q(φ)` and
using naturality of the open factorization gives the square for `b`. -/
theorem affineResidueModelEquiv_naturality
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    {E E' : schemeDerivedCategory W} (b : E ⟶ E')
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (hK : IsStrictlyPerfect W U K) (hC : IsStrictlyPerfect W U C)
    (m : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)
    (m' : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E' ≅ DerivedCategory.Q.obj C)
    (φ : K ⟶ C)
    (hφ : DerivedCategory.Q.map φ = m.inv ≫ (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom)
    (z : affineResidueCycleHomology W U p K) :
    affineResidueModelEquiv W w U hwU hU p hp E' C hC m' (affineResidueCycleHomologyMap φ z) =
      (derivedFiberCohomologyFunctor W w 1).map b
        (affineResidueModelEquiv W w U hwU hU p hp E K hK m z) := by
  classical
  let R := (SheafOfModules.overFunctor.{v}
    (moduleRings W.toRingedSpace) U).mapDerivedCategory
  let H := localDerivedFiberCohomologyFunctor W w U hwU 1
  let A := derivedFiberCohomologyFunctor W w 1
  let θ := Classical.choice (derived_fiber_open_factorization W w U hwU 1)
  have hq := Classical.choose_spec
    (affine_residue_evaluation_homology_naturality W w U hwU hU p hp)
  let q := Classical.choose (affine_residue_evaluation_homology_naturality W w U hwU hU p hp)
  let t := affinePerfectResidueModelIso W w U hwU hU
  let oK : H.obj (DerivedCategory.Q.obj K) ≅ A.obj E := H.mapIso m.symm ≪≫ θ.app E
  let oC : H.obj (DerivedCategory.Q.obj C) ≅ A.obj E' := H.mapIso m'.symm ≪≫ θ.app E'
  let eK := (q K).trans (t.app ⟨K, hK⟩).toLinearEquiv.toAddEquiv
  let eC := (q C).trans (t.app ⟨C, hC⟩).toLinearEquiv.toAddEquiv
  have hlocal : eC (affineResidueCycleHomologyMap φ z) =
      H.map (DerivedCategory.Q.map φ) (eK z) := by
    change (t.app ⟨C, hC⟩).hom (q C (affineResidueCycleHomologyMap φ z)) = _
    rw [hq K C φ z]
    exact ConcreteCategory.congr_hom
      (t.hom.naturality (X := ⟨K, hK⟩) (Y := ⟨C, hC⟩) (ObjectProperty.homMk φ))
        (q K z)
  have hsquare : H.map (DerivedCategory.Q.map φ) ≫ oC.hom = oK.hom ≫ A.map b := by
    exact affineResidueModel_map_square R H A θ b m m' _ hφ
  change oC.hom (eC (affineResidueCycleHomologyMap φ z)) = A.map b (oK.hom (eK z))
  rw [hlocal]
  exact ConcreteCategory.congr_hom hsquare (eK z)

end AlgebraicGeometry.Scheme
