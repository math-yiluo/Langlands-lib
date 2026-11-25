/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkComplexIso
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalTensorComparisonScalar
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalTensorComparisonOne
@[expose] public section

/-! Canonical spectrum tensor generator formula for a fixed chain isomorphism -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical affine-spectrum comparison respects tensor generators for the explicitly
constructed input coordinates, not for arbitrary chain isomorphisms.
Proof: the coefficient-one identity is the composition-unit germ calculation. The
comparison is semilinear over the actual stalk map along X'.isoSpec.inv. Write
`d tensor x = d • (1 tensor x)`, use semilinearity, and then the coefficient-one
identity. The chain coordinates are constructed from the extension/restriction unit
and the inverse pullback-stalk comparison; source-point transport is by isoSpec naturality.
Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-generator-formula-of-q). -/
theorem canonicalSpectrum_tensor_generator_formula_of_q
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    let := (tensorMap f f' g g' sq z).toAlgebra
    let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    let := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    let := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    let := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    let := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let H :=
      let z := X'.isoSpec.inv z0
      let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj P
      let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
      let j := X'.isoSpec.inv
      let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
      let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
      let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
        AddCommGrpCat.{u}
      let alpha := (NatIso.mapHomologicalComplex
        ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
        Scheme.Modules.tensorPullbackCompositionIso j g'
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
        (.up ℤ)).app P
      let U :=
        letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
        letI : (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0).Additive :=
          comparisonStalkAdditive (Spec Γ(X', ⊤)) z0
        let E := Scheme.Modules.tensorPullback j
        let S := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙
          forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        let SZ := RingedSpace.moduleStalkFunctor X'.toRingedSpace (j z0)
        let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (j z0))) AddCommGrpCat.{u}
        let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        (Functor.mapHomologicalComplexCompIso (Iso.refl (SZ ⋙ F)) (.up ℤ)).app Pg ≪≫
          (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j z0) (.up ℤ)).app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm.app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙ F0))
            (.up ℤ)).symm.app ((E.mapHomologicalComplex (.up ℤ)).obj Pg)
      let H := (F.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso f f' g g' sq z P) ≪≫ U ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          ((S0.mapHomologicalComplex (.up ℤ)).mapIso alpha.symm) ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).symm
      H
    let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
      (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
        (Scheme.isoSpec_inv_naturality g')).symm
    let eA := canonicalSpectrumStalkEquiv X (g' z) ((Spec.map g'.appTop) z0) hA
    let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
    let q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q0 :=
      canonicalSpectrumStalkComplexIso X (g' z) ((Spec.map g'.appTop) z0) hA P
    (∀ (k : ℤ) (d : C z) (x : Q.X k),
        H.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by
  intro z P0 _ _ _ _ _ _ _ _ _ _ R0 A0 B0 Q Q0 H hA eA eD q k d x
  have hs := canonicalSpectrum_tensor_comparison_smul f f' g g' sq sq0 z0 P k d
    ((1 : C (X'.isoSpec.inv z0)) ⊗ₜ[_, _] x)
  have hu := canonicalSpectrum_tensor_comparison_one f f' g g' sq sq0 z0 P k x
  have hl := ModuleCat.ExtendScalars.smul_tmul
    ((tensorMap f f' g g' sq z).comp
      (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
    (M := (stalkComplex g' z P).X k) d 1 x
  simp only [mul_one] at hl
  have hr := ModuleCat.ExtendScalars.smul_tmul
    ((tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
      (algebraMap (A (Spec.map g'.appTop) z0)
        (A (Spec.map g'.appTop) z0 ⊗[R (Spec.map f.appTop) (Spec.map g'.appTop) z0]
          B (Spec.map f'.appTop) z0)))
    (M := (stalkComplex (Spec.map g'.appTop) z0 P0).X k)
    (canonicalSpectrumStalkEquiv X' z z0 rfl d) 1 (q.hom.f k x)
  simp only [mul_one] at hr
  exact (congrArg (fun t ↦ H.hom.f k t) hl.symm).trans
    (hs.trans ((congrArg (fun t : (tensorComplex (Spec.map f.appTop)
      (Spec.map f'.appTop) (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).X k ↦
        eD d • t) hu).trans hr))

end AlgebraicGeometry.SingleComplexBaseChange
