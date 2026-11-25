/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.RestrictStalkInvSmul
/-! # Scalar compatibility of the canonical affine-spectrum comparison -/

@[expose] public section

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

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem isoPullbackAdditiveStalkIso_smul
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] (y : Y) (M : Z.Modules)
    (d : Z.presheaf.stalk (j y))
    (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).obj M) :
    (isoPullbackAdditiveStalkIso j y).hom.app M (d • x) =
      (j.stalkMap y).hom d •
        (show (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
          ((Scheme.Modules.tensorPullback j).obj M) from
          (isoPullbackAdditiveStalkIso j y).hom.app M x) := by
  change ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
    ((tensorPullbackRestrictIso j).inv.app M))
      ((Scheme.Modules.restrictStalkNatIso j y).inv.app M (d • x)) = _
  rw [Scheme.Modules.restrictStalkNatIso_inv_smul, map_smul]
  rfl

-- Identifying the complex composition factors reduces several stalk functor types.
/-- Scalar compatibility of the fixed additive comparison; this assertion does not involve
input-complex coordinates or the coefficient-one equation.
Proof: the two tensor-stalk isomorphisms are linear over their output stalk rings.
The intervening map alpha is a sheaf-module isomorphism, so its stalk is linear.
For the additive pullback-stalk comparison along j, restriction on germs sends
r times m to j.stalkMap(r) times the restricted germ of m. The adjunction uniqueness
map from tensor pullback to restriction is a sheaf-module map and hence preserves
that action. Thus isoPullbackAdditiveStalkIso is semilinear over j.stalkMap.
Composing gives semilinearity of H; its coefficient map is exactly eD because
the point transport here is reflexive. Lifting to complexes and inserting the
functor composition isomorphisms preserves this degreewise equation.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-comparison-scalar). -/
theorem canonicalSpectrum_tensor_comparison_smul
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
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
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
    let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
    ∀ (k : ℤ) (d : C z) (t : (tensorComplex f f' g g' sq z P).X k),
      H.hom.f k (d • t) = eD d • (show (tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).X k from H.hom.f k t) := by
  dsimp only
  intro k d t
  let z := X'.isoSpec.inv z0
  let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
    (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let j := X'.isoSpec.inv
  let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
  let alpha := (NatIso.mapHomologicalComplex
    ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso j g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
    (.up ℤ)).app P
  let a := (tensorStalkIso f f' g g' sq z P).hom.f k
  let b := (isoPullbackAdditiveStalkIso j z0).hom.app (Pg.X k)
  let c := (S0.mapHomologicalComplex (.up ℤ)).map alpha.inv |>.f k
  let e := (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).inv.f k
  change e (c (b (a (d • t)))) =
    canonicalSpectrumStalkEquiv X' z z0 rfl d • e (c (b (a t)))
  have hb := isoPullbackAdditiveStalkIso_smul j z0 (Pg.X k) d (a t)
  have hd : (j.stalkMap z0).hom d = canonicalSpectrumStalkEquiv X' z z0 rfl d := by
    simp only [canonicalSpectrumStalkEquiv, eqToIso_refl, Iso.refl_trans]
    rfl
  -- Keep the scalar identities typed as linear maps before composing them.
  have ha := a.hom.map_smul d t
  have hc := c.hom.map_smul ((j.stalkMap z0).hom d) (b (a t))
  have he := e.hom.map_smul ((j.stalkMap z0).hom d) (c (b (a t)))
  exact (congrArg (fun v ↦ e (c (b v))) ha).trans
    ((congrArg (fun v ↦ e (c v)) hb).trans
      ((congrArg (fun v ↦ e v) hc).trans
        (he.trans (congrArg (fun r ↦ r • e (c (b (a t)))) hd))))


end AlgebraicGeometry.SingleComplexBaseChange
