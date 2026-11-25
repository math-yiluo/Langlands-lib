/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalTensorGeneratorFormulaOfQ
/-! # Canonical affine spectrum comparison on tensor generators

Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-generator-formula).
-/

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

-- The fixed stalk comparison requires substantial definitional reduction.
/-- Existence of input-complex coordinates compatible with the fixed comparison,
using the actual affine-spectrum stalk ring maps.

Proof: put a = X.isoSpec.inv and j = X'.isoSpec.inv. Along a, the canonical
pullback-stalk comparison is an isomorphism from the stalk of a*P to extension
of scalars of the stalk of P. Since a induces an invertible stalk ring map,
the extension/restriction unit is an isomorphism. Compose that unit with the
inverse pullback-stalk comparison after restricting scalars; transport its
source point by isoSpec naturality. Apply this natural linear isomorphism in
every degree. Naturality with respect to the differentials gives q and its
inverse as chain maps. This constructs q; it does not use an arbitrary witness
of an existence statement without a characterizing property.
To check the generator equation, represent x by a section germ. The first
comparison sends d tensor x to d times the germ of the pullback unit applied to
that section. The comparison along j sends this germ to its pullback along j,
and sends the coefficient d through j.stalkMap. The composition mate alpha is
characterized by the composite adjunction units: its inverse identifies this
successive pullback-unit germ with the pullback-unit germ along the spectrum
map applied to the section pulled back along a. This is precisely the germ
obtained from q(x). The inverse last tensor-stalk comparison therefore returns
eD(d) tensor q(x). Every stalk element has a section-germ representative, so
this proves the formula for every x and d in every degree. The coefficient
maps are the displayed actual stalk maps; equality transport changes neither
the germ nor the formula. The argument works for the zero complex and zero
modules. No flatness or boundedness is needed, and an empty spectrum has no z0.
Source: Stacks Project, Tags 0098 (pullback stalks), 0096 (adjunction units),
and 0DJ8 (affine reduction).
(blueprint: lem-pc-affine-spectrum-canonical-tensor-generator-formula). -/
theorem exists_canonicalSpectrum_tensor_generator_formula
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
    ∃ q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q0,
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        H.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by
  dsimp only
  let z := X'.isoSpec.inv z0
  let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  refine ⟨canonicalSpectrumStalkComplexIso X (g' z) ((Spec.map g'.appTop) z0) hA P, ?_⟩
  exact canonicalSpectrum_tensor_generator_formula_of_q f f' g g' sq sq0 z0 P

end AlgebraicGeometry.SingleComplexBaseChange
