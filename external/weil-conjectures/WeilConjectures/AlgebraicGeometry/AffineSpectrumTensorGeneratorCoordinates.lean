/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalTensorGeneratorFormula
/-! # Affine spectrum stalk coordinates on tensor generators

Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-tensor-generator-coordinates).
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

/-- The fixed additive chain isomorphism between the original and spectrum tensor
complexes, obtained by the two tensor-stalk comparisons and pullback composition.
Source: Stacks Project, sheaves.tex, lemma-stalk-pullback-modules (0098) and
lemma-adjoint-pullback-pushforward-modules (0096).
(blueprint: lem-pc-affine-spectrum-tensor-generator-coordinates). -/
@[irreducible]
def affineSpectrumTensorAdditiveIso
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
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

set_option linter.unusedVariables false in
/-- Affine stalk coordinates and the formula for the canonical additive comparison
on pure tensors. This does not assert linearity or construct a tensor chain isomorphism.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules; Tag 0096,
pullback adjunction; Tag 0DJ8, affine reduction of equation-bc.
(blueprint: lem-pc-affine-spectrum-tensor-generator-coordinates).
Proof: use the stalk ring isomorphisms induced by the four isoSpec inverses.
Naturality of isoSpec and the composition law for stalk maps identify the maps
from R to A and B and the tensor-to-D map. The pullback-stalk comparison along
X.isoSpec.inv, transported over the point equality from isoSpec naturality,
gives q. For d tensor x, the tensorStalkIso sends this tensor to the germ d
multiplying the pullback germ of x. The additive stalk comparison along j and
the adjunction mate defining alpha send these germs to the same germs in the
spectrum square. Applying the inverse spectrum tensorStalkIso gives exactly
eD(d) tensor q(x). Naturality in the differential gives q as a chain isomorphism.
No flatness, boundedness, or nonzero assumption is used; the zero complex and
zero stalk rings satisfy the same formula. -/
theorem exists_affineSpectrum_tensor_generator_coordinates
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
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
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    let H := affineSpectrumTensorAdditiveIso f f' g g' sq sq0 z0 P
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        H.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by
  intro z P0 Pg j S0 F F0 alpha R0 A0 B0 D0 Q Q0 V0 H
  let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  let eA := canonicalSpectrumStalkEquiv X (g' z) ((Spec.map g'.appTop) z0) hA
  let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
  refine (exists_canonicalSpectrum_stalk_ring_coordinates f f' g g' sq sq0 z0).elim
    fun eR hR ↦ ?_
  refine hR.elim fun eB hR ↦ ?_
  refine (exists_canonicalSpectrum_tensor_generator_formula f f' g g' sq sq0 z0 P).elim
    fun q hq ↦ ?_
  refine ⟨eR, eA, eB, eD, q, hR.1, hR.2.1, hR.2.2, ?_⟩
  simpa only [H, affineSpectrumTensorAdditiveIso] using hq

end AlgebraicGeometry.SingleComplexBaseChange
