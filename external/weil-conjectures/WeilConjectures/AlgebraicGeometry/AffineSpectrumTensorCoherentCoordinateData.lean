/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.AffineSpectrumTensorGeneratorCoordinates
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
private theorem tensor_additive_smul
    {A₁ D₁ A₂ D₂ : Type u} [CommRing A₁] [CommRing D₁]
    [CommRing A₂] [CommRing D₂] (a : A₁ →+* D₁) (a₀ : A₂ →+* D₂)
    (M : ModuleCat.{u} A₁) (M₀ : ModuleCat.{u} A₂) (e : D₁ →+* D₂)
    (p : M → M₀)
    (h : (forget₂ (ModuleCat D₁) AddCommGrpCat).obj ((ModuleCat.extendScalars a).obj M) ⟶
      (forget₂ (ModuleCat D₂) AddCommGrpCat).obj ((ModuleCat.extendScalars a₀).obj M₀))
    (hg : ∀ d x, h (d ⊗ₜ[A₁,a] x) = e d ⊗ₜ[A₂,a₀] p x)
    (r : D₁) (v : (ModuleCat.extendScalars a).obj M) :
    h (r • v) = e r • (show (ModuleCat.extendScalars a₀).obj M₀ from h v) := by
  induction v using TensorProduct.inductionOn with
  | tmul d x =>
    rw [ModuleCat.ExtendScalars.smul_tmul, hg, hg, map_mul]
    rfl
  | add v v' hv hv' => simp only [smul_add, map_add, hv, hv']

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical additive pullback-stalk comparison on ordinary complexes.
Source: Stacks Project, Tag 0098, stalk pullback formula.
(blueprint: lem-pc-affine-spectrum-tensor-coherent-coordinate-data). -/
def ordinaryIsoPullbackStalkComplexIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :=
  letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  letI : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  let E := Scheme.Modules.tensorPullback j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let SZ := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  (Functor.mapHomologicalComplexCompIso (Iso.refl (SZ ⋙ F)) (.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm.app P ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙ F0))
      (.up ℤ)).symm.app ((E.mapHomologicalComplex (.up ℤ)).obj P)

-- The stalk comparison has several nested complex functor compositions.
/-- Canonical affine coordinates with chain-level pullback-stalk coherence.
Source: Stacks Project, Tag 0098 (stalk pullback formula), Tag 0096 (adjunction),
and Tag 0DJ8 (affine reduction).
(blueprint: lem-pc-affine-spectrum-tensor-coherent-coordinate-data).
Proof: obtain the four stalk ring coordinates and q, with the pure-tensor formula
for the fixed additive comparison H, from the generator-coordinate lemma. In each
degree tensor induction proves H(r v) = eD(r) H(v): zero and sums use additivity,
and a pure tensor uses the generator formula and multiplicativity of eD.
ModuleCat.isoMk lifts each additive component to a linear isomorphism into
restriction of scalars. The differential equation is inherited from H, and
HomologicalComplex.Hom.isoOfComponents assembles t. Its tensor formula is the
same generator formula. After forgetting scalars, t is H by extensionality.
Postcompose with the spectrum tensorStalkIso: its inverse in H cancels, giving
exactly the requested chain coherence. No flatness or boundedness is needed. -/
theorem exists_affineSpectrum_tensor_coherent_coordinate_data
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
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) ∧
      (F.mapHomologicalComplex (.up ℤ)).map t.hom ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.restrictScalars.{u} eD.toRingHom ⋙ F)) (.up ℤ)).hom.app V0 ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom =
        (F.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso f f' g g' sq z P).hom ≫
          (ordinaryIsoPullbackStalkComplexIso j z0 Pg).hom ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) := by
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
  let D0 := C z0
  let Q := stalkComplex g' z P
  let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
  let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
  let H := affineSpectrumTensorAdditiveIso f f' g g' sq sq0 z0 P
  obtain ⟨eR, eA, eB, eD, q, hR, hB, hD, hgen⟩ :=
    exists_affineSpectrum_tensor_generator_coordinates f f' g g' sq sq0 z0 i P
  let V := tensorComplex f f' g g' sq z P
  let W := ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
    (.up ℤ)).obj V0
  have hH (k : ℤ) (d : C z) (x : Q.X k) :
      H.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
      eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
        (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x) :=
    hgen k d x
  have hsmul (k : ℤ) (r : C z) (v : V.X k) :
      H.hom.f k (r • v) = r • (show W.X k from H.hom.f k v) := by
    exact tensor_additive_smul
      ((tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
      ((tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
        (algebraMap A0 (A0 ⊗[R0] B0)))
      (Q.X k) (Q0.X k) eD.toRingHom (fun x => q.hom.f k x)
      (H.hom.f k) (hH k) r v
  let es (k : ℤ) : V.X k ≅ W.X k :=
    ModuleCat.isoMk (M := V.X k) (N := W.X k)
      (HomologicalComplex.Hom.isoApp H k) (fun r => by
      ext v
      exact (hsmul k r v).symm)
  let t : V ≅ W := HomologicalComplex.Hom.isoOfComponents (C₁ := V) (C₂ := W) es (by
    intro k l hkl
    ext v
    exact ConcreteCategory.congr_hom (H.hom.comm k l) v)
  refine ⟨eR, eA, eB, eD, q, t, hR, hB, hD, ?_, ?_⟩
  · exact hH
  · have ht : (F.mapHomologicalComplex (.up ℤ)).map t.hom ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.restrictScalars.{u} eD.toRingHom ⋙ F))
          (.up ℤ)).hom.app V0 = H.hom := by
      ext k v
      rfl
    rw [← Category.assoc, ht]
    simp only [H, affineSpectrumTensorAdditiveIso, ordinaryIsoPullbackStalkComplexIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_map, Category.comp_id]



end AlgebraicGeometry.SingleComplexBaseChange
