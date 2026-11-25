/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates

/-! # AffineBaseChangeTildeMateIdentityFactorization

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-mate-identity-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

private theorem homology_factorization
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {X Y U Z : C} {S S₁ S₂ : D} (κ : S ≅ H.obj X) (σ : X ≅ Y)
    (β : Y ⟶ Z) (r : X ⟶ U) (v : U ⟶ Z)
    (b₁ : S ⟶ S₁) (b₂ : S₁ ⟶ S₂) (b₃ : S₂ ⟶ H.obj U)
    (hσ : σ.hom ≫ β = r ≫ v)
    (hb : κ.hom ≫ H.map r = b₁ ≫ b₂ ≫ b₃) :
    (κ ≪≫ H.mapIso σ).hom ≫ H.map β = b₁ ≫ b₂ ≫ b₃ ≫ H.map v := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← H.map_comp, hσ, H.map_comp, ← Category.assoc, hb]
  simp only [Category.assoc]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Affine mate compatibility for the identity tilde representative.
Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-base-change-tilde-mate-identity-factorization).
Proof: Restrict M to R and choose a flat K-flat resolution P with a
quasi-isomorphism to that restriction. Scalar extension of P to R' computes the
universal left-derived scalar-extension functor in m. Its universal comparison
with the affine sheaf derived pullback, together with exact tilde and the affine
acyclic pushforward comparison, identifies its homology with H(Lg* Rf* Q(tilde M)).
Compose this comparison with m.cohomologyIso to obtain eC. This constructs eC
independently of A', and does not assert that any base-change map is invertible.

Use derivedBaseChange_unit_compatibility on the common resolution: after the
right-derived pushforward unit and the pullback counits, the pinned derived mate
is the termwise ordinary exchange. The unit-normalized tensor-pullback/tilde
comparison sends this exchange to scalar extension of the resolution augmentation
followed by the coefficient map A tensor_R R' to A'. Applying homology,
m.comparison_eq gives the augmentation factor; homology of ordinaryToLocalized
and exact restriction of scalars give the remaining two factors in cE.

The identity-on-carriers restriction-of-scalars comparison transports this arrow
along hφf', placing rho.inv after restrictScalars j applied to cE, exactly s.
Transport the extended complex through hφg'; its homology map is z₀. Exact tilde,
the termwise affine pushforward comparison, and the right-derived pushforward unit
then give affineTildePushforwardCohomologyMap. The inverse pullback counit and the
inverse tensor-pullback/tilde comparison give t for the identity representative.
Naturality of the derived units and cancellation of the supplied invertible
pullback counit identify the last factor with H(Rf'* t.hom). Reassociation yields
the displayed equality. Only commutativity of the square is used in this mate
calculation; no cartesian square or coefficient-map invertibility is needed.
All resolutions and homology comparisons apply to unbounded complexes. -/
theorem exists_affineBaseChangeTildeMateIdentityFactorization
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (hw : Spec.map (CommRingCat.ofHom φg') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom φf') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (hK : schemeDerivedQCohProperty (Spec (.of A))
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
 :
    let K := DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    let e := Iso.refl K
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    let α := algebraMap (A ⊗[R] R') A'
    let j : R' →+* A ⊗[R] R' := Algebra.TensorProduct.includeRight.toRingHom
    let T := tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] R')))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α φf' hφf'.symm
    let s := (ModuleCat.restrictScalars j).map cE ≫ ρ.inv.app (C.homology i)
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A') (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφg'] : C = Cg))
    let t := affineBaseChangeTildeRepresentativeIso A A' φg' K M e hc
    ∃ eC : T.obj ((ModuleCat.restrictScalars j).obj (m.cohomology i)) ≅
        H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eC.hom ≫ H.map (schemeDerivedBaseChangeMap
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf'))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) hw K) =
      T.map s ≫ T.map ((ModuleCat.restrictScalars φf').map z₀) ≫
        affineTildePushforwardCohomologyMap A' R' φf' Cg i ≫
        H.map ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map t.hom)
    := by
  set_option backward.isDefEq.respectTransparency true in
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    obtain ⟨σ, hσ⟩ := exists_affineTildeDerivedTensorMate
      R A R' A' M m φg' φf' hφg' hφf' hw hM hK hc
    let κ := affineTildeDerivedTensorSourceIso R A R' A' M m i
    refine ⟨κ ≪≫ H.mapIso σ, ?_⟩
    exact homology_factorization H κ σ _ _ _ _ _ _ hσ
      (affineTildeDerivedTensorToPushforward_homology
        R A R' A' M m φg' φf' hφg' hφf' i)

end AlgebraicGeometry
