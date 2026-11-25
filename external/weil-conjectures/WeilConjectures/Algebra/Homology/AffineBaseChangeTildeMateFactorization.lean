/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization

/-! # AffineBaseChangeTildeMateFactorization

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-mate-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem mate_naturality_of_transformation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ⟶ L ⋙ Q) {Y Z : D} (k : Y ⟶ Z) :
    P.map (R.map k) ≫
        a'.homEquiv _ _ (e.app (R.obj Z) ≫ Q.map (a.counit.app Z)) =
      a'.homEquiv _ _ (e.app (R.obj Y) ≫ Q.map (a.counit.app Y)) ≫
        R'.map (Q.map k) := by
  rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_naturality_right]
  congr 1
  have hn := e.naturality (R.map k)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Q.map_comp]
  have hc := a.counit.naturality k
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]

private theorem affineMate_naturality
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) {K L : schemeDerivedCategory X} (k : K ⟶ L) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map k) ≫
      schemeDerivedBaseChangeMap f f' g p h L =
    schemeDerivedBaseChangeMap f f' g p h K ≫
      (schemeDerivedDirectImage f').map ((derivedPullback p).map k) := by
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  let adj := fun {A B : Scheme.{u}} (a : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction a
      (hAdd := (Classical.choose exists_derivedPullbackComposition) a)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) a)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) a))
  let q := c f' g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (c p f).symm
  have hn := mate_naturality_of_transformation (adj f) (adj f')
    (derivedPullback g) (derivedPullback p) q.hom k
  change (derivedPullback g).map ((schemeDerivedDirectImage f).map k) ≫
      (adj f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj L) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj L)) h.symm) ≫
          (c p f).inv.app ((schemeDerivedDirectImage f).obj L) ≫
          (derivedPullback p).map ((adj f).counit.app L)) =
      (adj f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
          (c p f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback p).map ((adj f).counit.app K)) ≫
        (schemeDerivedDirectImage f').map ((derivedPullback p).map k)
  simpa only [q, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj, Functor.comp_map,
    Functor.id_obj, Category.assoc] using hn

-- Explicit cohomology coordinates require additional definitional-equality work.
/-- The source tensor model transports the affine derived mate to the ordinary
coefficient map followed by the actual right-derived pushforward unit. This
contains no natural presentation of target cohomology and no global sections.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof and equation-bc;
more-algebra.tex, Tag 06Y6; cohomology.tex, Tag 08HY, derived mate construction.
(blueprint: lem-pc-affine-base-change-tilde-mate-factorization).

Proof: Resolve the restriction of M to R by a flat K-flat complex P. The universal
left-derived scalar extension and the counit in m identify its value with scalar
extension of P to R'. Exact tilde and the affine pullback tensor formula identify
this derived object with Lg* of the affine pushforward of Q(tilde M). The affine
acyclic pushforward calculation identifies the latter with Rf*K, using e. Take
cohomology and compose with m.cohomologyIso to obtain eC. Apply the pinned derived
base-change unit compatibility on the common K-flat span. The unit-normalized
tensor-pullback comparison identifies its ordinary exchange with the augmentation
followed termwise by the coefficient map from A tensor R' to A'. Apply homology:
m.comparison_eq supplies the augmentation factor, and exact restriction of scalars
supplies the mapHomologyIso factor in cE. The natural comparison for consecutive
restriction of scalars is rho; it is identity on carriers, so transporting through
hphi_f introduces exactly rho.inv. Transport the extended complex through hphi_g.
The remaining arrow is the termwise tilde/pushforward comparison followed by the
right-derived unit, which is the explicitly constructed cohomology map. Finally,
the inverse pullback counit and e identify its target with Lg'*K. Naturality and
cancellation of this counit yield the displayed factorization. The coefficient
map need not be invertible, and the square need only commute. P may be unbounded;
zero rings and zero complexes are included. -/
theorem exists_affineBaseChangeTildeMateFactorization
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
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
 :
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
  let K₀ := DerivedCategory.Q.obj
    (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
  have hK₀ : schemeDerivedQCohProperty (Spec (.of A)) K₀ := by
    intro n
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm) (hK n)
  obtain ⟨eC, heC⟩ := exists_affineBaseChangeTildeMateIdentityFactorization
    R A R' A' φg' φf' hφg' hφf' hw M hM hK₀ hc i
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
  let F := schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⋙
    derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))
  refine ⟨eC ≪≫ H.mapIso (F.mapIso e), ?_⟩
  dsimp only at heC ⊢
  have hn := congrArg (fun a ↦ H.map a) (affineMate_naturality
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom φf'))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom φg')) hw e.hom)
  simp only [Functor.map_comp] at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  dsimp only [F, Functor.comp_map]
  rw [hn, ← Category.assoc]
  erw [heC]
  simp only [Category.assoc]
  rw [← H.map_comp, ← Functor.map_comp,
    affineBaseChangeTildeRepresentativeIso_identity_hom]

end AlgebraicGeometry
