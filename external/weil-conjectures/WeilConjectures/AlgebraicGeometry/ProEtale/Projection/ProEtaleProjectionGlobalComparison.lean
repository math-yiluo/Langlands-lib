/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.CategoryTheory.Projection.ProjectionMateSquareCoherence
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorComparisonTransport

/-!
# Comparing the native and canonical global projection mates

## References

* Stacks Project, Tags 06YU, 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits
private theorem compareProjectionMates
    {A B : Type*} [Category A] [Category B]
    {F K : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (adj' : K ⊣ S)
    (T V : A × A ⥤ A) (U W : B × B ⥤ B)
    (alpha : T ⋙ F ≅ (F.prod F) ⋙ U) (beta : V ⋙ K ≅ (K.prod K) ⋙ W)
    (a : T ≅ V) (b : U ≅ W) (l : K ≅ F)
    (hc : ∀ P Q : A,
      l.hom.app (T.obj (P, Q)) ≫ alpha.hom.app (P, Q) ≫ b.hom.app (F.obj P, F.obj Q) =
        K.map (a.hom.app (P, Q)) ≫ beta.hom.app (P, Q) ≫
          W.map (Prod.mkHom (l.hom.app P) (l.hom.app Q))) (E : B) :
    ∃ s : (Functor.curryObj T).obj (R.obj E) ≅ (Functor.curryObj V).obj (S.obj E),
    ∃ t : F ⋙ (Functor.curryObj U).obj E ⋙ R ≅ K ⋙ (Functor.curryObj W).obj E ⋙ S,
    ∀ P : A,
      derivedProjectionFormulaMate F R adj T U alpha E P ≫ t.hom.app P =
        s.hom.app P ≫ derivedProjectionFormulaMate K S adj' V W beta E P := by
  let r := conjugateIsoEquiv adj adj' l
  let s := ((Functor.curry.mapIso a).app (R.obj E)) ≪≫
    (Functor.curryObj V).mapIso (r.app E)
  let t := Functor.isoWhiskerLeft (F ⋙ (Functor.curryObj U).obj E) r ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F ((Functor.curry.mapIso b).app E)) S ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight l.symm ((Functor.curryObj W).obj E)) S
  refine ⟨s, t, ?_⟩
  intro P
  have h := projectionMate_square_of_tensor_coherence_projection
    (G := 𝟭 A) (H := 𝟭 B) adj adj' T U V W alpha a.hom b.hom beta
    ((Functor.leftUnitor K) ≪≫ l ≪≫ (Functor.rightUnitor F).symm)
    (by intro M N; simpa using hc M N) E P
  simpa [s, t, r, conjugateIsoEquiv, conjugateEquiv, Functor.curryObj,
    Functor.curry, Category.assoc] using h

private theorem ordinaryTransport_square
    {A B : Type*} [Category A] [Category B] {K F : A ⥤ B}
    (e : K ≅ F) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (mu : ∀ M N : A, F.obj ((T.obj M).obj N) ≅ (U.obj (F.obj M)).obj (F.obj N))
    (M N : A) :
    e.hom.app ((T.obj M).obj N) ≫ (mu M N).hom =
      (e.app _ ≪≫ mu M N ≪≫ ((U.mapIso (e.app M).symm).app _) ≪≫
        (U.obj (K.obj M)).mapIso (e.app N).symm).hom ≫
        (U.map (e.hom.app M)).app (K.obj N) ≫
          (U.obj (F.obj M)).map (e.hom.app N) := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Iso.app_inv, Category.assoc]
  rw [NatTrans.naturality_assoc]
  simp [← Functor.map_comp]

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  Operation.left proEtaleRingDerivedPullbackFactors proEtaleCanonicalTensorComparison
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf SheafOfModules.monoidalCategory
  proEtaleOrdinaryTensorPullback

private theorem tensorModelIso
    {Z : Scheme.{u}} {T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel Z T) (b : TensorModel T) :
    ∃ e : a.tensor ≅ b.functor,
      Functor.isoWhiskerLeft
        (((resolving T).ι ⋙ DerivedCategory.Q).prod
          ((resolving T).ι ⋙ DerivedCategory.Q)) e =
        a.representative.symm ≪≫ b.representative := by
  let K := (((resolving T).ι ⋙ DerivedCategory.Q).prod
    ((resolving T).ι ⋙ DerivedCategory.Q))
  let W := (Functor.whiskeringLeft _ _ (Der T)).obj K
  let : W.Full := ⟨fun {F G} ↦ (b.descent F G).2⟩
  let : W.Faithful := ⟨fun {F G} ↦ (b.descent F G).1⟩
  let ff := Functor.FullyFaithful.ofFullyFaithful W
  exact ⟨ff.preimageIso (a.representative.symm ≪≫ b.representative), by
    simp only [Functor.isoWhiskerLeft]
    exact ff.isoEquiv.apply_symm_apply _⟩

private theorem operation_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (o : Operation (proEtaleBaseChange f) R S)
    (ho : o.coefficient =
      ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩) :
    o = globalOperation f R S c := by
  cases o
  unfold globalOperation
  congr 1

private theorem ordinaryTensor_unique
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (o : Operation (proEtaleBaseChange f) R S) (a b : o.OrdinaryTensor) : a = b := by
  have h : a.iso = b.iso := by
    funext M N
    apply Iso.ext
    apply (o.moduleAdjunction.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply SheafOfModules.CochainScalarConstruction.pure_hom_ext R M N
    intro W x y
    exact (a.pure_unit M N W x y).trans (b.pure_unit M N W x y).symm
  cases a
  cases b
  cases h
  rfl

private theorem globalOrdinary_square
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M N : Mod R) :
    let o := globalOperation f R S c
    let e := o.moduleAdjunction.leftAdjointUniq (proEtaleRingModuleAdjunction f R S c)
    e.hom.app (((tensor R).obj M).obj N) ≫
        (proEtaleOrdinaryTensorPullback f R S c M N).hom =
      ((globalOrdinaryTensor f R S c).iso M N).hom ≫
        (((tensor S).map (e.hom.app M)).app (o.pullback.obj N) ≫
          ((tensor S).obj ((proEtaleRingModulePullback f R S c).obj M)).map
            (e.hom.app N)) := by
  exact ordinaryTransport_square
    ((globalOperation f R S c).moduleAdjunction.leftAdjointUniq
      (proEtaleRingModuleAdjunction f R S c)) (tensor R) (tensor S)
    (proEtaleOrdinaryTensorPullback f R S c) M N

/-- Comparing normalized global models does not involve a slice or exactness data. -/
theorem proEtaleProjectionGlobalComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (g : Global f R S c) (E : DerivedCategory (proEtaleRingModules X S)) :
    ∃ s : (Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E) ≅
      (Functor.curryObj g.tensorY.functor).obj (g.operation.right.obj E),
    ∃ t : (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c) ≅
      (g.operation.left ⋙ (Functor.curryObj g.tensorX.functor).obj E ⋙ g.operation.right),
    ∀ P : Der R,
      proEtaleProjectionFormulaMate f R S c a b E P ≫ t.hom.app P =
        s.hom.app P ≫ derivedProjectionFormulaMate g.operation.left g.operation.right
          g.operation.derivedAdjunction g.tensorY.functor g.tensorX.functor
          g.tensorComparison.comparison E P := by
  classical
  rcases g with ⟨o, hcoeff, hpush, adj, ay, bx, say, sbx, mu, tc, htc⟩
  have ho := operation_eq f R S c o hcoeff
  subst o
  have hmu := ordinaryTensor_unique (globalOperation f R S c) mu
    (globalOrdinaryTensor f R S c)
  subst mu
  obtain ⟨ea, ha⟩ := tensorModelIso a ay
  obtain ⟨eb, hb⟩ := tensorModelIso b bx
  let e := (globalOperation f R S c).moduleAdjunction.leftAdjointUniq
    (proEtaleRingModuleAdjunction f R S c)
  exact compareProjectionMates (proEtaleRingDerivedAdjunction f R S c)
    (globalOperation f R S c).derivedAdjunction a.tensor ay.functor b.tensor bx.functor
    (proEtaleCanonicalTensorComparison f R S c a b) tc.comparison ea eb
    (Functor.mapDerivedCategoryNatIso e)
    (proEtaleTensorComparisonTransport f R S c (globalOperation f R S c).pullback e
      (globalOperation f R S c).leftModel (Functor.mapDerivedCategoryNatIso e)
      (fun C ↦ Functor.mapDerivedCategoryNatIso_fac e C) a b ay bx
      (globalOrdinaryTensor f R S c).iso tc (globalOrdinary_square f R S c) ea eb ha hb) E

end AlgebraicGeometry.Scheme
