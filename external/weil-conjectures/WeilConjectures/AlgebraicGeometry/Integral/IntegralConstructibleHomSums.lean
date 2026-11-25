/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleBoundedBelowCompactness
import WeilConjectures.AlgebraicGeometry.Adic.AdicGlobalDerivedHom
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Shifted Hom from integral constructible complexes and countable sums

We use the completed coefficient presentation of the integral category. The scalar
ring is its recorded `ULift` of the valuation ring, canonically ring-isomorphic to
that valuation ring. A colimit cofan supplies the ambient derived coproduct and its
coprojections without choosing a second coproduct object.

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12
* Bhatt--Scholze, Lemma 6.8.12
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def evaluationHomEquiv (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : pbcModules X (pbcAdicCompletion X d)) :
    (SheafOfModules.unit ((adicLisseForget X).obj (pbcAdicCompletion X d)) ⟶ M) ≃+
      ((adicGlobalSections X d).obj M) where
  toFun f := f.val.app (Opposite.op (⊤_ X.ProEt))
    (1 : (pbcAdicCompletion X d).obj.obj (Opposite.op (⊤_ X.ProEt)))
  invFun x := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map ((terminalIsTerminal (C := X.ProEt)).op.to U) x)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      exact M.val.congr_map_apply
        ((terminalIsTerminal (C := X.ProEt)).op.hom_ext _ _) x))
  left_inv f := by
    apply M.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    change M.val.map _ (f.val.app _
      (1 : (pbcAdicCompletion X d).obj.obj (Opposite.op (⊤_ X.ProEt)))) =
        f.val.app U (1 : (pbcAdicCompletion X d).obj.obj U)
    rw [← PresheafOfModules.naturality_apply]
    change f.val.app U ((pbcAdicCompletion X d).obj.map _ 1) =
      f.val.app U (1 : (pbcAdicCompletion X d).obj.obj U)
    rw [map_one]
  right_inv x := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val _ = x
    rw [Equiv.apply_symm_apply]
    change M.val.map _ x = x
    have h : (terminalIsTerminal (C := X.ProEt)).op.to
        (Opposite.op (⊤_ X.ProEt)) = 𝟙 _ :=
      (terminalIsTerminal (C := X.ProEt)).op.hom_ext _ _
    rw [h]
    simp
  map_add' f g := rfl

private def evaluationHomIso (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    preadditiveCoyoneda.obj
        (Opposite.op (SheafOfModules.unit
          ((adicLisseForget X).obj (pbcAdicCompletion X d)))) ≅
      adicGlobalSections X d ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun M ↦ (evaluationHomEquiv X d M).toAddCommGrpIso) (by
    intro M N f
    ext x
    rfl)

open SheafOfModules in
private theorem cohomologyHomEquiv (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived X d) :
    ∃ e : ∀ N : PbcCompletedDerived X d,
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0).obj
          ((adicGlobalRHom X d K).obj N)) ≃+ (K ⟶ N),
      ∀ (N N' : PbcCompletedDerived X d) (f : N ⟶ N')
        (x : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0).obj
          ((adicGlobalRHom X d K).obj N)),
        e N' ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0).map
          ((adicGlobalRHom X d K).map f) x) = e N x ≫ f := by
  let R := pbcAdicCompletion X d
  let : IsGrothendieckAbelian.{u + 1} (pbcModules X R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology X) R).1
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfSize.{0, 0} V :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} (R := A)
  let : PreservesFiniteColimits V := PreservesColimitsOfSize.preservesFiniteColimits V
  let F := adicGlobalSections X d
  let Γ := preadditiveCoyoneda.obj
    (Opposite.op (SheafOfModules.unit ((adicLisseForget X).obj R)))
  let b : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅ Γ.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (C := pbcModules X R) (D := ModuleCat.{u + 1} A)
      (E := AddCommGrpCat.{u + 1}) F V).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (C := pbcModules X R) (D := AddCommGrpCat.{u + 1}) (evaluationHomIso X d).symm
  let c : F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0 ⋙ V ≅
      Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0 :=
    Functor.isoWhiskerLeft F.rightDerivedFunctor (Functor.mapDerivedCategoryHomologyFunctorIso
      (C := ModuleCat.{u + 1} A) (D := AddCommGrpCat.{u + 1}) V 0) ≪≫
      Functor.isoWhiskerRight b (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
  let H := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{u + 1, u, u + 1} (ProEt.topology X) R)).obj (Opposite.op K)
  let t := Functor.isoWhiskerLeft H c
  obtain ⟨e, he⟩ := rhom_global_sectionsOfUniverses.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X) R
  refine ⟨fun N ↦ (t.app N).addCommGroupIsoToAddEquiv.trans (e (Opposite.op K, N)), ?_⟩
  intro N N' f x
  have ht := ConcreteCategory.congr_hom (t.hom.naturality f) x
  change (t.app N').hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0).map
        ((adicGlobalRHom X d K).map f) x) =
    (ringedSiteZerothHypercohomologyOfUniverses.{u + 1, u, u + 1, u + 2}
      (ProEt.topology X) R).map
        ((derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
          (ProEt.topology X) R).map (𝟙 (Opposite.op K), f)) ((t.app N).hom x) at ht
  exact (congrArg (e (Opposite.op K, N')) ht).trans (by
    change e (Opposite.op K, N') _ = e (Opposite.op K, N) ((t.app N).hom x) ≫ f
    simpa only [unop_id, Category.id_comp] using he (Opposite.op K, N) (Opposite.op K, N')
      (𝟙 (Opposite.op K), f) ((t.app N).hom x))

open Classical in
/-- The canonical map from the direct sum of shifted Hom modules is bijective,
and hence is an isomorphism of modules over the integral coefficient ring.
Its component at `i` is postcomposition with the shifted coprojection `s.inj i`.
The countable family may be empty and its common lower bound may be any integer.
The source belongs to the recorded bounded constructible complete category, using
the canonical continuous-coefficient/completed-coefficient identification. -/
theorem integralConstructible_hom_sums
    (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hdim : ∃ N : ℕ, topologicalKrullDim X ≤ (N : WithBot ℕ∞))
    (hℓ : ∀ x : X, IsUnit (ℓ : X.presheaf.stalk x))
    (K : PbcIntegralCategory ℓ E X hdim hℓ)
    (I : Type (u + 1)) [Countable I]
    (M : I → PbcCompletedDerived X (pbcIntegralDatum ℓ E))
    (_hM : ∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n)
    (q : ℤ) (s : Cofan M) (_hs : IsColimit s) :
    Function.Bijective
      (DirectSum.toModule (PbcIntegralRing ℓ E) I (K.obj ⟶ s.pt⟦q⟧)
        (fun i : I ↦ Linear.rightComp (PbcIntegralRing ℓ E) K.obj
          ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum ℓ E)) q).map
            (s.inj i)))) := by
  let A := PbcIntegralRing ℓ E
  let d := pbcIntegralDatum ℓ E
  let D := PbcCompletedDerived X d
  let S := shiftFunctor D q
  let M' : I → D := fun i ↦ S.obj (M i)
  let s' : Cofan M' := Cofan.mk (S.obj s.pt) (fun i ↦ S.map (s.inj i))
  have hs' : IsColimit s' :=
    (isColimitMapCoconeCofanMkEquiv S M s.inj).1 (isColimitOfPreserves S _hs)
  have hM' : ∃ n : ℤ, ∀ i, DerivedCategory.IsGE (M' i) n := by
    obtain ⟨n, hn⟩ := _hM
    refine ⟨n - q, fun i ↦ ?_⟩
    have : DerivedCategory.IsGE (M i) n := hn i
    exact DerivedCategory.TStructure.t.isGE_shift (M i) n q (n - q) (by omega)
  let G := adicGlobalRHom X d K.obj
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let t := Cofan.mk (∐ (fun i ↦ G.obj (M' i))) (Sigma.ι _)
  let ht := coproductIsCoproduct (fun i ↦ G.obj (M' i))
  have hcomp := integralConstructible_boundedBelow_compactness
    X ℓ E hdim hℓ K I M' hM' s' hs' t ht
  have hG : IsColimit (Cofan.mk (G.obj s'.pt) (fun i ↦ G.map (s'.inj i))) :=
    ((ht.nonempty_isColimit_iff_isIso_desc).mpr hcomp).some
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0
  have hH := (AlgebraicGeometry.derivedModuleHomology_coproduct A 0 I
    (fun i ↦ G.obj (M' i)) (G.obj s'.pt) (fun i ↦ G.map (s'.inj i)) hG).some
  let V := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  have hGH : IsColimit ((G ⋙ H).mapCocone s') :=
    (isColimitMapCoconeCofanMkEquiv (G ⋙ H) M' s'.inj).symm hH
  have hV : IsColimit ((G ⋙ H ⋙ V).mapCocone s') := isColimitOfPreserves V hGH
  let U := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  have hU : IsColimit ((G ⋙ H ⋙ V ⋙ U).mapCocone s') := isColimitOfPreserves U hV
  obtain ⟨e, he⟩ := cohomologyHomEquiv X d K.obj
  let P := preadditiveCoyoneda.obj (Opposite.op K.obj)
  let a : G ⋙ H ⋙ V ⋙ U ≅ P :=
    NatIso.ofComponents (fun N ↦ (AddEquiv.ulift.trans (e N)).toAddCommGrpIso) (by
      intro N N' f
      ext x
      exact he N N' f x.down)
  have hP : IsColimit (P.mapCocone s') := IsColimit.mapCoconeEquiv a hU
  let W := forget₂ (ModuleCat.{u + 2} A) AddCommGrpCat.{u + 2}
  let Z : I → ModuleCat.{u + 2} A := fun i ↦ ModuleCat.of A (K.obj ⟶ M' i)
  let c : Cofan Z := Cofan.mk (ModuleCat.of A (K.obj ⟶ s'.pt))
    (fun i ↦ ModuleCat.ofHom (Linear.rightComp A K.obj (s'.inj i)))
  have hcV : IsColimit (W.mapCocone c) := by
    exact (isColimitMapCoconeCofanMkEquiv W Z c.inj).symm
      ((isColimitMapCoconeCofanMkEquiv P M' s'.inj).1 hP)
  have hc : IsColimit c := isColimitOfReflects W hcV
  let hZ := ModuleCat.coproductCoconeIsColimit.{u + 1, u + 1, u + 2} Z
  have hdesc : IsIso (hZ.desc c) :=
    (hZ.nonempty_isColimit_iff_isIso_desc).mp ⟨hc⟩
  exact (ConcreteCategory.isIso_iff_bijective (hZ.desc c)).mp hdesc

end AlgebraicGeometry.Scheme
