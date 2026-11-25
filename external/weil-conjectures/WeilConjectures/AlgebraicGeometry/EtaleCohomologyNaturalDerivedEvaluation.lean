/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB

import Mathlib.CategoryTheory.Abelian.Injective.Ext
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Constant-integer Ext in the standard large model computes terminal evaluation,
naturally in the coefficient sheaf.
Source: Stacks Project, Tags 01FT and 06XP, Lemma 13.27.2(1).
(blueprint: new-etale-cohomology-natural-derived-evaluation)

Proof: The constant-sheaf adjunction at the terminal object V identifies Hom from
the constant lifted integer sheaf to F with F(V), by evaluation at 1. This is an
additive identification, natural in F. On a chosen injective resolution of F it
identifies the Hom complex with the terminal-section complex, after lifting the
latter to the universe of the standard Ext model. Ext is the homology of the Hom
complex; the right-derived evaluation is the homology of the section complex.
The exact additive universe-lift functor preserves homology, so its homology may
be unlifted. Compose these three identifications for each F and n. A morphism
F -> G lifts to a chain map between their chosen injective resolutions. The
Hom-to-sections identification commutes degreewise with this chain map; both the
Ext computation and the right-derived computation are natural for the lift.
Consequently the composite equivalences satisfy the displayed equation. Different
lifts are homotopic and have the same homology map. The construction uses a fixed
comparison, rather than asserting naturality of arbitrary additive equivalences.
For the zero sheaf and for the empty scheme in positive degree both groups are
zero; the same argument applies without any nonemptiness assumption. -/
theorem etaleCohomologyNaturalDerivedEvaluation
    (X : Scheme.{u}) (V : X.Etale) (hV : IsTerminal V) :
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
    ∃ e : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ),
        @Sheaf.H _ _ X.smallEtaleTopology F inferInstance (HasExt.standard _) (n + 1) ≃+
          ((E.rightDerived (n + 1)).obj F),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (φ : F ⟶ G) (n : ℕ)
        (x : @Sheaf.H _ _ X.smallEtaleTopology F inferInstance
          (HasExt.standard _) (n + 1)),
        e G n (@Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
          _ _ φ (n + 1) x) = (E.rightDerived (n + 1)).map φ (e F n x)  := by
  -- Construct the comparison from the same injective resolution on both sides.
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let U := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    Sheaf.integerSheaf.{u} X.smallEtaleTopology
  let S := (CochainComplex.singleFunctor _ 0).obj A
  let c := Sheaf.complexEvaluationIso.{u} X.smallEtaleTopology V hV
  -- The constant-sheaf evaluation isomorphism commutes with every chain map.
  have hc {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ}
      (f : K ⟶ L) :
      EtaleComparisonAux.postMap S f ≫ (c L).hom =
        (c K).hom ≫ ((E ⋙ U).mapHomologicalComplex _).map f := by
    ext n a
    obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
      a n (zero_add n)
    change ULift.up (Sheaf.evaluationEquiv X.smallEtaleTopology V hV (L.X n)
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n))
        ((CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)).comp
          (.ofHom f) (add_zero n)))) =
      ULift.up ((f.f n).hom.app (op V)
        (Sheaf.evaluationEquiv X.smallEtaleTopology V hV (K.X n)
          ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n))
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)))))
    rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
    simp only [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    exact congrArg ULift.up
      (Sheaf.evaluationEquiv_naturality X.smallEtaleTopology V hV (f.f n) a)
  let d (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (n : ℤ) :=
    (CochainComplex.HomComplex.leftHomologyData S K n).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso (c K)
  have hd {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ}
      (f : K ⟶ L) (n : ℤ) :
      AddCommGrpCat.ofHom (EtaleComparisonAux.postClass (S := S) f n) ≫ (d L n).hom =
        (d K n).hom ≫ HomologicalComplex.homologyMap
          (((E ⋙ U).mapHomologicalComplex _).map f) n := by
    have h := EtaleComparisonAux.homologyClass_naturality (S := S) f n
    have h' := congrArg ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map)
      (hc f)
    simp only [HomologicalComplex.homologyFunctor_map,
      HomologicalComplex.homologyMap_comp] at h'
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← cancel_epi (CochainComplex.HomComplex.leftHomologyData S K n).homologyIso.hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    erw [← reassoc_of% h, Iso.hom_inv_id_assoc]
    exact h'
  let := HasExt.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
  let e (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
      AddCommGrpCat.of (@Sheaf.H _ _ X.smallEtaleTopology F inferInstance
        (HasExt.standard _) n) ≅ U.obj ((E.rightDerived n).obj F) :=
    ((injectiveResolution F).extAddEquivCohomologyClass (X := A) (n := n)).toAddCommGrpIso ≪≫
      d (injectiveResolution F).cochainComplex n ≪≫
      (((E.mapHomologicalComplex (.up ℤ)).obj
        (injectiveResolution F).cochainComplex).sc (n : ℤ)).mapHomologyIso U ≪≫
      U.mapIso ((injectiveResolution F).isoRightDerivedObjCochainComplex E n).symm
  -- Ext, homology preservation, and right-derived evaluation use the same lift.
  have he {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
      (Abelian.extFunctorObj A n).map f ≫ (e G n).hom =
        (e F n).hom ≫ U.map ((E.rightDerived n).map f) := by
    let φ : (injectiveResolution F).Hom (injectiveResolution G) f :=
      ⟨InjectiveResolution.desc f _ _, by simp [InjectiveResolution.desc_commutes_zero]⟩
    have hext : (Abelian.extFunctorObj A n).map f ≫
        (injectiveResolution G).extAddEquivCohomologyClass.toAddCommGrpIso.hom =
      (injectiveResolution F).extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        AddCommGrpCat.ofHom (EtaleComparisonAux.postClass (S := S) φ.hom' (n : ℤ)) := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      change (injectiveResolution G).extAddEquivCohomologyClass
          (a.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
        EtaleComparisonAux.postClass φ.hom' (n : ℤ)
          ((injectiveResolution F).extAddEquivCohomologyClass a)
      exact (EtaleComparisonAux.extClass_naturality f _ _ φ n a).symm
    have hclass := hd φ.hom' (n : ℤ)
    have hu := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ (n : ℤ)).map
        ((E.mapHomologicalComplex _).map φ.hom')) U
    have hr := congrArg (fun a ↦ U.map a)
      ((injectiveResolution F).isoRightDerivedObjCochainComplex_inv_naturality φ E n)
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [reassoc_of% hext, reassoc_of% hclass]
    erw [reassoc_of% hu]
    simp only [Functor.map_comp] at hr
    erw [← Category.assoc, hr]
    simp only [Category.assoc]
  refine ⟨fun F n ↦ (e F (n + 1)).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift, ?_⟩
  intro F G f n x
  have h := ConcreteCategory.congr_hom (he f (n + 1)) x
  change (e G (n + 1)).hom ((Sheaf.H.map f (n + 1)) x) =
    U.map ((E.rightDerived (n + 1)).map f) ((e F (n + 1)).hom x) at h
  change ULift.down ((e G (n + 1)).hom ((Sheaf.H.map f (n + 1)) x)) =
    (E.rightDerived (n + 1)).map f (ULift.down ((e F (n + 1)).hom x))
  exact congrArg ULift.down h

end AlgebraicGeometry.Scheme.Modules
