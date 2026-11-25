/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap

/-! # Functorial base-derived tensor cohomology

Source: Stacks Project, Tags 06Y6 and 0BYJ.
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- The ordinary derived counit is a natural transformation with its tensor-algebra action.

Source: Stacks Project, Tag 06Y6 (derived extension and universal counit), and
Tag 0BYJ (functorial tensor associativity).

Proof: use exists_baseDerivedTensorCohomologyModelMap to obtain the E-linear map
on the cohomology of the canonical models for each chain map. The universal
property of the target model forces the supplied derived natural transformation
to be the canonical leftDerivedNatTrans induced by the identity. Faithful
restriction to B and cancellation of cohomologyIso prove uniqueness of the
E-linear map. Choose these uniquely determined maps. The identity and composition
laws for leftDerivedNatTrans, its naturality, and the corresponding laws of
homology give the functor laws after faithful restriction. Its objects are the
canonical model cohomology objects themselves, so e is the identity isomorphism.
Exact restriction sends quasi-isomorphisms to quasi-isomorphisms; localization,
derived extension, and homology then give isomorphisms. The canonical derived
comparison is also an isomorphism. The model-map equation and faithful
restriction prove that H inverts quasi-isomorphisms.
To prove naturality of the ordinary comparison, first check ordinaryIso
naturality on generators 1 tensor p and extend by tensor induction. Restrict
the desired cohomology square to B and compose with the inverse exact-restriction
homology isomorphism. Substitute comparison_eq and the model-map equation.
Counit compatibility, counit naturality, the two homology factorization
naturality squares, and the generator square prove the equality. This constructs
sigma with its actual model.comparison components. No extension to C, tensor
with a second complex, or localized comparison is constructed here. Zero rings,
zero complexes, identity maps and unbounded complexes use the same argument.
(blueprint: lem-pc-base-tensor-cohomology-functor). -/
theorem exists_baseTensorCohomologyFunctor (i : ℤ) :
    let m := fun P : CochainComplex (ModuleCat.{u} A) ℤ ↦
      baseDerivedTensorCohomologyModel R A B P C
    let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    ∃ (H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (σ : H ⟶ E ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
        (.up ℤ) i)
      (e : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ, (m P).cohomology i ≅ H.obj P),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).IsInvertedBy H ∧
      ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (e P).hom ≫ σ.app P = (m P).comparison i  := by
  classical
  dsimp only
  let m := fun P : CochainComplex (ModuleCat.{u} A) ℤ ↦
    baseDerivedTensorCohomologyModel R A B P C
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let G := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
    HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let K := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let c (P P' : CochainComplex (ModuleCat.{u} A) ℤ) : (m P).derived ⟶ (m P').derived :=
    let := (m P').universal
    Functor.leftDerivedNatTrans (m P).derived (m P').derived
      (m P).counit (m P').counit W (𝟙 _)
  have cid (P : CochainComplex (ModuleCat.{u} A) ℤ) : c P P = 𝟙 _ := by
    let := (m P).universal
    exact Functor.leftDerivedNatTrans_id _ _ W
  have ccomp (P P' P'' : CochainComplex (ModuleCat.{u} A) ℤ) :
      c P P' ≫ c P' P'' = c P P'' := by
    let := (m P').universal
    let := (m P'').universal
    simpa only [Category.id_comp] using
      Functor.leftDerivedNatTrans_comp (m P).derived (m P').derived (m P'').derived
        (m P).counit (m P').counit (m P'').counit W (𝟙 _) (𝟙 _)
  have hciso (P P' : CochainComplex (ModuleCat.{u} A) ℤ) : IsIso (c P P') := by
    let := (m P).universal
    let := (m P').universal
    change IsIso (Functor.leftDerivedNatIso (m P).derived (m P').derived
      (m P).counit (m P').counit W (Iso.refl _)).hom
    infer_instance
  have exists_map (P P' : CochainComplex (ModuleCat.{u} A) ℤ) (f : P ⟶ P') :
      ∃! g : (m P).cohomology i ⟶ (m P').cohomology i,
        G.map g ≫ ((m P').cohomologyIso i).hom =
          ((m P).cohomologyIso i).hom ≫ K.map ((m P).derived.map (F.map f)) ≫
            K.map ((c P P').app (F.obj P')) := by
    obtain ⟨δ, g, hδ, hg⟩ :=
      RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
        R A B C P P' f (m P) (m P') i
    have hd : δ = c P P' := by
      let := (m P').universal
      apply Functor.leftDerived_ext (m P').derived (m P').counit W (m P).derived
      rw [hδ]
      simp [c, Functor.leftDerivedNatTrans_fac]
    rw [hd] at hg
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    apply G.map_injective
    apply (cancel_mono ((m P').cohomologyIso i).hom).1
    exact hg'.trans hg.symm
  choose g hg using fun P P' f ↦ (exists_map P P' f).exists
  let H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B) :=
    { obj := fun P ↦ (m P).cohomology i
      map := fun f ↦ g _ _ f
      map_id := by
        intro P
        apply G.map_injective
        apply (cancel_mono ((m P).cohomologyIso i).hom).1
        rw [hg, cid]
        erw [F.map_id, (m P).derived.map_id, K.map_id, G.map_id]
        dsimp only [F, Functor.comp_obj]
        erw [Category.comp_id]
      map_comp := by
        intro P P' P'' f f'
        apply G.map_injective
        apply (cancel_mono ((m P'').cohomologyIso i).hom).1
        rw [Functor.map_comp, Category.assoc, hg P P'' (f ≫ f'), hg P' P'' f',
          reassoc_of% hg P P' f]
        have hn := congrArg K.map ((c P P').naturality (F.map f'))
        simp only [Functor.map_comp] at hn
        rw [← reassoc_of% hn]
        rw [← K.map_comp ((c P P').app (F.obj P'')) ((c P' P'').app (F.obj P''))]
        rw [← NatTrans.comp_app, ccomp]
        simp only [Functor.map_comp, Category.assoc] }
  have hinv : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).IsInvertedBy H := by
    intro P P' f hf
    have hfR : QuasiIso
        (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f) := by
      have : QuasiIso f := hf
      infer_instance
    have hfD : IsIso (F.map f) := by
      exact (DerivedCategory.isIso_Qh_map_iff _).2
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hfR)
    have := hciso P P'
    have hh : IsIso (G.map (g P P' f) ≫ ((m P').cohomologyIso i).hom) := by
      rw [hg]
      infer_instance
    have : IsIso (G.map (H.map f)) := (isIso_comp_right_iff _ _).mp hh
    exact isIso_of_reflects_iso (H.map f) G
  let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let σ : H ⟶ E ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
      (.up ℤ) i :=
    { app := fun P ↦ (m P).comparison i
      naturality := by
        intro P P' f
        let r := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
        let b := (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)
        let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
        let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
        let s := r.map f
        let v := b.map s
        let u := E.map f
        have ho : v ≫ (m P').ordinaryIso.hom =
            (m P).ordinaryIso.hom ≫ (G.mapHomologicalComplex (.up ℤ)).map u := by
          apply HomologicalComplex.Hom.ext
          funext j
          apply ExtendScalars.hom_ext
          intro p
          let p' : P.X j := p
          have hv : v.f j ((1 : B) ⊗ₜ[R, algebraMap R B] p') =
              (1 : B) ⊗ₜ[R, algebraMap R B]
                (show (r.obj P').X j from f.f j p') := by
            exact ExtendScalars.map_tmul (algebraMap R B) ((r.map f).f j) 1 p'
          change (m P').ordinaryIso.hom.f j
              (v.f j ((1 : B) ⊗ₜ[R, algebraMap R B] p')) =
            ((G.mapHomologicalComplex (.up ℤ)).map u).f j
              ((m P).ordinaryIso.hom.f j ((1 : B) ⊗ₜ[R, algebraMap R B] p'))
          rw [hv]
          erw [(m P').ordinaryIso_tmul, (m P).ordinaryIso_tmul]
          exact (ExtendScalars.map_tmul (algebraMap A (A ⊗[R] B)) (f.f j)
            (Algebra.TensorProduct.includeRight 1) p').symm
        have h0 : (c P P').app (F.obj P') ≫ (m P').counit.app (πR.obj (r.obj P')) =
            (m P).counit.app (πR.obj (r.obj P')) := by
          let := (m P').universal
          dsimp only [c, F, Functor.comp_obj]
          simpa only [NatTrans.id_app, Category.comp_id] using
            Functor.leftDerivedNatTrans_app (m P).derived (m P').derived
              (m P).counit (m P').counit W (𝟙 _) (πR.obj (r.obj P'))
        have h0' := congrArg K.map h0
        have h1 := congrArg K.map ((m P).counit.naturality (πR.map s))
        have h2 := (DerivedCategory.homologyFunctorFactorsh
          (ModuleCat.{u} B) i).hom.naturality (πB.map v)
        have h3 := (HomotopyCategory.homologyFunctorFactors
          (ModuleCat.{u} B) (.up ℤ) i).hom.naturality v
        have h4 := congrArg (fun z ↦ HomologicalComplex.homologyMap z i) ho
        have h5 := ShortComplex.mapHomologyIso_inv_naturality
          ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map u) G
        dsimp only [Functor.comp_map] at h1 h2 h3
        simp only [Functor.map_comp] at h0' h1
        simp only [HomologicalComplex.homologyMap_comp] at h4
        change G.map (HomologicalComplex.homologyMap u i) ≫
            ((E.obj P').sc i |>.mapHomologyIso G).inv =
          ((E.obj P).sc i |>.mapHomologyIso G).inv ≫
            HomologicalComplex.homologyMap
              ((G.mapHomologicalComplex (.up ℤ)).map u) i at h5
        apply G.map_injective
        apply (cancel_mono ((E.obj P').sc i |>.mapHomologyIso G).inv).1
        change G.map (g P P' f ≫ (m P').comparison i) ≫ _ =
          G.map ((m P).comparison i ≫ HomologicalComplex.homologyMap u i) ≫ _
        simp only [Functor.map_comp, Category.assoc]
        rw [(m P').comparison_eq i]
        erw [reassoc_of% hg P P' f]
        rw [h5]
        erw [← Category.assoc (G.map ((m P).comparison i)), (m P).comparison_eq i]
        erw [reassoc_of% h0', reassoc_of% h1, reassoc_of% h2,
          reassoc_of% h3]
        exact congrArg (fun z ↦ ((m P).cohomologyIso i).hom ≫
          K.map ((m P).counit.app (πR.obj (r.obj P))) ≫
          (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
            (πB.obj (b.obj (r.obj P))) ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
            (b.obj (r.obj P)) ≫ z) h4 }
  exact ⟨H, σ, fun P ↦ Iso.refl _, hinv, fun P ↦ Category.id_comp _⟩


end ModuleCat
