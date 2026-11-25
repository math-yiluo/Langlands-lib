/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Ordinary counit transport of base-derived tensor models

Source: Stacks Project, More on Algebra, Tags 06Y6 and 08IB.
(blueprint: lem-pc-base-derived-tensor-model-quasiiso-ordinary-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory
open scoped ChangeOfRings
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

set_option linter.unusedSectionVars false in
private theorem tensorLinearLift
    (M N : ModuleCat.{u} (A ⊗[R] B))
    (f : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ⟶
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = f := by
  refine ⟨ofHom { toFun := f, map_add' := f.hom.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.inductionOn with
    | tmul a b =>
      have hb (y : M) :
          f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • y) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f y :=
        f.hom.map_smul b y
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.hom.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl


/-- The tensor-algebra cohomology isomorphism commutes with the ordinary counit.

Proof: restrict the quasi-isomorphism to R-modules; exactness of restriction
makes it invertible in D(R). The unique isomorphism between the two universal
left-derived functors, compatible with the counits, and the image of this
invertible map give an isomorphism of their derived values. Apply B-cohomology
and conjugate by cohomologyIso. Naturality for multiplication by a in A and
cohomologyIso_smul show that this B-linear map commutes with a tensor 1.
B-linearity gives compatibility with 1 tensor b. Products and sums of these
operators generate A tensor_R B, so tensor induction makes the map linear
for that algebra. Its inverse is linear by the same commuting identities.
This gives e. The generator equations ordinaryIso_tmul show that the ordinary
isomorphisms are natural for s: both composites send b tensor q to
(1 tensor b) tensor s(q). Naturality of the counits, of the derived and homotopy
homology factorization maps, and of restriction-of-scalars homology
isomorphisms now gives the comparison square after substituting comparison_eq.
Faithfulness of restriction of scalars identifies it as the claimed square
of A-tensor-R-B-linear maps. No localization or extension to D is used here.
Source: Stacks Project, Tags 06Y6 and 08IB, perfect.tex equation-bc before Tag 0DJ8.
(blueprint: lem-pc-base-derived-tensor-model-quasiiso-ordinary-comparison). -/
theorem exists_baseDerivedTensorModel_quasiIso_ordinary_comparison
    {P G : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ G) (hs : QuasiIso s)
    (MP : BaseDerivedTensorCohomologyModel R A B P D)
    (MG : BaseDerivedTensorCohomologyModel R A B G D) (i : ℤ) :
    ∃ e : MP.cohomology i ≅ MG.cohomology i,
      MP.comparison i ≫ HomologicalComplex.homologyMap
        (((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).map s) i =
      e.hom ≫ MG.comparison i := by
  let FR := (restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let U := restrictScalars (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have : MP.derived.IsLeftDerivedFunctor MP.counit W := MP.universal
  have : MG.derived.IsLeftDerivedFunctor MG.counit W := MG.universal
  let η := Functor.leftDerivedUnique MG.derived MP.derived MP.counit MG.counit W
  let KP := FR ⋙ πR ⋙ DerivedCategory.Qh ⋙ MP.derived ⋙ H
  let KG := FR ⋙ πR ⋙ DerivedCategory.Qh ⋙ MG.derived ⋙ H
  let δ : KP ≅ KG := Functor.isoWhiskerLeft (FR ⋙ πR ⋙ DerivedCategory.Qh)
    (Functor.isoWhiskerRight η H)
  have : QuasiIso s := hs
  have : QuasiIso (FR.map s) := inferInstance
  have hqs : IsIso (DerivedCategory.Qh.map (πR.map (FR.map s))) := by
    rw [DerivedCategory.isIso_Qh_map_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (show QuasiIso (FR.map s) from inferInstance)
  have : IsIso (KP.map s) := by
    dsimp only [KP, Functor.comp_map]
    infer_instance
  let eb : U.obj (MP.cohomology i) ≅ U.obj (MG.cohomology i) :=
    MP.cohomologyIso i ≪≫ asIso (KP.map s) ≪≫ δ.app G ≪≫ (MG.cohomologyIso i).symm
  have hA (a : A) :
      U.map ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
        𝟙 (MP.cohomology i)) ≫ eb.hom =
      eb.hom ≫ U.map ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
        𝟙 (MG.cohomology i)) := by
    have hP := MP.cohomologyIso_smul i a
    have hG := MG.cohomologyIso_smul i a
    change U.map _ ≫ (MP.cohomologyIso i).hom =
      (MP.cohomologyIso i).hom ≫ KP.map (a • 𝟙 P) at hP
    change U.map _ ≫ (MG.cohomologyIso i).hom =
      (MG.cohomologyIso i).hom ≫ KG.map (a • 𝟙 G) at hG
    have hcomm : (a • 𝟙 P) ≫ s = s ≫ (a • 𝟙 G) := by simp
    have hmap := congrArg KP.map hcomm
    simp only [Functor.map_comp] at hmap
    have hn : KP.map (a • 𝟙 G) ≫ (δ.app G).hom =
        (δ.app G).hom ≫ KG.map (a • 𝟙 G) := δ.hom.naturality (a • 𝟙 G)
    dsimp only [eb, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hP]
    simp only [Category.assoc]
    rw [← Category.assoc (KP.map (a • 𝟙 P)), hmap]
    simp only [Category.assoc]
    rw [← Category.assoc (KP.map (a • 𝟙 G)), hn]
    have hGi : KG.map (a • 𝟙 G) ≫ (MG.cohomologyIso i).inv =
        (MG.cohomologyIso i).inv ≫ U.map
          ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
            𝟙 (MG.cohomology i)) := by
      rw [← cancel_epi (MG.cohomologyIso i).hom]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun q => q ≫ (MG.cohomologyIso i).inv) hG.symm
    simp only [Category.assoc]
    rw [hGi]
  obtain ⟨e0, he0⟩ := tensorLinearLift R A B (MP.cohomology i) (MG.cohomology i)
    eb.hom (by
      intro a x
      exact congrArg (fun h => h x) (hA a))
  have : IsIso e0 := by
    apply (ConcreteCategory.isIso_iff_bijective e0).2
    have hb := (ConcreteCategory.isIso_iff_bijective eb.hom).1 inferInstance
    have hefun : (e0 : MP.cohomology i → MG.cohomology i) = eb.hom := by
      funext x
      exact congrArg (fun q => q x) he0
    simpa only [hefun] using hb
  let F := extendScalars (algebraMap R B)
  let J := extendScalars (algebraMap A (A ⊗[R] B))
  let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let t := (F.mapHomologicalComplex (.up ℤ)).map (FR.map s)
  let u := (J.mapHomologicalComplex (.up ℤ)).map s
  have hO : t ≫ MG.ordinaryIso.hom =
      MP.ordinaryIso.hom ≫ (U.mapHomologicalComplex (.up ℤ)).map u := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ExtendScalars.hom_ext
    intro q
    let q' : P.X j := q
    change MG.ordinaryIso.hom.f j (F.map ((restrictScalars (algebraMap R A)).map
        (s.f j)) ((1 : B) ⊗ₜ[R, algebraMap R B] q')) =
      U.map (J.map (s.f j))
        (MP.ordinaryIso.hom.f j ((1 : B) ⊗ₜ[R, algebraMap R B] q'))
    rw [ExtendScalars.map_tmul, MG.ordinaryIso_tmul, MP.ordinaryIso_tmul]
    change (Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A,
        algebraMap A (A ⊗[R] B)] (s.f j) q') =
      J.map (s.f j) (Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A,
        algebraMap A (A ⊗[R] B)] q')
    exact (ExtendScalars.map_tmul _ _ _ _).symm
  have hfac : η.hom.app (DerivedCategory.Qh.obj (πR.obj (FR.obj P))) ≫
      MG.counit.app (πR.obj (FR.obj P)) = MP.counit.app (πR.obj (FR.obj P)) := by
    change (Functor.leftDerivedNatTrans MP.derived MG.derived MP.counit MG.counit W
      (𝟙 _)).app _ ≫ _ = _
    simpa only [NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app MP.derived MG.derived MP.counit MG.counit W
        (𝟙 _) (πR.obj (FR.obj P))
  have hc : MP.derived.map (DerivedCategory.Qh.map (πR.map (FR.map s))) ≫
      η.hom.app (DerivedCategory.Qh.obj (πR.obj (FR.obj G))) ≫
        MG.counit.app (πR.obj (FR.obj G)) =
      MP.counit.app (πR.obj (FR.obj P)) ≫ DerivedCategory.Qh.map (πB.map t) := by
    have hn := MG.counit.naturality (πR.map (FR.map s))
    change MG.derived.map (DerivedCategory.Qh.map (πR.map (FR.map s))) ≫
        MG.counit.app (πR.obj (FR.obj G)) =
      MG.counit.app (πR.obj (FR.obj P)) ≫ DerivedCategory.Qh.map (πB.map t) at hn
    rw [← Category.assoc, η.hom.naturality, Category.assoc, hn,
      ← Category.assoc, hfac]
  have h1 := congrArg H.map hc
  simp only [Functor.map_comp] at h1
  have h2 := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.naturality
    (πB.map t)
  have h3 := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.naturality
    t
  have h4 := congrArg (fun a => HomologicalComplex.homologyMap a i) hO
  simp only [HomologicalComplex.homologyMap_comp] at h4
  have h5 := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map u) U
  change U.map (HomologicalComplex.homologyMap u i) ≫
      (((J.mapHomologicalComplex (.up ℤ)).obj G).sc i |>.mapHomologyIso U).inv =
    (((J.mapHomologicalComplex (.up ℤ)).obj P).sc i |>.mapHomologyIso U).inv ≫
      HomologicalComplex.homologyMap ((U.mapHomologicalComplex (.up ℤ)).map u) i at h5
  refine ⟨asIso e0, ?_⟩
  apply U.map_injective
  simp only [Functor.map_comp, asIso_hom]
  change U.map (MP.comparison i) ≫ U.map (HomologicalComplex.homologyMap u i) =
    U.map e0 ≫ U.map (MG.comparison i)
  rw [show U.map e0 = eb.hom from he0]
  apply (cancel_mono (((J.mapHomologicalComplex (.up ℤ)).obj G).sc i
    |>.mapHomologyIso U).inv).1
  rw [Category.assoc, h5]
  rw [← Category.assoc, MP.comparison_eq]
  simp only [Category.assoc]
  rw [MG.comparison_eq]
  dsimp only [eb, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change KP.map s ≫ (δ.app G).hom ≫ H.map (MG.counit.app (πR.obj (FR.obj G))) =
    H.map (MP.counit.app (πR.obj (FR.obj P))) ≫
      H.map (DerivedCategory.Qh.map (πB.map t)) at h1
  dsimp only [Functor.comp_map] at h2 h3
  change (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).map (πB.map t) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ ≫
      HomologicalComplex.homologyMap t i at h3
  rw [← h4]
  have hh := congrArg (fun a => (MP.cohomologyIso i).hom ≫ a ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
        (πB.obj ((F.mapHomologicalComplex (.up ℤ)).obj (FR.obj G))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj (FR.obj G)) ≫
      HomologicalComplex.homologyMap MG.ordinaryIso.hom i) h1
  simp only [Category.assoc] at hh
  rw [reassoc_of% h2, reassoc_of% h3] at hh
  exact hh.symm

end ModuleCat
