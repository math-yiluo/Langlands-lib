/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivCohomology
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingCounitSquare

/-! # Derived tensor comparison after restriction to the second coefficient ring

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices.
(blueprint: lem-pc-base-derived-tensor-restricted-ring-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Transport derived tensor cohomology as a module over the second coefficient ring.

Proof: restriction along eR and eB, with restriction along their inverses, gives
exact inverse equivalences of module categories. Applying them termwise gives
inverse equivalences of homotopy categories preserving quasi-isomorphisms. The
localization universal property extends these to the chosen derived categories,
also when their morphism universes differ. The coefficient tensor isomorphism
identifies ordinary extension of scalars, on generators b tensor x. Transport
M.derived and its universal counit through the localization equivalences.
Uniqueness of left derived functors identifies this transported functor with
N.derived, compatibly with the counits. Apply homology to its component at q and
conjugate by M.cohomologyIso and N.cohomologyIso; this gives kB and its inverse.
Naturality at multiplication by a, together with cohomologyIso_smul, gives the
first identity. The counit compatibility, comparison_eq and ordinaryIso_tmul,
followed by exact-restriction homology naturality, give the second identity on
underlying elements. The given generator formula for s identifies the ordinary
complex map appearing there. Restriction along includeRight is faithful, so the
ordinaryIso generator calculation suffices. No tensor-algebra linearity of kB
is asserted here: that is obtained by tensor induction in the caller. No
flatness or invertibility of comparison maps is used. Zero rings and complexes
are permitted, and the maps to C₀ and C do not enter this argument.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices and
universal derived change of rings; localization uniqueness supplies the
possibly different morphism universes.
(blueprint: lem-pc-base-derived-tensor-restricted-ring-comparison). -/
theorem exists_baseDerivedTensor_restricted_ring_comparison
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom)
    (q : Q₀ ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q)
    (eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B))
    (heE : ∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b)
    (s : ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
        (.up ℤ)).obj Q₀ ≅
      ((restrictScalars.{u} eE.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj Q))
    (hs : ∀ (j : ℤ) (r : A₀ ⊗[R₀] B₀) (x : Q₀.X j),
      s.hom.f j (r ⊗ₜ[A₀,algebraMap A₀ (A₀ ⊗[R₀] B₀)] x) =
        eE r ⊗ₜ[A,algebraMap A (A ⊗[R] B)] (show Q.X j from q.hom.f j x))
    (i : ℤ) :
    let K := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    ∃ kB : (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
        (M.cohomology i) ≅
      (restrictScalars.{u} eB.toRingHom).obj
        ((restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
          (N.cohomology i)),
      (∀ (a : A₀) (x : M.cohomology i),
        kB.hom ((Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) • x) =
          (Algebra.TensorProduct.includeLeft (S := R) (eA a) : A ⊗[R] B) •
            (show N.cohomology i from kB.hom x)) ∧
      ∀ x : M.cohomology i,
        ((K.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).inv
            (N.comparison i (show N.cohomology i from kB.hom x)) =
          HomologicalComplex.homologyMap s.hom i (M.comparison i x) := by
  dsimp only
  let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
  let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let P₀ := π₀ ⋙ DerivedCategory.Qh ⋙ M.derived ⋙ H₀
  let P := π ⋙ DerivedCategory.Qh ⋙ N.derived ⋙ H
  let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
  let U := restrictScalars.{u} eB.toRingHom
  let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
  let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
  let c₀ := fun K : CochainComplex (ModuleCat.{u} R₀) ℤ ↦
    H₀.map (M.counit.app (π₀.obj K)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.app
        ((HomotopyCategory.quotient _ _).obj (T₀.obj K)) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i).hom.app
        (T₀.obj K)
  let c := fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦
    H.map (N.counit.app (π.obj K)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
        ((HomotopyCategory.quotient _ _).obj (T.obj K)) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
        (T.obj K)
  let F₀ := (restrictScalars.{u} (algebraMap R₀ A₀)).mapHomologicalComplex (.up ℤ)
  let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let K₀ := F₀.obj Q₀
  let K := F.obj Q
  let S₀ := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B₀ →ₐ[R₀] A₀ ⊗[R₀] B₀).toRingHom
  let S := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let ρ : restrictScalars.{u} eA.toRingHom ⋙ restrictScalars (algebraMap R₀ A₀) ≅
      restrictScalars (algebraMap R A) ⋙ restrictScalars eR.toRingHom :=
    (restrictScalarsComp (algebraMap R₀ A₀) eA.toRingHom).symm ≪≫
      restrictScalarsComp' eR.toRingHom (algebraMap R A)
        (eA.toRingHom.comp (algebraMap R₀ A₀)) hRA
  let p : K₀ ≅ V.obj K := F₀.mapIso q ≪≫ (NatIso.mapHomologicalComplex ρ (.up ℤ)).app Q
  obtain ⟨t, d, ht, hd⟩ := exists_derivedExtension_ringEquiv_cohomology
    M.derived N.derived M.counit N.counit M.universal N.universal eR eB hRB i
  let f : P₀.obj K₀ ⟶ U.obj (P.obj K) := P₀.map p.hom ≫ d.hom.app K
  let kB : S₀.obj (M.cohomology i) ≅ U.obj (S.obj (N.cohomology i)) :=
    M.cohomologyIso i ≪≫ P₀.mapIso p ≪≫ d.app K ≪≫ (U.mapIso (N.cohomologyIso i)).symm
  have hk : kB.hom ≫ U.map (N.cohomologyIso i).hom = (M.cohomologyIso i).hom ≫ f := by
    simp only [kB, f, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id]
    erw [U.map_id, Category.comp_id]
  have hA (a : A₀) :
      S₀.map ((Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) •
        𝟙 (M.cohomology i)) ≫ kB.hom =
      kB.hom ≫ U.map (S.map
        ((Algebra.TensorProduct.includeLeft (S := R) (eA a) : A ⊗[R] B) •
          𝟙 (N.cohomology i))) := by
    have hp : F₀.map (a • 𝟙 Q₀) ≫ p.hom =
        p.hom ≫ V.map (F.map (eA a • 𝟙 Q)) := by
      apply HomologicalComplex.hom_ext
      intro j
      ext x
      change q.hom.f j (a • (show Q₀.X j from x)) =
        eA a • (show Q.X j from q.hom.f j x)
      exact (q.hom.f j).hom.map_smul a x
    have hmap := congrArg P₀.map hp
    simp only [Functor.map_comp] at hmap
    have hn := d.hom.naturality (F.map (eA a • 𝟙 Q))
    change P₀.map (V.map (F.map (eA a • 𝟙 Q))) ≫ d.hom.app K =
      d.hom.app K ≫ U.map (P.map (F.map (eA a • 𝟙 Q))) at hn
    have hM := M.cohomologyIso_smul i a
    change S₀.map _ ≫ (M.cohomologyIso i).hom =
      (M.cohomologyIso i).hom ≫ P₀.map (F₀.map (a • 𝟙 Q₀)) at hM
    have hN := congrArg U.map (N.cohomologyIso_smul i (eA a))
    simp only [Functor.map_comp] at hN
    change U.map (S.map _) ≫ U.map (N.cohomologyIso i).hom =
      U.map (N.cohomologyIso i).hom ≫ U.map (P.map (F.map (eA a • 𝟙 Q))) at hN
    apply (cancel_mono (U.map (N.cohomologyIso i).hom)).1
    rw [Category.assoc, hk]
    rw [← Category.assoc, hM]
    simp only [Category.assoc, f]
    rw [← Category.assoc (P₀.map (F₀.map (a • 𝟙 Q₀))), hmap]
    simp only [Category.assoc]
    rw [hn, hN, ← Category.assoc kB.hom, hk]
    simp only [f, Category.assoc]
  let v : T₀.obj K₀ ≅ (U.mapHomologicalComplex (.up ℤ)).obj (T.obj K) :=
    T₀.mapIso p ≪≫ t.app K
  have hv (j : ℤ) (b : B₀) (x : Q₀.X j) :
      v.hom.f j (b ⊗ₜ[R₀,algebraMap R₀ B₀] (show K₀.X j from x)) =
        eB b ⊗ₜ[R,algebraMap R B] (show K.X j from q.hom.f j x) := by
    change (t.hom.app K).f j
      ((extendScalars (algebraMap R₀ B₀)).map (p.hom.f j)
        (b ⊗ₜ[R₀,algebraMap R₀ B₀] x)) = _
    rw [ExtendScalars.map_tmul, ht]
    rfl
  have hf : f ≫ U.map (c K) = c₀ K₀ ≫ HomologicalComplex.homologyMap v.hom i ≫
      ((T.obj K).sc i |>.mapHomologyIso U).hom := by
    let πB₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ)
    have h₁ := congrArg H₀.map (M.counit.naturality (π₀.map p.hom))
    simp only [Functor.comp_map, Functor.map_comp] at h₁
    have h₂ := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.naturality
      (πB₀.map (T₀.map p.hom))
    have h₃ := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀)
      (.up ℤ) i).hom.naturality (T₀.map p.hom)
    dsimp only [Functor.comp_map] at h₂ h₃
    have hc₀ : P₀.map p.hom ≫ c₀ (V.obj K) =
        c₀ K₀ ≫ HomologicalComplex.homologyMap (T₀.map p.hom) i := by
      dsimp only [c₀]
      simp only [Category.assoc]
      erw [← Category.assoc, ← Category.assoc, h₁]
      simp only [Category.assoc]
      erw [reassoc_of% h₂]
      exact congrArg (fun m ↦ H₀.map (M.counit.app (π₀.obj K₀)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.app
          (πB₀.obj (T₀.obj K₀)) ≫ m) h₃
    have hdK : d.hom.app K ≫ U.map (c K) =
        c₀ (V.obj K) ≫ HomologicalComplex.homologyMap (t.hom.app K) i ≫
          ((T.obj K).sc i |>.mapHomologyIso U).hom := hd K
    dsimp only [f]
    rw [Category.assoc, hdK]
    simp only [← Category.assoc]
    rw [hc₀]
    simp only [Category.assoc]
    simp only [v, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      HomologicalComplex.homologyMap_comp, Category.assoc]
  refine ⟨kB, ?_, ?_⟩
  · intro a x
    exact ConcreteCategory.congr_hom (hA a) x
  · exact baseDerivedTensor_ring_counit_square Q₀ Q M N eA eB q eE heE s hs i
      v hv f hf kB.hom hk

end ModuleCat
