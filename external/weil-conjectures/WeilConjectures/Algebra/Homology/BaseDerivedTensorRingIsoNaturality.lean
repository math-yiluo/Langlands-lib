/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingTransport

/-! # Naturality of the localized tensor counit under ring isomorphisms

Source: Stacks Project, Tag 06Y6, derived change of rings; Tag 0DJ7, equation-bc.
(blueprint: lem-pc-base-derived-tensor-ring-iso-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace ModuleCat

private theorem leftHomologyForgetRestriction
    {D D0 : Type u} [CommRing D] [CommRing D0] (eD : D ≃+* D0)
    (S : ShortComplex (ModuleCat.{u} D0)) (h : S.LeftHomologyData) :
    let T := restrictScalars.{u} eD.toRingHom
    let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
    ((h.map T).map F).homologyIso.hom = (h.map F0).homologyIso.hom := by
  dsimp only
  let T := restrictScalars.{u} eD.toRingHom
  let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
  let h1 := (h.map T).map F
  let h2 := h.map F0
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map F0)) h1 h2 :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by
        simp only [ShortComplex.id_τ₂, Category.comp_id, Category.id_comp]
        rfl
      commf' := by
        simp only [ShortComplex.id_τ₁, Category.comp_id, Category.id_comp]
        simp only [h1, h2, ShortComplex.LeftHomologyData.map_f']
        rfl
      commπ := by
        simp only [Category.comp_id, Category.id_comp]
        rfl }
  have hiso := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    (𝟙 (S.map F0)) h1 h2
  rw [γ.leftHomologyMap'_eq, ShortComplex.homologyMap_id] at hiso
  change h1.homologyIso.hom ≫ 𝟙 _ = 𝟙 _ ≫ h2.homologyIso.hom at hiso
  simpa only [Category.comp_id, Category.id_comp] using hiso

private theorem forgetRestrictionHomology
    {D D0 : Type u} [CommRing D] [CommRing D0] (eD : D ≃+* D0)
    (S : ShortComplex (ModuleCat.{u} D0)) :
    let T := restrictScalars.{u} eD.toRingHom
    let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
    ((S.map T).mapHomologyIso F).hom ≫ F.map (S.mapHomologyIso T).hom =
      (S.mapHomologyIso F0).hom := by
  dsimp only
  let T := restrictScalars.{u} eD.toRingHom
  let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
  rw [(S.homologyData.left.map T).mapHomologyIso_eq F]
  change ((S.homologyData.left.map T).map F).homologyIso.hom ≫
    F.map ((S.mapHomologyIso T).inv) ≫ F.map ((S.mapHomologyIso T).hom) = _
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact leftHomologyForgetRestriction eD S S.homologyData.left

/-- Transport the localized tensor comparison through compatible ring isomorphisms.
The target chain isomorphism is fixed on pure tensors, rather than chosen freely.

Proof: the structural equations at a tensor 1 and 1 tensor b give the two
coefficient maps into D. Forget the scalars of q and t to get additive chain
isomorphisms; q's linearity supplies semilinearity of the first, and ht supplies
the generator formula of the second. Apply exists_baseDerivedTensor_ring_transport.
Forgetting after restriction has the same homology comparison as forgetting
directly: compare the two mapped left homology data using identity maps on
cycles and homology. Homology naturality at t then cancels the forgetful homology
isomorphisms in the transport theorem and gives exactly the displayed square.
No flatness, boundedness, or invertibility of either comparison is required.
The proof also applies to zero rings and zero complexes.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ7, equation-bc.
(blueprint: lem-pc-base-derived-tensor-ring-iso-naturality). -/
theorem exists_baseDerivedTensor_ringIso_square
    {R A B D R0 A0 B0 D0 : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [CommRing R0] [CommRing A0] [CommRing B0] [CommRing D0]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [Algebra R0 A0] [Algebra R0 B0] [Algebra (A0 ⊗[R0] B0) D0]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R0)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B0)]
    (eR : R ≃+* R0) (eA : A ≃+* A0) (eB : B ≃+* B0) (eD : D ≃+* D0)
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R0 A0 (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R0 B0 (eR r))
    (hD : ∀ (a : A) (b : B),
      eD (algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] b)) =
        algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Q0 : CochainComplex (ModuleCat.{u} A0) ℤ)
    (q : Q ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q0)
    (M : BaseDerivedTensorCohomologyModel R A B Q D)
    (M0 : BaseDerivedTensorCohomologyModel R0 A0 B0 Q0 D0)
    (t : (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((restrictScalars.{u} eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars.{u, u, u} ((algebraMap (A0 ⊗[R0] B0) D0).comp
          (algebraMap A0 (A0 ⊗[R0] B0)))).mapHomologicalComplex (.up ℤ)).obj Q0))
    (ht : ∀ (k : ℤ) (d : D) (x : Q.X k),
      t.hom.f k (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B))] x) =
      eD d ⊗ₜ[A0, (algebraMap (A0 ⊗[R0] B0) D0).comp
        (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x))
    (i : ℤ) :
    let V0 := ((extendScalars.{u, u, u} ((algebraMap (A0 ⊗[R0] B0) D0).comp
      (algebraMap A0 (A0 ⊗[R0] B0)))).mapHomologicalComplex (.up ℤ)).obj Q0
    let T := restrictScalars.{u} eD.toRingHom
    let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
    ∃ l : F.obj ((extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) D)).obj
        (M.cohomology i)) ≅
        F0.obj ((extendScalars.{u, u, u} (algebraMap (A0 ⊗[R0] B0) D0)).obj
          (M0.cohomology i)),
      l.hom ≫ F0.map (M0.localizedComparison i) ≫
          F.map ((V0.sc i).mapHomologyIso T).inv =
        F.map (M.localizedComparison i) ≫
          F.map (HomologicalComplex.homologyMap t.hom i) := by
  let FA := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let FA0 := forget₂ (ModuleCat.{u} A0) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
  let α : (FA.mapHomologicalComplex (.up ℤ)).obj Q ≅
      (FA0.mapHomologicalComplex (.up ℤ)).obj Q0 :=
    (FA.mapHomologicalComplex (.up ℤ)).mapIso q
  have hα (k : ℤ) (a : A) (x : Q.X k) :
      α.hom.f k (a • x) = eA a • (show Q0.X k from α.hom.f k x) :=
    (q.hom.f k).hom.map_smul a x
  have hRA : eA.toRingHom.comp (algebraMap R A) =
      (algebraMap R0 A0).comp eR.toRingHom := by
    ext r
    exact hA r
  have hRB : eB.toRingHom.comp (algebraMap R B) =
      (algebraMap R0 B0).comp eR.toRingHom := by
    ext r
    exact hB r
  have hDA : eD.toRingHom.comp
      ((algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))) =
      ((algebraMap (A0 ⊗[R0] B0) D0).comp
        (algebraMap A0 (A0 ⊗[R0] B0))).comp eA.toRingHom := by
    ext a
    simpa using hD a 1
  have hDB : eD.toRingHom.comp ((algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom) =
      ((algebraMap (A0 ⊗[R0] B0) D0).comp
        Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom := by
    ext b
    simpa using hD 1 b
  let V := ((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
    (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
  let V0 := ((extendScalars.{u, u, u} ((algebraMap (A0 ⊗[R0] B0) D0).comp
    (algebraMap A0 (A0 ⊗[R0] B0)))).mapHomologicalComplex (.up ℤ)).obj Q0
  let τ : (F.mapHomologicalComplex (.up ℤ)).obj V ≅
      (F0.mapHomologicalComplex (.up ℤ)).obj V0 :=
    (F.mapHomologicalComplex (.up ℤ)).mapIso t
  have hτ (k : ℤ) (d : D) (x : Q.X k) :
      τ.hom.f k (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B))] x) =
      eD d ⊗ₜ[A0, (algebraMap (A0 ⊗[R0] B0) D0).comp
        (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from α.hom.f k x) := ht k d x
  obtain ⟨l, hl⟩ := exists_baseDerivedTensor_ring_transport Q Q0 M M0
    eR eA eB eD hRA hRB hDA hDB α hα τ hτ i
  refine ⟨l, ?_⟩
  let T := restrictScalars.{u} eD.toRingHom
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map t.hom) F
  have hc := forgetRestrictionHomology eD (V0.sc i)
  change l.hom ≫ F0.map (M0.localizedComparison i) ≫
    F.map ((V0.sc i).mapHomologyIso T).inv =
      F.map (M.localizedComparison i) ≫ F.map (HomologicalComplex.homologyMap t.hom i)
  have hc' : ((V0.sc i).mapHomologyIso F0).hom ≫
      F.map ((V0.sc i).mapHomologyIso T).inv =
      (((V0.sc i).map T).mapHomologyIso F).hom := by
    rw [← hc, Category.assoc]
    erw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  calc
    _ = F.map (M.localizedComparison i) ≫ ((V.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫
        ((V0.sc i).mapHomologyIso F0).hom ≫
        F.map ((V0.sc i).mapHomologyIso T).inv := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ F.map ((V0.sc i).mapHomologyIso T).inv) hl.symm
    _ = F.map (M.localizedComparison i) ≫ ((V.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫
        (((V0.sc i).map T).mapHomologyIso F).hom := by rw [hc']
    _ = _ := by
      change F.map (M.localizedComparison i) ≫ ((V.sc i).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap (F.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map t.hom)) ≫
        (((V0.sc i).map T).mapHomologyIso F).hom = _
      erw [hn]
      erw [Iso.inv_hom_id_assoc]
      rfl

end ModuleCat
