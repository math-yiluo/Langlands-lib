/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps

/-! # Naturality of the explicit strict Roos cohomology maps

proof.md, first paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableLimits A]

set_option backward.isDefEq.respectTransparency false in
private theorem roosMap_eq {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : K ⟶ L) :
    WeilConjectures.integralOperationsRoosMap f =
      (shiftFunctor _ (-1 : ℤ)).map
        (CochainComplex.mappingCone.map (roosTransition K) (roosTransition L)
          (Limits.Pi.map (fun n ↦ f.app (op n))) (Limits.Pi.map (fun n ↦ f.app (op n)))
          (WeilConjectures.integralOperationsRoos_square f)) := by
  unfold WeilConjectures.integralOperationsRoosMap
  congr 1
  ext p
  simp [CochainComplex.mappingCone.map, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
        HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.desc_f _ _ _ _ p (p + 1) rfl,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd, roosTransition]

set_option backward.isDefEq.respectTransparency false in
private theorem towerKernelIso_π (M : ℕᵒᵖ ⥤ A) (n : ℕ) :
    (towerKernelIso M).hom ≫ limit.π M (op n) =
      kernel.ι _ ≫ Pi.π (fun n : ℕ ↦ M.obj (op n)) n := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel _)
    (Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct _)
      (towerProductShift (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op))
      (fun n ↦ by simp [towerProductShift]) (limit.isLimit M))
    WalkingParallelPair.zero
  change (towerKernelIso M).hom ≫
    Fan.IsLimit.lift (productIsProduct (fun n : ℕ ↦ M.obj (op n)))
      (fun n : ℕ ↦ limit.π M (op n)) = kernel.ι _ at h
  have h' := congrArg (fun k ↦ k ≫ Pi.π (fun n : ℕ ↦ M.obj (op n)) n) h
  have hf := Fan.IsLimit.fac (productIsProduct (fun n : ℕ ↦ M.obj (op n)))
    (fun n : ℕ ↦ limit.π M (op n)) n
  change _ ≫ Pi.π (fun n : ℕ ↦ M.obj (op n)) n = limit.π M (op n) at hf
  simpa only [Category.assoc, hf] using h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem roosProjection_chain {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : K ⟶ L) :
    WeilConjectures.integralOperationsRoosMap f ≫
        CochainComplex.mappingCocone.fst (roosTransition L) =
      CochainComplex.mappingCocone.fst (roosTransition K) ≫
        Limits.Pi.map (fun n ↦ f.app (op n)) := by
  rw [roosMap_eq]
  apply HomologicalComplex.hom_ext
  intro p
  have hc : (CochainComplex.mappingCone.map (roosTransition K) (roosTransition L)
      (Limits.Pi.map (fun n ↦ f.app (op n)))
      (Limits.Pi.map (fun n ↦ f.app (op n)))
      (WeilConjectures.integralOperationsRoos_square f)).f (p + -1) ≫
        (CochainComplex.mappingCone.fst (roosTransition L)).1.v (p + -1) p (by omega) =
      (CochainComplex.mappingCone.fst (roosTransition K)).1.v (p + -1) p (by omega) ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f p := by
    simp [CochainComplex.mappingCone.ext_from_iff _ p (p + -1) (by omega),
      CochainComplex.mappingCone.map]
  simpa [CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.fst (roosTransition L)).1 (-1) 0 (by omega) p p
      (add_zero p) (p + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.fst (roosTransition K)).1 (-1) 0 (by omega) p p
      (add_zero p) (p + -1) (by omega)] using hc

set_option backward.isDefEq.respectTransparency false in
private noncomputable def roosTriangleMap {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : K ⟶ L) :
    CochainComplex.mappingCocone.triangle (roosTransition K) ⟶
      CochainComplex.mappingCocone.triangle (roosTransition L) where
  hom₁ := WeilConjectures.integralOperationsRoosMap f
  hom₂ := Limits.Pi.map (fun n ↦ f.app (op n))
  hom₃ := Limits.Pi.map (fun n ↦ f.app (op n))
  comm₁ := (roosProjection_chain f).symm
  comm₂ := WeilConjectures.integralOperationsRoos_square f
  comm₃ := by
    symm
    change Limits.Pi.map (fun n ↦ f.app (op n)) ≫
      (CochainComplex.mappingCone.inr (roosTransition L) ≫ _) =
      (CochainComplex.mappingCone.inr (roosTransition K) ≫ _) ≫ _
    rw [roosMap_eq]
    let c := CochainComplex.mappingCone.triangleMap (roosTransition K) (roosTransition L)
      (Limits.Pi.map (fun n ↦ f.app (op n)))
      (Limits.Pi.map (fun n ↦ f.app (op n)))
      (WeilConjectures.integralOperationsRoos_square f)
    have hc : CochainComplex.mappingCone.inr (roosTransition K) ≫
        CochainComplex.mappingCone.map (roosTransition K) (roosTransition L)
          (Limits.Pi.map (fun n ↦ f.app (op n)))
          (Limits.Pi.map (fun n ↦ f.app (op n)))
          (WeilConjectures.integralOperationsRoos_square f) =
      Limits.Pi.map (fun n ↦ f.app (op n)) ≫
        CochainComplex.mappingCone.inr (roosTransition L) := c.comm₂
    rw [← Category.assoc, ← hc, Category.assoc, Category.assoc]
    congr 1
    exact (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)).inv.naturality _

set_option backward.isDefEq.respectTransparency false in
private theorem roosBoundary_naturality {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    HomologicalComplex.homologyMap (Limits.Pi.map (fun n ↦ f.app (op n))) (q - 1) ≫
        roosBoundary L q =
      roosBoundary K q ≫ HomologicalComplex.homologyMap
        (WeilConjectures.integralOperationsRoosMap f) q := by
  have hn (T U : Triangle (CochainComplex A ℤ)) (c : T ⟶ U) :
      HomologicalComplex.homologyMap c.hom₃ (q - 1) ≫
          CochainComplex.homologyδOfTriangle U (q - 1) q (by omega) =
        CochainComplex.homologyδOfTriangle T (q - 1) q (by omega) ≫
          HomologicalComplex.homologyMap c.hom₁ q := by
    dsimp only [CochainComplex.homologyδOfTriangle]
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← c.comm₃,
      HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc]
    congr 1
    exact ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
      1 (q - 1) q (by omega)).hom.naturality _
  exact hn _ _ (roosTriangleMap f)

variable [HasExactLimitsOfShape (Discrete ℕ) A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorProjection_π (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) (n : ℕ) :
    milnorProjection K q ≫ limit.π (milnorCohomologyTower K q) (op n) =
      roosProjection K q ≫ HomologicalComplex.homologyMap
        (Pi.π (fun n : ℕ ↦ K.obj (op n)) n) q := by
  dsimp only [milnorProjection, roosKernelIso, Iso.trans_hom, kernel.mapIso, kernel.map]
  rw [Category.assoc, Category.assoc, towerKernelIso_π]
  erw [kernel.lift_ι_assoc]
  rw [← Category.assoc, kernel.lift_ι_assoc]
  change (roosProjection K q ≫ (productHomologyIso K q).hom) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (fun k ↦ roosProjection K q ≫ k)
    (piComparison_comp_π (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q)
      (fun n : ℕ ↦ K.obj (op n)) n)

set_option backward.isDefEq.respectTransparency false in
private theorem milnorInclusion_π (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    (productHomologyIso K (q - 1)).hom ≫
        cokernel.π (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (K.obj (op n)).homology (q - 1))
          (fun n ↦ HomologicalComplex.homologyMap
            (K.map (homOfLE (Nat.le_succ n)).op) (q - 1))) ≫ milnorInclusion K q =
      roosBoundary K q := by
  dsimp only [milnorInclusion, roosCokernelIso, cokernel.mapIso, cokernel.map]
  erw [cokernel.π_desc_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem productHomologyIso_naturality {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) :
    HomologicalComplex.homologyMap (Limits.Pi.map (fun n ↦ f.app (op n))) p ≫
        (productHomologyIso L p).hom =
      (productHomologyIso K p).hom ≫
        Limits.Pi.map (fun n ↦ HomologicalComplex.homologyMap (f.app (op n)) p) := by
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) p
  change H.map _ ≫ piComparison H (fun n : ℕ ↦ L.obj (op n)) =
    piComparison H (fun n : ℕ ↦ K.obj (op n)) ≫
      Limits.Pi.map (fun n ↦ H.map (f.app (op n)))
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Limits.Pi.map_π, H.map_comp]
  simp only [Category.assoc, Limits.Pi.map_π]
  rw [← Category.assoc, piComparison_comp_π]

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The maps obtained by factoring the cone boundary and projection are natural.

proof.md, first paragraph;
the expanded proof's naturality step (auxiliary; not a blueprint node).

Proof: A strict tower map induces the diagonal product map on both summands of
Cone(1-T)[-1]. The equation for the transition endomorphisms makes it a chain map.
The diagonal map commutes with the cone inclusion and negative projection, hence
with the connecting homomorphism and projection in cohomology. The canonical
product/cohomology comparison commutes with it, as is checked after each product
projection. On cokernels, cancel the cokernel projection and use the boundary
square; on kernels, compose with the kernel inclusion and use the projection
square. The kernel-to-limit identification respects every coordinate projection,
so it also commutes with the induced limit map. Transporting the two squares
along these endpoint isomorphisms gives the two equations below. No exactness
claim is part of this statement; the maps are the explicitly constructed maps. -/
theorem roos_cohomology_naturality {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableLimits A] [HasExactLimitsOfShape (Discrete ℕ) A]
    (q : ℤ) {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : K ⟶ L) :
    milnorTowerCokernelMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q - 1))) ≫
        milnorInclusion L q =
      milnorInclusion K q ≫ HomologicalComplex.homologyMap
        (WeilConjectures.integralOperationsRoosMap f) q ∧
    HomologicalComplex.homologyMap (WeilConjectures.integralOperationsRoosMap f) q ≫
        milnorProjection L q =
      milnorProjection K q ≫ limMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q)) := by
  constructor
  · let e := (productHomologyIso K (q - 1)).hom ≫
      cokernel.π (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ (K.obj (op n)).homology (q - 1))
        (fun n ↦ HomologicalComplex.homologyMap
          (K.map (homOfLE (Nat.le_succ n)).op) (q - 1)))
    have : Epi e := inferInstance
    apply (cancel_epi e).1
    have he : e ≫ milnorTowerCokernelMap (Functor.whiskerRight f
          (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q - 1))) =
        HomologicalComplex.homologyMap (Limits.Pi.map (fun n ↦ f.app (op n))) (q - 1) ≫
          (productHomologyIso L (q - 1)).hom ≫
            cokernel.π (towerTransitionEndomorphism
              (K := fun n : ℕ ↦ (L.obj (op n)).homology (q - 1))
              (fun n ↦ HomologicalComplex.homologyMap
                (L.map (homOfLE (Nat.le_succ n)).op) (q - 1))) := by
      dsimp only [e, milnorTowerCokernelMap, cokernel.map]
      erw [Category.assoc, cokernel.π_desc]
      simpa only [Category.assoc, Functor.whiskerRight_app, Functor.comp_map,
        HomologicalComplex.homologyFunctor_map, milnorTowerCokernel] using congrArg
        (fun k ↦ k ≫ cokernel.π (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (L.obj (op n)).homology (q - 1))
          (fun n ↦ HomologicalComplex.homologyMap
            (L.map (homOfLE (Nat.le_succ n)).op) (q - 1))))
        (productHomologyIso_naturality f (q - 1)).symm
    rw [← Category.assoc, he]
    dsimp only [e]
    simp only [Category.assoc]
    rw [milnorInclusion_π]
    have hk := congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap
      (WeilConjectures.integralOperationsRoosMap f) q) (milnorInclusion_π K q)
    simpa only [Category.assoc] using (roosBoundary_naturality f q).trans hk.symm
  · apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    rw [Category.assoc, milnorProjection_π, Category.assoc, limMap_π]
    change _ = milnorProjection K q ≫
      limit.π (milnorCohomologyTower K q) (op n) ≫
        HomologicalComplex.homologyMap (f.app (op n)) q
    rw [← Category.assoc (milnorProjection K q), milnorProjection_π]
    have h := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
      (roosProjection_chain f)
    simp only [HomologicalComplex.homologyMap_comp] at h
    rw [← Category.assoc, h, Category.assoc, ← HomologicalComplex.homologyMap_comp,
      Limits.Pi.map_π, HomologicalComplex.homologyMap_comp, ← Category.assoc]

end AlgebraicGeometry.Scheme.ProEt
