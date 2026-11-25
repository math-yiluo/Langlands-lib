/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Tensor.TensorProjectionAdjunct
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The affine-line localization triangle in normalized projective coordinates
Source: blueprint proposition-purity-vector-bundles, Step 5(b), detailed affine-space trace steps 2,
3 and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Restricting an inverse-image unit along a section is invertible.
private theorem section_unit_iso
    {C E H : Type*} [Category C] [Category E] [Category H]
    {P : C ⥤ E} {F : E ⥤ C} {I : E ⥤ H} {G : H ⥤ E}
    (a : P ⊣ F) (d : I ⊣ G) [(P ⋙ I).Full] [(P ⋙ I).Faithful]
    {X : C} {M : E} (e : P.obj X ≅ M) :
    IsIso (a.homEquiv _ _ e.hom ≫ F.map (d.unit.app M)) := by
  have h : a.homEquiv _ _ e.hom ≫ F.map (d.unit.app M) =
      (a.comp d).unit.app X ≫ (G ⋙ F).map (I.map e.hom) := by
    simp only [Adjunction.homEquiv_apply, Adjunction.comp_unit_app,
      Functor.comp_map, Category.assoc]
    have hd := d.unit.naturality e.hom
    change e.hom ≫ d.unit.app M =
      d.unit.app (P.obj X) ≫ G.map (I.map e.hom) at hd
    rw [← F.map_comp, hd, F.map_comp]
  rw [h]
  infer_instance

-- Change only the first coordinate, keeping the normalized trace unchanged.
private theorem normalize_closed_coordinate
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {B₀ B K M : C} (r : M ⟶ B) (c : M ⟶ K) (b₀ : B₀ ⊞ K ≅ M)
    (hr : IsIso (biprod.inl ≫ b₀.hom ≫ r)) (hc : b₀.hom ≫ c = biprod.snd) :
    ∃ b : B ⊞ K ≅ M,
      biprod.inl ≫ b.hom ≫ r = 𝟙 B ∧ b.hom ≫ c = biprod.snd := by
  let e := asIso (biprod.inl ≫ b₀.hom ≫ r)
  let b := biprod.mapIso e.symm (Iso.refl K) ≪≫ b₀
  refine ⟨b, ?_, ?_⟩
  · simp [b, e, Category.assoc]
  · simp [b, Category.assoc, hc]

/-- Push the open-closed triangle along the projective-line projection, retaining both
coordinates of the normalized projective-line decomposition.
Source: blueprint lemma-integral-linear-character--1, steps 2, 3 and 6
(blueprint: lem-amb-affine-trace-line-localization).

Proof: retain the closed vertex B = Rq_* Ri_* i^* M of the open-closed triangle
for the infinity section i and affine chart j, and push that triangle along Rq_*.
The exact/derived inverse-image comparison transports its open counit to the specified
adjunction J, including the induced comparison on the connecting morphism.
Tensor D.decomposition with K, use the tensor-unit comparison on the second summand,
and apply the proper projection formula to construct b₀ : B₀ ⊞ K ≅ Rq_* M, where
B₀ = K tensor A_S(1)[2]. The counit normalization gives b₀ followed by the projective
counit equal to second projection. The tensor-projection adjunct calculation identifies
the first injection followed by b₀ with the adjunct of the canonical isomorphism
q* B₀ ≅ M. Its composite with the restriction map r is invertible: it is the unit of
the composite adjunction q* then i*, followed by the image of an isomorphism, and
q* then i* is equivalent to identity because i is a section of q.
Change the first coordinate of b₀ by the inverse of this isomorphism B₀ ≅ B.
This makes the first injection followed by b and r exactly identity, while preserving
the normalized second projection. No assertion on the second restriction component
is required. All comparisons and the proper projection formula are unbounded.
The zero ring and empty scheme give the same argument in the zero category. -/
theorem affineTraceLine_localization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (D : OrdinaryFiniteP1Datum A N hA t S hS)
    (K : DerivedCategoryModule A S) :
    let F := ordinaryFinitePushforward A (ProjectiveLine S ↘ S)
    let J := affineTraceOpenAdjunction A S
    let M := (ordinaryFiniteP1Right A N hA S).obj K
    ∃ (B : DerivedCategoryModule A S) (r : F.obj M ⟶ B)
      (w : B ⟶ ((affineTraceLineLeft A S).obj
        ((affineTraceLineRight A N hA S).obj K))⟦(1 : ℤ)⟧)
      (b : B ⊞ K ≅ F.obj M),
      Triangle.mk (F.map (J.counit.app M)) r w ∈ distTriang _ ∧
        biprod.inl ≫ b.hom ≫ r = 𝟙 B ∧ b.hom ≫ D.adjunction.counit.app K = biprod.snd := by
  classical
  have _ := hN
  let q := ProjectiveLine S ↘ S
  let j := ProjectiveLine.affineChart S
  let i := ProjectiveLine.infinity S
  let F := ordinaryFinitePushforward A q
  let : F.CommShift ℤ := by
    dsimp [F, ordinaryFinitePushforward]
    infer_instance
  have : F.IsTriangulated := by
    dsimp [F, ordinaryFinitePushforward]
    infer_instance
  let P := ordinaryFinitePullback A q
  let I := (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory
  let G := ordinaryFinitePushforward A i
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
  let d := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i
  let M := (ordinaryFiniteP1Right A N hA S).obj K
  let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let E := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let T := (ordinaryFiniteTensor A S).obj K
  let B₀ := T.obj L
  let uK : T.obj (ordinaryFiniteUnit A S) ≅ K := derivedTensorSingleUnitIso K
  have : T.Additive := additive_derivedTensor_obj K
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A q
  have hp : IsIso (ordinaryFiniteProjection A q E K) := by
    unfold ordinaryFiniteProjection
    infer_instance
  let b₀ : B₀ ⊞ K ≅ F.obj M :=
    biprod.mapIso (Iso.refl B₀) uK.symm ≪≫
      (Functor.mapBiprod T L (ordinaryFiniteUnit A S)).symm ≪≫
      T.mapIso D.decomposition ≪≫ asIso (ordinaryFiniteProjection A q E K)
  have hc : b₀.hom ≫ D.adjunction.counit.app K = biprod.snd := by
    dsimp only [b₀, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Category.assoc]
    rw [D.counit_normalization K]
    change _ ≫ _ ≫ T.map D.decomposition.hom ≫
      T.map (D.decomposition.inv ≫ biprod.snd) ≫ uK.hom = _
    rw [← T.map_comp_assoc, D.decomposition.hom_inv_id_assoc]
    apply biprod.hom_ext'
    · simp only [biprod.mapIso_hom, Iso.refl_hom, Iso.symm_hom,
        biprod.inl_map_assoc, Category.id_comp, Functor.mapBiprod_inv,
        biprod.inl_desc_assoc, ← T.map_comp_assoc]
      change T.map ((biprod.inl : L ⟶ L ⊞ ordinaryFiniteUnit A S) ≫
        biprod.snd) ≫ uK.hom = (biprod.inl : B₀ ⟶ B₀ ⊞ K) ≫ biprod.snd
      erw [biprod.inl_snd, biprod.inl_snd, T.map_zero, zero_comp]
    · simp only [biprod.mapIso_hom, Iso.refl_hom, Iso.symm_hom,
        biprod.inr_map_assoc, Functor.mapBiprod_inv, biprod.inr_desc_assoc,
        ← T.map_comp_assoc]
      change uK.inv ≫ T.map ((biprod.inr : ordinaryFiniteUnit A S ⟶
        L ⊞ ordinaryFiniteUnit A S) ≫ biprod.snd) ≫ uK.hom =
          (biprod.inr : K ⟶ B₀ ⊞ K) ≫ biprod.snd
      erw [biprod.inr_snd, biprod.inr_snd, T.map_id, Category.id_comp,
        uK.inv_hom_id]
  let e : P.obj B₀ ≅ M :=
    leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) q K L ≪≫
      ((ordinaryFiniteTensor A (ProjectiveLine S)).obj (P.obj K)).mapIso
        (ordinaryFiniteShiftedLinePullback A N hA t q hS)
  have hb : biprod.inl ≫ b₀.hom = a.homEquiv _ _ e.hom := by
    apply (a.homEquiv _ _).symm.injective
    have hcomp : biprod.inl ≫ b₀.hom =
        T.map (ordinaryFiniteP1Unit A N hA t S hS) ≫
          ordinaryFiniteProjection A q E K := by
      simp [b₀, ← T.map_comp_assoc, D.decomposition_hom]
    rw [hcomp]
    simp only [Equiv.symm_apply_apply]
    change (a.homEquiv B₀ M).symm
      (T.map (ordinaryFiniteP1Unit A N hA t S hS) ≫
        ordinaryFiniteProjection A q E K) = e.hom
    have ht := tensorProjectionAdjunct A q K L E
      (ordinaryFiniteP1Unit A N hA t S hS)
    change (a.homEquiv B₀ M).symm
      (T.map (ordinaryFiniteP1Unit A N hA t S hS) ≫
        ordinaryFiniteProjection A q E K) = _ at ht
    rw [ht]
    have hu : P.map (ordinaryFiniteP1Unit A N hA t S hS) ≫ a.counit.app E =
        (ordinaryFiniteShiftedLinePullback A N hA t q hS).hom := by
      change (a.homEquiv L E).symm
        (a.homEquiv L E (ordinaryFiniteShiftedLinePullback A N hA t q hS).hom) = _
      exact (a.homEquiv L E).symm_apply_apply _
    change _ ≫ ((ordinaryFiniteTensor A (ProjectiveLine S)).obj (P.obj K)).map
      (P.map (ordinaryFiniteP1Unit A N hA t S hS) ≫ a.counit.app E) = _
    rw [hu]
    rfl
  have hPI : (P ⋙ I).IsEquivalence := by
    apply Functor.isEquivalence_of_iso (F := 𝟭 _)
    exact (Functor.isoWhiskerLeft P
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm ≪≫
      leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i q
        (ProjectiveLine.infinity_over (S := S))).symm
  let r := F.map (d.unit.app M)
  have hr : IsIso (biprod.inl ≫ b₀.hom ≫ r) := by
    rw [← Category.assoc, hb]
    exact section_unit_iso (P := P) (F := F) (I := I) (G := G) a d e
  obtain ⟨b, hbr, hbc⟩ := normalize_closed_coordinate r
    (D.adjunction.counit.app K) b₀ hr hc
  suffices htri : ∃ w, Triangle.mk
      (F.map ((affineTraceOpenAdjunction A S).counit.app M)) r w ∈ distTriang _ by
    obtain ⟨w, hw⟩ := htri
    exact ⟨F.obj (G.obj (I.obj M)), r, w, b, hw, hbr, hbc⟩
  have hi : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by
      rw [show i ≫ q = 𝟙 S from ProjectiveLine.infinity_over]
      infer_instance
    exact IsClosedImmersion.of_comp i q
  obtain ⟨v, hv⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} A) j i
    (ProjectiveLine.range_infinity S) M
  let z := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let e₁ := F.mapIso ((affineTraceOpenLeft A S).mapIso (z.app M))
  let w := F.map v ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫
    (shiftFunctor _ (1 : ℤ)).map e₁.inv
  refine ⟨w, isomorphic_distinguished _ (F.map_distinguished _ hv) _ ?_⟩
  refine Triangle.isoMk _ _ e₁ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change F.map ((affineTraceOpenAdjunction A S).counit.app M) ≫ 𝟙 _ =
      e₁.hom ≫ F.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app M)
    dsimp only [e₁, Functor.mapIso_hom, affineTraceOpenLeft, j]
    rw [Category.comp_id, ← F.map_comp]
    congr 1
    unfold affineTraceOpenAdjunction
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_inv]
    rfl
  · change r ≫ 𝟙 _ = 𝟙 _ ≫ F.map (d.unit.app M)
    simp [r]
  · change w ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom =
      𝟙 _ ≫ (F.map v ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
    dsimp only [w, affineTraceOpenLeft, j]
    simp only [Category.id_comp, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun f ↦ F.map v ≫ f) (Category.comp_id _)

end AlgebraicGeometry.Etale
