/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedModuleTensorTransport
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # The tensor comparison for completed coefficient and site transport

Source: Stacks Project, algebraization.tex, Tag 0A0E, with Modules on Sites, Tags 03DA and 03EK.
(blueprint: lem-weil-pbc-completed-cech-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open MonoidalCategory

private theorem tensor_unit_iso_cancel
    {D : Type*} [Category* D] [MonoidalCategory D]
    {M M' U T Q : D} (z : M ≅ M') (c : 𝟙_ D ⟶ U) (b : U ⟶ T)
    (i : M ⊗ T ⟶ Q) :
    z.hom ≫ (ρ_ M').inv ≫ M' ◁ c ≫ M' ◁ b ≫ z.inv ▷ T ≫ M ◁ 𝟙 T ≫ i =
      (ρ_ M).inv ≫ M ◁ (c ≫ b) ≫ i := by
  rw [← whiskerLeft_comp_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]
  simp only [Iso.hom_inv_id_assoc, whiskerLeft_id, Category.id_comp]

private theorem tensor_transport_unit_component
    {B D : Type*} [Category* B] [Category* D] [Preadditive B] [Preadditive D]
    [MonoidalCategory B] [MonoidalCategory D]
    [(curriedTensor B).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor B).obj M).PreservesZeroMorphisms]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} B] [HasColimitsOfSize.{0, 0} D]
    (F : B ⥤ D) [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor B) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (c : 𝟙_ D ⟶ F.obj (𝟙_ B))
    (P K : CochainComplex B ℤ) (N : CochainComplex D ℤ)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ N)
    (q : ℤ) (b : 𝟙_ B ⟶ K.X 0) (z : N.X q ≅ F.obj (P.X q))
    (hz : v.hom.f q = z.inv)
    (hτ : F.map (ρ_ (P.X q)).inv ≫ (τ.hom.app (P.X q)).app (𝟙_ B) =
      (ρ_ (F.obj (P.X q))).inv ≫ F.obj (P.X q) ◁ c) :
    z.hom ≫ F.map ((ρ_ (P.X q)).inv ≫ P.X q ◁ b ≫
      HomologicalComplex.ιMapBifunctor P K (curriedTensor B) (.up ℤ)
        q 0 q (add_zero q)) ≫
      (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) P K ≫
        HomologicalComplex.mapBifunctorMap v.hom
          (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K)) (curriedTensor D) (.up ℤ)).f q =
      (ρ_ (N.X q)).inv ≫ N.X q ◁ (c ≫ F.map b) ≫
        HomologicalComplex.ιMapBifunctor N ((F.mapHomologicalComplex (.up ℤ)).obj K)
          (curriedTensor D) (.up ℤ) q 0 q (add_zero q) := by
  have hn := (τ.hom.app (P.X q)).naturality b
  change F.map (P.X q ◁ b) ≫ (τ.hom.app (P.X q)).app (K.X 0) =
    (τ.hom.app (P.X q)).app (𝟙_ B) ≫ F.obj (P.X q) ◁ F.map b at hn
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  rw [HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map, hz]
  dsimp only [HomologicalComplex.mapBifunctorComparisonApp]
  rw [reassoc_of% hn, reassoc_of% hτ]
  exact tensor_unit_iso_cancel z c (F.map b) _

attribute [local irreducible] completedCechModulesEquiv intrinsicPresentationRoundTrip
  pbcCompletedComparison

-- Elaborate the unbounded tensor comparison across the two coefficient models.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient restriction and site transport commute with total tensor and its unit.

Source: Stacks Project, Modules on Sites, Tags 03DA and 03EK; algebraization.tex,
Tag 0A0E, the finite-free tensor calculation after coefficient and site transport.
(blueprint: lem-weil-pbc-completed-cech-tensor-transport).

Proof: take the ordinary module bifunctor comparison and its right-unit
normalization from completedCechModuleTensorTransport. The coefficient-back functor
and site functor are equivalences, so their composite preserves the coproducts in
totalization. Apply HomologicalComplex.mapBifunctorComparisonNatTrans; the existing
comparison is natural in both complexes and respects both differentials and their
Koszul signs. Map the inverse of intrinsicPresentationRoundTrip degreewise to
identify the first transported factor with G(C), then tensor with this chain
isomorphism. For the displayed equation, expand completedKoszulTensorUnit into the
inverse right unitor, tensoring with the named degree-zero unit, and the (q,0)
summand inclusion. The comparison's summand formula and naturality in the unit
reduce this to the ordinary right-unit normalization. Whisker exchange and
right-unitor naturality move the inverse round trip to its round trip, which
cancels. The remaining composite is exactly the prescribed (q,0) inclusion.
No exterior-to-dual comparison, boundedness assumption, or choice of a replacement
complex is involved. The formula also holds for zero modules and the zero ring. -/
theorem completedCechTensorTransport
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients
      (adicDatumRing X (intrinsicPresentationDatum d))
    letI := SheafOfModules.monoidalCategory (adicDatumRing X (intrinsicPresentationDatum d))
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (adicDatumRing X (intrinsicPresentationDatum d))
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (adicDatumRing X (intrinsicPresentationDatum d))
    let G := (completedCechModulesEquiv X d).functor
    let F := intrinsicPresentationModulesBack X d ⋙ G
    let H := F.mapHomologicalComplex (.up ℤ)
    let P := (intrinsicPresentationComplex X d).obj C
    let O := completedCechRing X d
    let N := (G.mapHomologicalComplex (.up ℤ)).obj C
    let L := ((curriedTensor _).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P ⋙ H
    let R := H ⋙ (ringedKoszulTensor O).obj N
    ∃ e : L ≅ R,
      ∀ (r : ℕ) (a : Fin r → A) (m : ℕ) (q : ℤ),
        G.map ((intrinsicPresentationRoundTrip X d).hom.app (C.X q) ≫
          (intrinsicPresentationModulesBack X d).map
            ((completedKoszulTensorUnit X (intrinsicPresentationDatum d) r a P m).f q)) ≫
          (e.hom.app (completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a m)).f q =
        letI := SheafOfModules.monoidalCategory O
        (ρ_ (N.X q)).inv ≫ N.X q ◁
          (completedCechCoefficientUnit X d ≫ F.map
            (completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m)) ≫
          HomologicalComplex.ιMapBifunctor N
            (H.obj (completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a m))
            (curriedTensor _) (.up ℤ) q 0 q (add_zero q) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (adicDatumRing X (intrinsicPresentationDatum d))
  let := SheafOfModules.monoidalCategory (adicDatumRing X (intrinsicPresentationDatum d))
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (adicDatumRing X (intrinsicPresentationDatum d))
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (adicDatumRing X (intrinsicPresentationDatum d))
  let := SheafOfModules.monoidalCategory (completedCechRing X d)
  let G := (completedCechModulesEquiv X d).functor
  let F := intrinsicPresentationModulesBack X d ⋙ G
  let H := F.mapHomologicalComplex (.up ℤ)
  let P := (intrinsicPresentationComplex X d).obj C
  let N := (G.mapHomologicalComplex (.up ℤ)).obj C
  let η := intrinsicPresentationRoundTrip X d
  have : (intrinsicPresentationModulesBack X d).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (pbcCompletedComparison X d).symm)).functor.IsEquivalence
  have : F.IsEquivalence := by dsimp [F]; infer_instance
  obtain ⟨τ, hτ⟩ := completedCechModuleTensorTransport X d
  let v : H.obj P ≅ N := HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ G.mapIso (η.app (C.X q)).symm) (by
      intro p q hpq
      change G.map (η.inv.app (C.X p)) ≫ G.map (C.d p q) =
        G.map ((intrinsicPresentationModulesBack X d).map
          ((intrinsicPresentationModules X d).map (C.d p q))) ≫
          G.map (η.inv.app (C.X q))
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (η.inv.naturality (C.d p q)).symm)
  let T := (curriedTensor (SheafOfModules.{u + 1}
    ((sheafCompose (completedCechTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d)))).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let t := (asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
    (c₁ := .up ℤ) (c₂ := .up ℤ) τ.hom (.up ℤ))).app P
  let e := t ≪≫ Functor.isoWhiskerLeft H (T.mapIso v)
  refine ⟨e, ?_⟩
  intro r a m q
  let K := completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a m
  let b := completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m
  let z := G.mapIso (η.app (C.X q))
  rw [G.map_comp, Category.assoc]
  exact tensor_transport_unit_component F τ (completedCechCoefficientUnit X d)
    P K N v q b z rfl (hτ (P.X q))

end AlgebraicGeometry.Scheme
