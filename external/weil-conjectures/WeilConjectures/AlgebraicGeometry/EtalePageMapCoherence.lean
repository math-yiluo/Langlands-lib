/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology

/-! # Coherence of the unswapped étale page maps

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-etale-page-map-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem apply_eq_index {A : Sort*} {B : A → Sort*} {R : Sort*}
    (m : ∀ a, B a → R) {a b : A} (h : a = b)
    (v : ∀ a, a = b → B a) : m a (v a h) = m b (v b rfl) := by
  subst a
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent inverse-image and spectral-page map families.
set_option linter.unusedVariables false in
/-- The supplied pullback page maps obey diagram and cocone equations.
Source: Stacks Project, Tag 015J (functorial hypercohomology), Tag 015K
(comparison maps), and Tag 0EZM (inverse-system comparison).

Proof: For identity maps, transport M across D.map_id, substitute hidentity,
and apply hid. The extra identity-complex comparison is componentwise identity.
For composition, transport M across D.map_comp, substitute hcomposition,
and apply hcomp. The composition-complex inverse comparison in hcomp is the
same componentwise map as the displayed NatIso.mapHomologicalComplex comparison.
For cocone compatibility, apply hcomp to D.map f and c.π.app j, then transport
along c.w f. Its complex map is
upperStarComp.hom followed by the pullback of φ f followed by (eG j).inv and
L.ι.app (op j). Substitute hG, cancel (eG i).inv with (eG i).hom, and use
L.w f.op. This gives precisely (eG i).inv followed by L.ι.app (op i).
All transports are equality transports of scheme arrows with fixed endpoints;
prove their compatibility with M by equality induction. No choices of
presentations, page objects, or comparison maps are made here.
(blueprint: lem-weil-pbc-etale-page-map-coherence). -/
theorem etale_page_map_coherence
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hFK : ∀ i : I, CochainComplex.plus
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (F i))
    (hLK : CochainComplex.plus
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) L.pt)
    (T₀ : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (T₀ X K).sequence ⟶ (T₀ Y L).sequence)
    (hid : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (T₀ X K).sequence)
    (hcomp : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w) :
    (∀ i : I,
      M (D.map (𝟙 i)) ⟨F i, hFK i⟩ ⟨F i, hFK i⟩ (φ (𝟙 i)) =
        𝟙 (T₀ (D.obj i) ⟨F i, hFK i⟩).sequence) ∧
    (∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      M (D.map (g ≫ f)) ⟨F i, hFK i⟩ ⟨F k, hFK k⟩ (φ (g ≫ f)) =
        M (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f) ≫
          M (D.map g) ⟨F j, hFK j⟩ ⟨F k, hFK k⟩ (φ g)) ∧
    (∀ (i j : I) (f : j ⟶ i),
      M (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f) ≫
        M (c.π.app j) ⟨F j, hFK j⟩ ⟨L.pt, hLK⟩
          ((eG j).inv ≫ L.ι.app (op j)) =
      M (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
        ((eG i).inv ≫ L.ι.app (op i))) := by
  have identity_law (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (a : X ⟶ X) (ha : a = 𝟙 X) :
      M a K K
        ((NatIso.mapHomologicalComplex
          (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) ha))
          (ComplexShape.up ℤ)).hom.app K.obj ≫
        (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
          (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (T₀ X K).sequence := by
    refine (apply_eq_index (fun a v ↦ M a K K v) ha (fun a ha ↦
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) ha))
        (ComplexShape.up ℤ)).hom.app K.obj ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
        (ComplexShape.up ℤ)).hom.app K.obj)).trans ?_
    have hrefl : (NatIso.mapHomologicalComplex
        (Iso.refl (upperStar AddCommGrpCat.{u + 1} (𝟙 X)))
        (ComplexShape.up ℤ)).hom.app K.obj = 𝟙 _ := by
      change (NatTrans.mapHomologicalComplex (𝟙 _) _).app _ = _
      rw [NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
    erw [hrefl, Category.id_comp]
    have hunit : (Functor.mapHomologicalComplexIdIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ)).hom.app K.obj = 𝟙 _ := rfl
    simpa only [Iso.trans_hom, NatTrans.comp_app, hunit, Category.comp_id] using hid X K
  have composition_law {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
      (a : Z ⟶ X) (ha : a = g ≫ f)
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (J : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K.obj ⟶ J.obj)
      (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J.obj ⟶ N.obj) :
      M a K N
        ((NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} g f a ha)
          (ComplexShape.up ℤ)).hom.app K.obj ≫
          ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map v ≫ w) = M f K J v ≫ M g J N w := by
    exact (apply_eq_index (fun a v ↦ M a K N v) ha (fun a ha ↦
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} g f a ha)
        (ComplexShape.up ℤ)).hom.app K.obj ≫
      ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).map v ≫ w)).trans (hcomp f g K J N v w)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hidentity i]
    exact identity_law (D.obj i) ⟨F i, hFK i⟩ _ (D.map_id i)
  · intro i j k f g
    rw [hcomposition i j k f g]
    exact composition_law (D.map f) (D.map g) _ (D.map_comp g f)
      ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ ⟨F k, hFK k⟩ (φ f) (φ g)
  · intro i j f
    rw [← composition_law (D.map f) (c.π.app j) (c.π.app i) (c.w f).symm
      ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ ⟨L.pt, hLK⟩ (φ f)
      ((eG j).inv ≫ L.ι.app (op j))]
    apply congrArg (M (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩)
    have hw := congrArg (fun t ↦ (eG i).inv ≫ t) (L.w f.op)
    rw [hG i j f] at hw
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hw

end AlgebraicGeometry.Etale
