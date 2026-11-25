/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Exact countable sums compute derived coproducts

Source: Stacks Project, Derived Categories, Tag 0A5L, Lemma `lemma-direct-sums`,
statement and proof (blueprint: lem-kun-derived-countable-sums-exact).
-/

@[expose] public section

universe w v u t

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Fractions and coproducts of denominators give preservation of coproducts. -/
private theorem localizationPreservesCoproducts
    {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    (J : Type*) [HasCoproductsOfShape J C]
    (L : C ⥤ D) [L.Additive] (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [W.IsStableUnderCoproductsOfShape J] : PreservesColimitsOfShape (Discrete J) L := by
  classical
  have := Localization.essSurj L W
  have hz (K : J → C) (X : C) (a : ∐ K ⟶ X)
      (ha : ∀ j, L.map (Sigma.ι K j) ≫ L.map a = 0) : L.map a = 0 := by
    have h (j : J) : ∃ (Y : C) (s : Y ⟶ K j) (_ : W s), s ≫ (Sigma.ι K j ≫ a) = 0 := by
      have h := ha j
      rw [← L.map_comp, ← L.map_zero] at h
      obtain ⟨Y, s, hs, h⟩ := (MorphismProperty.map_eq_iff_precomp L W _ _).mp h
      exact ⟨Y, s, hs, by simpa using h⟩
    choose Y s hs h using h
    have hWs : W (Limits.Sigma.map s) :=
      W.colimMap (Discrete.natTrans (F := Discrete.functor Y) (G := Discrete.functor K)
        (fun j ↦ s j.as)) (fun j ↦ hs j.as)
    have : IsIso (L.map (Limits.Sigma.map s)) := Localization.inverts L W _ hWs
    apply (cancel_epi (L.map (Limits.Sigma.map s))).1
    rw [← L.map_comp]
    have he : Limits.Sigma.map s ≫ a = 0 := by
      ext j
      simpa using h j
    simp [he]
  have hzero (K : J → C) (X : C) (a : L.obj (∐ K) ⟶ L.obj X)
      (ha : ∀ j, L.map (Sigma.ι K j) ≫ a = 0) : a = 0 := by
    obtain ⟨φ, rfl⟩ := Localization.exists_leftFraction L W a
    have hφ (j : J) : L.map (Sigma.ι K j) ≫ L.map φ.f = 0 := by
      have := Localization.inverts L W φ.s φ.hs
      have h := ha j
      dsimp [MorphismProperty.LeftFraction.map] at h
      simpa only [← cancel_mono (L.map φ.s), Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, zero_comp] using h
    have := hz K φ.Y' φ.f hφ
    simp [MorphismProperty.LeftFraction.map, this]
  have hp (K : J → C) :
      Nonempty (IsColimit (L.mapCocone (colimit.cocone (Discrete.functor K)))) := by
    have hex (s : Cofan (fun j ↦ L.obj (K j))) :
        ∃ (a : L.obj (∐ K) ⟶ s.pt), ∀ j, L.map (Sigma.ι K j) ≫ a = s.inj j := by
      let e := L.objObjPreimageIso s.pt
      have h (j : J) := Localization.exists_rightFraction L W (s.inj j ≫ e.inv)
      choose φ hφ using h
      let g := Sigma.desc (fun j ↦ (φ j).f)
      let r := Limits.Sigma.map (fun j ↦ (φ j).s)
      have hr : W r :=
        W.colimMap (Discrete.natTrans
          (F := Discrete.functor (fun j ↦ (φ j).X')) (G := Discrete.functor K)
          (fun j ↦ (φ j.as).s)) (fun j ↦ (φ j.as).hs)
      have : IsIso (L.map r) := Localization.inverts L W _ hr
      refine ⟨inv (L.map r) ≫ L.map g ≫ e.hom, ?_⟩
      intro j
      have := Localization.inverts L W (φ j).s (φ j).hs
      apply (cancel_epi (L.map (φ j).s)).1
      have he : Sigma.ι (fun j ↦ (φ j).X') j ≫ r = (φ j).s ≫ Sigma.ι K j := by
        simp [r]
      rw [← Category.assoc, ← L.map_comp, ← he, L.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← L.map_comp_assoc]
      simp only [g, Sigma.ι_comp_desc]
      have h := congrArg (fun a ↦ L.map (φ j).s ≫ a ≫ e.hom) (hφ j)
      simpa [MorphismProperty.RightFraction.map, Category.assoc] using h.symm
    choose desc fac using hex
    have hcofan : IsColimit (Cofan.mk (L.obj (∐ K)) (fun j ↦ L.map (Sigma.ι K j))) :=
      Cofan.IsColimit.mk _ desc fac (by
        intro s m hm
        change ∀ j, L.map (Sigma.ι K j) ≫ m = s.inj j at hm
        let e := L.objObjPreimageIso s.pt
        apply (cancel_mono e.inv).1
        apply sub_eq_zero.mp
        apply hzero K (L.objPreimage s.pt)
        intro j
        simp only [Preadditive.comp_sub, ← Category.assoc, hm j, fac s j, sub_self])
    exact ⟨(isColimitMapCoconeCofanMkEquiv L K _).symm hcofan⟩
  have h (K : J → C) : PreservesColimit (Discrete.functor K) L :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit _) (hp K).some
  let := h
  exact preservesColimitsOfShape_of_discrete L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Coproduct preservation descends through an essentially surjective functor. -/
private theorem preservesCoproductsOfEssSurj
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {B : Type*} [Category* B] (J : Type*) [HasCoproductsOfShape J C]
    (q : C ⥤ D) [q.EssSurj] (H : D ⥤ B)
    [PreservesColimitsOfShape (Discrete J) q]
    [PreservesColimitsOfShape (Discrete J) (q ⋙ H)] :
    PreservesColimitsOfShape (Discrete J) H := by
  classical
  have h (E : J → D) : PreservesColimit (Discrete.functor E) H := by
    let K := fun j ↦ q.objPreimage (E j)
    let e : Discrete.functor K ⋙ q ≅ Discrete.functor E :=
      Discrete.natIso (fun j ↦ q.objObjPreimageIso (E j.as))
    have : PreservesColimit (Discrete.functor K ⋙ q) H :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves q (colimit.isColimit (Discrete.functor K)))
        (isColimitOfPreserves (q ⋙ H) (colimit.isColimit (Discrete.functor K)))
    exact preservesColimit_of_iso_diagram H e
  let := h
  exact preservesColimitsOfShape_of_discrete H

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The coproduct comparison conjugates a coproduct of morphisms. -/
private theorem isIsoMapCoproduct
    {C : Type*} [Category* C] {B : Type*} [Category* B]
    (J : Type*) [HasCoproductsOfShape J C] [HasCoproductsOfShape J B]
    (H : C ⥤ B) [PreservesColimitsOfShape (Discrete J) H]
    (K M : J → C) (f : ∀ j, K j ⟶ M j) [∀ j, IsIso (H.map (f j))] :
    IsIso (H.map (Limits.Sigma.map f)) := by
  have he : H.map (Limits.Sigma.map f) =
      (PreservesCoproduct.iso H K).hom ≫ Limits.Sigma.map (fun j ↦ H.map (f j)) ≫
        (PreservesCoproduct.iso H M).inv := by
    apply (cancel_epi (PreservesCoproduct.iso H K).inv).1
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply colimit.hom_ext
    rintro ⟨j⟩
    change Sigma.ι _ j ≫ ((PreservesCoproduct.iso H K).inv ≫ H.map (Limits.Sigma.map f)) =
      Sigma.ι _ j ≫ (Limits.Sigma.map (fun j ↦ H.map (f j)) ≫
        (PreservesCoproduct.iso H M).inv)
    simp only [PreservesCoproduct.inv_hom, ← Category.assoc, ι_comp_sigmaComparison,
      Limits.Sigma.ι_map, ← H.map_comp]
    rw [Category.assoc, ι_comp_sigmaComparison, ← H.map_comp]
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Degreewise coproducts descend to the homotopy category. -/
private theorem quotientPreservesCoproducts
    (A : Type u) [Category.{v} A] [Abelian A]
    (J : Type*) [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J) (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have h (K : J → CochainComplex A ℤ) : PreservesColimit (Discrete.functor K) q := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    exact (isColimitMapCoconeCofanMkEquiv q K _).symm
      (HomotopyCategory.isColimitCofanQuotient (coproductIsCoproduct K))
  let := h
  exact preservesColimitsOfShape_of_discrete q

/-- In an abelian category with exact countable coproducts, the termwise coproduct
of unbounded cochain complexes, with the images of its specified coprojections, is
also a coproduct in the derived category. The index type may be empty and may lie
in any universe. The termwise complex and its differential are the actual
construction `HomologicalComplex.coconeOfHasColimitEval`.

Source: Stacks Project, Derived Categories, Tag 0A5L, Lemma `lemma-direct-sums`
(blueprint: lem-kun-derived-countable-sums-exact).

Proof plan:
1. Form sums degreewise. The universal property induces the differential, whose
square is zero by checking every coprojection. Chain maps and homotopies out of
this complex assemble degreewise, so it is a coproduct in the homotopy category.
2. Sum the short exact sequences for cycles, boundaries and cohomology. Exactness
identifies the cohomology of the sum with the sum of the cohomologies, naturally
in chain maps. Thus countable sums of quasi-isomorphisms are quasi-isomorphisms;
quasi-isomorphisms also satisfy two-out-of-three.
3. By `lem-pc-quasi-isomorphisms-multiplicative-system` and
`lem-pc-right-fraction-representation`, represent each derived map by a roof.
Sum the denominators and assemble the numerators. Step 2 inverts the summed
denominator, giving a map with the desired restrictions. Every derived target
is represented by a complex.
4. By `lem-pc-right-fraction-common-refinement`, equality of localized maps from
the homotopy category can be witnessed after precomposition by a quasi-isomorphism:
apply common refinement to roofs with identity denominators.
5. For uniqueness, put two roofs out of the sum over a common denominator using
the right-calculus square axiom; two-out-of-three makes both refinements valid.
6. Apply the square axiom to each coprojection and the common denominator. Equal
restrictions and step 4 give componentwise refinements on which the numerators
agree and whose maps to the original summands are quasi-isomorphisms.
7. Sum these refinements, including the homotopies witnessing their equations.
The summed map to the original sum is a quasi-isomorphism by step 2. Hence its
factor to the common denominator is one by two-out-of-three. Cancel its image
to obtain equality of the localized numerators and therefore of the two maps.
8. These existence and uniqueness assertions are the coproduct universal property.
For an empty family the termwise sums are zero objects. The empty summed
denominators are maps between zero complexes, hence isomorphisms; the same
argument includes the empty coproduct, without any boundedness assumption. -/
theorem isColimit_mapCocone_countableSum
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (I : Type w) [Countable I] (K : I → CochainComplex A ℤ) :
    Nonempty (IsColimit ((Q (C := A)).mapCocone
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)))) := by
  classical
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hq : PreservesColimitsOfShape (Discrete I) q := quotientPreservesCoproducts A I
  have hhas (E : I → HomotopyCategory A (ComplexShape.up ℤ)) : HasCoproduct E := by
    let M := fun i ↦ q.objPreimage (E i)
    let e : Discrete.functor E ≅ Discrete.functor M ⋙ q :=
      Discrete.natIso (fun i ↦ (q.objObjPreimageIso (E i.as)).symm)
    exact hasColimit_of_iso e
  let : HasCoproductsOfShape I (HomotopyCategory A (ComplexShape.up ℤ)) :=
    { has_colimit F := by
        have := hhas (fun i ↦ F.obj ⟨i⟩)
        exact hasColimit_of_iso Discrete.natIsoFunctor }
  have : Countable (Shrink.{0} I) := Countable.of_equiv _ (equivShrink.{0} I)
  have : HasExactColimitsOfShape (Discrete I) A :=
    HasExactColimitsOfShape.of_domain_equivalence A
      (Discrete.equivalence (equivShrink.{0} I)).symm
  have hH (p : ℤ) : PreservesColimitsOfShape (Discrete I)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p) := by
    have : PreservesColimitsOfShape (Discrete I)
        (q ⋙ HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p) :=
      preservesColimitsOfShape_of_natIso
        (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) p).symm
    exact preservesCoproductsOfEssSurj I q _
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have : W.IsStableUnderCoproductsOfShape I :=
    MorphismProperty.IsStableUnderCoproductsOfShape.mk W I (by
      intro M N _ _ f hf
      change HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (Limits.Sigma.map f)
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro p
      let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p
      have := hH p
      have (i : I) : IsIso (H.map (f i)) :=
        (HomotopyCategory.mem_quasiIso_iff (f i)).mp (hf i) p
      exact isIsoMapCoproduct I H M N f)
  have := localizationPreservesCoproducts I (Qh (C := A)) W
  have : PreservesColimitsOfShape (Discrete I) (q ⋙ Qh) := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (Q (C := A)) :=
    preservesColimitsOfShape_of_natIso (quotientCompQhIso A)
  exact ⟨isColimitOfPreserves Q
    (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor K))⟩

end DerivedCategory
