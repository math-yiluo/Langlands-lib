/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleUnionSESChainData

/-! # Short exact presentations of the single-module union comparison

Source: Stacks Project, Tags 08BV, 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open CochainComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
variable {C : Type u} [Category C] [Abelian C]
variable {A B A' B' : CochainComplex C ℤ}

private abbrev cyl (_t : A ⟶ B) := B ⊞ mappingCone (𝟙 A)
private def cylI (t : A ⟶ B) : A ⟶ cyl t := biprod.lift t (mappingCone.inr (𝟙 A))
private def cylQ (t : A ⟶ B) : cyl t ⟶ mappingCone t :=
  biprod.desc (mappingCone.inr t) (-mappingCone.map (𝟙 A) t (𝟙 A) t (by simp))
private lemma cyl_zero (t : A ⟶ B) : cylI t ≫ cylQ t = 0 := by
  dsimp [cylI, cylQ]
  simp only [biprod.lift_desc, Preadditive.comp_neg]
  have h := (mappingCone.triangleMap (𝟙 A) t (𝟙 A) t (by simp)).comm₂
  change mappingCone.inr (𝟙 A) ≫
    mappingCone.map (𝟙 A) t (𝟙 A) t (by simp) = t ≫ mappingCone.inr t at h
  rw [h, add_neg_cancel]
private def cylRow (t : A ⟶ B) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (cylI t) (cylQ t) (cyl_zero t)

private lemma cyl_exact (t : A ⟶ B) : (cylRow t).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (cyl t).X n ⟶ A.X n :=
    (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n ≫
      (mappingCone.snd (𝟙 A)).v n n (by omega)
  let s : (mappingCone t).X n ⟶ (cyl t).X n :=
    (mappingCone.snd t).v n n (by omega) ≫ (biprod.inl : B ⟶ cyl t).f n -
      (mappingCone.fst t).1.v n (n + 1) rfl ≫
        (mappingCone.inl (𝟙 A)).v (n + 1) n (by omega) ≫
          (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }
  · change (cylI t).f n ≫ r = 𝟙 _
    dsimp only [r]
    rw [← Category.assoc, ← HomologicalComplex.comp_f]
    simp only [cylI, biprod.lift_snd, mappingCone.inr_f_snd_v]
  · change s ≫ (cylQ t).f n = 𝟙 _
    apply mappingCone.ext_from t (n + 1) n rfl
    all_goals dsimp only [s]
    all_goals simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      Category.comp_id, zero_comp, sub_zero, zero_sub]
    all_goals simp only [← HomologicalComplex.comp_f, cylQ, biprod.inl_desc, biprod.inr_desc]
    all_goals simp [mappingCone.map]
  · change r ≫ (cylI t).f n + (cylQ t).f n ≫ s = 𝟙 _
    have hlq : (biprod.inl : B ⟶ cyl t).f n ≫ (cylQ t).f n =
        (mappingCone.inr t).f n := by
      rw [← HomologicalComplex.comp_f]
      simp only [cylQ, biprod.inl_desc]
    have hrq : (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫ (cylQ t).f n =
        -(mappingCone.map (𝟙 A) t (𝟙 A) t (by simp)).f n := by
      rw [← HomologicalComplex.comp_f]
      simp only [cylQ, biprod.inr_desc, HomologicalComplex.neg_f_apply]
    have hlr : (biprod.inl : B ⟶ cyl t).f n ≫
        (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
    have hrr : (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
        (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
    let F := HomologicalComplex.eval C (.up ℤ) n
    apply (cancel_epi (F.mapBiprod B (mappingCone (𝟙 A))).inv).mp
    apply biprod.hom_ext'
    · simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, Preadditive.comp_add]
      change (biprod.inl : B ⟶ cyl t).f n ≫ r ≫ (cylI t).f n +
        (biprod.inl : B ⟶ cyl t).f n ≫ (cylQ t).f n ≫ s =
          (biprod.inl : B ⟶ cyl t).f n ≫ 𝟙 _
      dsimp only [r, s]
      simp only [Category.assoc, reassoc_of% hlr, zero_comp, zero_add,
        reassoc_of% hlq]
      simp
    · simp only [Functor.mapBiprod_inv, biprod.inr_desc_assoc, Preadditive.comp_add]
      change (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
        r ≫ (cylI t).f n + (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
          (cylQ t).f n ≫ s = (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫ 𝟙 _
      dsimp only [r]
      simp only [Category.assoc, reassoc_of% hrr,
        reassoc_of% hrq]
      apply mappingCone.ext_from (𝟙 A) (n + 1) n rfl
      all_goals dsimp only [s]
      all_goals simp [mappingCone.map, Category.assoc, cylI, biprod.lift_eq]

section
variable [HasDerivedCategory.{w} C]
private def cylIso (t : A ⟶ B) : DerivedCategory.Q.obj (cyl t) ≅ DerivedCategory.Q.obj B where
  hom := DerivedCategory.Q.map biprod.fst
  inv := DerivedCategory.Q.map biprod.inl
  hom_inv_id := by
    have hz : DerivedCategory.Q.map (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t) = 0 := by
      have h₀ := DerivedCategory.Q_map_eq_of_homotopy C
        (mappingCone.homotopyToZeroOfId A)
      have h := congrArg
        (fun k ↦ k ≫ DerivedCategory.Q.map (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t)) h₀
      simpa using h
    have h := congrArg (fun k ↦ DerivedCategory.Q.map k)
      (biprod.total (X := B) (Y := mappingCone (𝟙 A)))
    simp only [Functor.map_add, Functor.map_comp, CategoryTheory.Functor.map_id, hz,
      comp_zero, add_zero] at h
    exact h
  inv_hom_id := by rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]

end

private def cylMap (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B') :
    cyl t ⟶ cyl t' :=
  biprod.map β (mappingCone.map (𝟙 A) (𝟙 A') α α (by simp))

private def cylRowMap (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t') : cylRow t ⟶ cylRow t' where
  τ₁ := α
  τ₂ := cylMap t t' α β
  τ₃ := mappingCone.map t t' α β hc
  comm₁₂ := by
    change α ≫ cylI t' = cylI t ≫ cylMap t t' α β
    symm
    apply biprod.hom_ext
    · simp [cylI, cylMap, Category.assoc, hc]
    · dsimp only [cylI, cylMap]
      simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      rw [biprod.lift_snd]
      exact (mappingCone.triangleMap (𝟙 A) (𝟙 A') α α (by simp)).comm₂
  comm₂₃ := by
    change cylMap t t' α β ≫ cylQ t' = cylQ t ≫ mappingCone.map t t' α β hc
    apply biprod.hom_ext'
    · dsimp only [cylMap, cylQ]
      simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (mappingCone.triangleMap t t' α β hc).comm₂.symm
    · dsimp only [cylMap, cylQ]
      simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      congr 1
      rw [← mappingCone.map_comp, ← mappingCone.map_comp]
      simp only [Category.id_comp, Category.comp_id, hc]

/-- Turn a strict cone comparison into a comparison of short exact cylinder rows. -/
private lemma cyl_presentation [HasDerivedCategory.{w} C]
    (a b c : Arrow (DerivedCategory C))
    (h : ∃ (A B A' B' : CochainComplex C ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B'),
      ∃ (hc : t ≫ β = α ≫ t')
        (e₁ : DerivedCategory.Q.obj A ≅ a.left)
        (e₂ : DerivedCategory.Q.obj B ≅ b.left)
        (e₃ : DerivedCategory.Q.obj (mappingCone t) ≅ c.left)
        (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj B' ≅ b.right)
        (e₃' : DerivedCategory.Q.obj (mappingCone t') ≅ c.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ b.hom ∧
        DerivedCategory.Q.map (mappingCone.map t t' α β hc) ≫ e₃'.hom =
          e₃.hom ≫ c.hom) :
    ∃ (P P' : ShortComplex (CochainComplex C ℤ)) (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ b.left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ c.left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ b.right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ c.right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = e₂.hom ≫ b.hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ c.hom := by
  classical
  obtain ⟨A, B, A', B', t, t', α, β, hc, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ := h
  refine ⟨cylRow t, cylRow t', cylRowMap t t' α β hc,
    (Iso.refl _) ≪≫ e₁, cylIso t ≪≫ e₂, (Iso.refl _) ≪≫ e₃,
    (Iso.refl _) ≪≫ e₁', cylIso t' ≪≫ e₂', (Iso.refl _) ≪≫ e₃',
    cyl_exact t, cyl_exact t', ?_, ?_, ?_⟩
  · simpa only [cylRowMap, cylRow, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp] using hα
  · have h : DerivedCategory.Q.map (cylMap t t' α β) ≫ (cylIso t').hom =
        (cylIso t).hom ≫ DerivedCategory.Q.map β := by
      dsimp only [cylIso]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp [cylMap]
    simpa only [cylRowMap, Iso.trans_hom, Category.assoc, hβ] using
      congrArg (fun k ↦ k ≫ e₂'.hom) h
  · simpa only [cylRowMap, cylRow, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp] using hγ

end

/-- The three canonical comparisons are obtained from a morphism of short exact
complexes, after identifying their localized vertices. No comparison is asserted
invertible. The coefficients need not be quasi-coherent or relatively flat, and
there is no compactness assumption on the two opens.

Source: Stacks Project, Tags 08BV (the injective restriction-difference sequence),
08FE (restriction of direct image), 08HY (the base-change map), and 0DJ9
(the relative Mayer--Vietoris induction diagram); Tags 013N--013O for cylinders.
(blueprint: new-pc-standard-single-union-ses-presentation).

Proof:
Work on W = U union V and on its base change W_A. Resolve N[0] and its ordinary
pullback in degree zero by K-injective complexes with injective terms. The opens
induced by U,V cover W, and their inverse images cover W_A. Apply
schemeKInjective_mayerVietoris_presentation to these covers. Sheaf gluing gives
exactness at the first two terms of each restriction-difference sequence;
flasqueness of injectives gives surjectivity at the overlap. Thus the rows are
short exact without compactness or quasi-coherent direct-image assumptions.
Apply derived direct image to the rows and derived pullback to the source row.
Use diagram resolutions to represent these derived functors and the comparison
on complexes. Transpose the ordinary pullback map under the derived adjunction.
Naturality of the restriction units makes the first square commute; subtraction
of the two restriction squares gives the second square. The degreewise identity
schemeMVUnderivedOpenCounit_square makes this a comparison of the cover diagrams.
Use the functorial mapping cylinder of the first differential to obtain a strict
morphism of short exact rows: for a chain map t:C -> D, the row
C -> D direct-sum Cone(id C) -> Cone(t) is degreewise split exact, and its
contractible summand disappears after localization. Homotopy-commuting squares
are made strict by their specified homotopies in this cylinder construction.
The cone comparison from the cover rows identifies the third term with the
derived direct image on the overlap. This produces P,P' and m as in the statement.
Transport the localized vertices by direct-image composition and exact open
restriction. Additivity gives the two biproduct comparisons. Tensor pullback
along an open inclusion is exact restriction, so these coefficient restrictions
are the literal tensorPullbackObj terms displayed here. Expand the canonical
base-change comparison as the mate of the pulled-back direct-image counit.
The composite-counit identity and the adjunction triangle identities identify
the union and overlap components with standardSingleBaseChangeMap, and the
middle component with the biproduct of the two member maps. These give the three
conjugacy equations. The cylinder step is before forming any boundary map;
no distinguishedness or connecting-square assertion is assumed in this lemma.
For an empty open the corresponding complexes are zero; identical or contained
opens give split restriction rows. The construction applies unchanged to zero
coefficients. The existential witnesses here do not define library data. -/
theorem standardSingle_union_ses_presentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ aU.left ⊞ aV.left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ aUV.left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ aU.right ⊞ aV.right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ aUV.right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ aUV.hom := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact cyl_presentation (Arrow.mk _) (Arrow.mk _) (Arrow.mk _)
    (standardSingle_union_ses_chain_data p g U V N)

end AlgebraicGeometry
