/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.AlgebraicGeometry.DerivedPullbackEvaluationSections

/-! # Evaluation mate and its zeroth hypercohomology

Source: Stacks Project, Cohomology, Remark 08I3 and Lemmas 079W, 08DJ
(blueprint: lem-pc-derived-internal-hom-pullback-mate-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def tensorHomAdjunction
    {C : Type*} [Category C] [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    (e : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (he : ∀ (A A' K K' L L' : C) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ H.obj (op K, L)),
      e A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e A K L f ≫ c)
    (K : C) : tensorRight K ⊣ (Functor.curry.obj H).obj (op K) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A L ↦ (e A K L).symm
      homEquiv_naturality_left_symm := by
        intro A' A L a f
        have h := he A A' K K L L a (𝟙 K) (𝟙 L) f
        change e A' K L (a ≫ f ≫ H.map (𝟙 _)) = _ at h
        simpa using h
      homEquiv_naturality_right := by
        intro A L L' f c
        apply (e A K L').injective
        have h := he A A K K L L' (𝟙 A) (𝟙 K) c ((e A K L).symm f)
        simpa using h.symm }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorHomAdjunction_homEquiv
    {C : Type*} [Category C] [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    (e : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (he : ∀ (A A' K K' L L' : C) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ H.obj (op K, L)),
      e A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e A K L f ≫ c)
    (A K L : C) :
    (tensorHomAdjunction H e he K).homEquiv A L = (e A K L).symm := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) A) L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorHomAdjunction_counit
    {C : Type*} [Category C] [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    (e : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (he : ∀ (A A' K K' L L' : C) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ H.obj (op K, L)),
      e A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e A K L f ≫ c)
    (K L : C) : (tensorHomAdjunction H e he K).counit.app L = e _ K L (𝟙 _) := by
  rw [← Adjunction.homEquiv_symm_id]
  simp only [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_naturality
    {C : Type*} [Category C] [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    (e : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (he : ∀ (A A' K K' L L' : C) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ H.obj (op K, L)),
      e A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e A K L f ≫ c)
    {K K' L L' : C} (b : K' ⟶ K) (c : L ⟶ L') :
    (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c) ⊗ₘ 𝟙 K') ≫ e _ K' L' (𝟙 _) =
      (𝟙 _ ⊗ₘ b) ≫ e _ K L (𝟙 _) ≫ c := by
  have h₁ := he _ _ K' K' L' L'
    (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)) (𝟙 K') (𝟙 L') (𝟙 _)
  have h₂ := he _ _ K K' L L' (𝟙 _) b c (𝟙 _)
  change e _ K' L' (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c) ≫
    𝟙 _ ≫ H.map (𝟙 _)) = _ at h₁
  rw [H.map_id] at h₁
  simp only [Category.comp_id] at h₁
  simp only [Category.id_comp] at h₂
  exact h₁.symm.trans h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackEvaluationMate_exists
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R) (m : F.CoreMonoidal)
    (e : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (q : ∀ A K L : D, (A ⟶ J.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (he : ∀ (A A' K K' L L' : C) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ H.obj (op K, L)),
      e A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e A K L f ≫ c)
    (hq : ∀ (A A' K K' L L' : D) (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
      (f : A ⟶ J.obj (op K, L)),
      q A' K' L' (a ≫ f ≫ J.map (b.op, c)) = (a ⊗ₘ b) ≫ q A K L f ≫ c) :
    ∃ γ : H ⟶ F.op.prod F ⋙ J ⋙ R,
      ∀ K L : C, γ.app (op K, L) =
        a.homEquiv _ _ ((q _ (F.obj K) (F.obj L)).symm
          ((m.μIso _ K).hom ≫ F.map (e _ K L (𝟙 _)))) := by
  let d (K L : C) := (q _ (F.obj K) (F.obj L)).symm
    ((m.μIso _ K).hom ≫ F.map (e _ K L (𝟙 _)))
  have dn {K K' L L' : C} (b : K' ⟶ K) (c : L ⟶ L') :
      F.map (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)) ≫ d K' L' =
        d K L ≫ J.map ((F.map b).op, F.map c) := by
    apply (q _ (F.obj K') (F.obj L')).injective
    have h₁ := hq _ _ _ _ _ _ (F.map (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)))
      (𝟙 (F.obj K')) (𝟙 (F.obj L')) (d K' L')
    have h₂ := hq _ _ _ _ _ _ (𝟙 _) (F.map b) (F.map c) (d K L)
    change q _ (F.obj K') (F.obj L')
      (F.map (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)) ≫
        d K' L' ≫ J.map (𝟙 _)) = _ at h₁
    rw [J.map_id] at h₁
    simp only [Category.comp_id] at h₁
    simp only [Category.id_comp] at h₂
    rw [h₁, h₂]
    dsimp only [d]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    let := m.toMonoidal
    have ht₁ := (Functor.Monoidal.μNatIso F).hom.naturality
      (X := (H.obj (op K, L), K'))
      (Y := (H.obj (op K', L'), K')) (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c), 𝟙 K')
    have ht₂ := (Functor.Monoidal.μNatIso F).hom.naturality
      (X := (H.obj (op K, L), K'))
      (Y := (H.obj (op K, L), K)) (𝟙 _, b)
    change (F.map (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)) ⊗ₘ
      F.map (𝟙 K')) ≫ (m.μIso _ K').hom =
      (m.μIso _ K').hom ≫ F.map
        (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c) ⊗ₘ 𝟙 K') at ht₁
    change (F.map (𝟙 _) ⊗ₘ F.map b) ≫ (m.μIso _ K).hom =
      (m.μIso _ K').hom ≫ F.map (𝟙 _ ⊗ₘ b) at ht₂
    rw [F.map_id] at ht₁ ht₂
    rw [← Category.assoc, ht₁, Category.assoc, ← F.map_comp]
    rw [evaluation_naturality H e he b c, F.map_comp, F.map_comp]
    rw [← Category.assoc, ← ht₂]
    simp only [Category.assoc]
  refine ⟨{ app := fun P ↦ a.homEquiv _ _ (d P.1.unop P.2), naturality := ?_ }, ?_⟩
  · intro P P' f
    change H.map f ≫ a.homEquiv _ _ (d P'.1.unop P'.2) =
      a.homEquiv _ _ (d P.1.unop P.2) ≫ R.map (J.map ((F.map f.1.unop).op, F.map f.2))
    rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
    congr 1
    exact dn f.1.unop f.2
  · intro K L
    rfl

private theorem counitSections
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
    (γ : H ⟶ F.op.prod F ⋙ J ⋙ R)
    (QS : C ⥤ AddCommGrpCat) (QT : D ⥤ AddCommGrpCat) (z : R ⋙ QS ≅ QT)
    (eS : ∀ P : Cᵒᵖ × C, QS.obj (H.obj P) ≃+ (P.1.unop ⟶ P.2))
    (eT : ∀ P : Dᵒᵖ × D, QT.obj (J.obj P) ≃+ (P.1.unop ⟶ P.2))
    (hnT : ∀ (P P' : Dᵒᵖ × D) (f : P ⟶ P') (x : QT.obj (J.obj P)),
      eT P' (QT.map (J.map f) x) = f.1.unop ≫ eT P x ≫ f.2)
    (hp : ∀ (K L : C) (x : QS.obj (H.obj (op K, L))),
      eT (op (F.obj K), F.obj L)
        ((z.hom.app (J.obj (op (F.obj K), F.obj L)))
          (QS.map (γ.app (op K, L)) x)) = F.map (eS (op K, L) x)) :
    ∀ (M : C) (E : D) (x : QS.obj (H.obj (op M, R.obj E))),
      eT (op (F.obj M), E)
        ((z.hom.app (J.obj (op (F.obj M), E)))
          (QS.map (γ.app (op M, R.obj E) ≫
            R.map (J.map (X := (op (F.obj M), F.obj (R.obj E)))
              (Y := (op (F.obj M), E)) ((𝟙 (F.obj M)).op, a.counit.app E))) x)) =
        F.map (eS (op M, R.obj E) x) ≫ a.counit.app E := by
  intro M E x
  let U := J.obj (op (F.obj M), F.obj (R.obj E))
  let V := J.obj (op (F.obj M), E)
  let f : (op (F.obj M), F.obj (R.obj E)) ⟶ (op (F.obj M), E) :=
    ((𝟙 (F.obj M)).op, a.counit.app E)
  let v : U ⟶ V := J.map f
  have hz := ConcreteCategory.congr_hom (z.hom.naturality v)
    (QS.map (γ.app (op M, R.obj E)) x)
  have hn := hnT (op (F.obj M), F.obj (R.obj E)) (op (F.obj M), E) f
    ((z.hom.app U) (QS.map (γ.app (op M, R.obj E)) x))
  change eT (op (F.obj M), E)
    ((z.hom.app V) (QS.map (γ.app (op M, R.obj E) ≫ R.map v) x)) = _
  rw [QS.map_comp]
  change eT (op (F.obj M), E)
    ((z.hom.app V) (QS.map (R.map v) (QS.map (γ.app (op M, R.obj E)) x))) = _
  change (z.hom.app V) (QS.map (R.map v) (QS.map (γ.app (op M, R.obj E)) x)) =
    QT.map v ((z.hom.app U) (QS.map (γ.app (op M, R.obj E)) x)) at hz
  rw [hz]
  change eT (op (F.obj M), E)
    (QT.map v ((z.hom.app U) (QS.map (γ.app (op M, R.obj E)) x))) =
      𝟙 (F.obj M) ≫
        eT (op (F.obj M), F.obj (R.obj E))
          ((z.hom.app U) (QS.map (γ.app (op M, R.obj E)) x)) ≫ a.counit.app E at hn
  rw [hn, Category.id_comp, hp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Construction of the evaluation mate, with compatible sections identifications.
No invertibility of the counit composite is asserted here.

Source: Stacks Project, Tags 08I3, 079W, 08DJ and 08JA
(blueprint: lem-pc-derived-internal-hom-pullback-mate-sections).

Proof: Choose the pullback/direct-image adjunction from the underived adjunction
by the K-flat and K-injective derived-functor construction of Tag 079W. The
canonical tensor-Hom bijections of Tag 08DJ give bS and bT by the Hom-equivalence
construction of an adjunction. Resolve both tensor factors by K-flat complexes.
Termwise pullback commutes with their tensor total complex, and localization
therefore gives t. Pull back evaluation and precompose with t.inv, transpose by
bT, and then transpose by a to obtain gamma. Naturality of evaluation and the
three transpositions proves naturality in both entries.

Compute global sections on K-injective representatives. Direct image followed
by sections on S is sections on T, so the derived comparison gives z after
zeroth cohomology. For eS and eT use the identification of degree-zero Hom
cocycles modulo homotopies with derived morphisms into a K-injective complex
(Tag 08JA). Composition of chain maps gives the two naturality equations.
With these specific compatible choices, transposing pulled-back evaluation
and postcomposing with the counit takes the class of phi to the class of
Lg*(phi) followed by the counit. This proves the last equation without using
invertibility of the internal-Hom composite. -/
theorem exists_derivedInternalHom_pullback_mate_sections
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (bS : ∀ K : schemeDerivedCategory S, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj
            (op K))
      (bT : ∀ K : schemeDerivedCategory T, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)).obj
            (op K))
      (t : tensor (schemeDerivedCategory S) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory T))
      (γ : derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf ⟶
        (derivedPullback g).op.prod (derivedPullback g) ⋙
          derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage g)
      (z : schemeDerivedDirectImage g ⋙
          ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf ≅
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)
      (eS : ∀ P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P)),
        eS P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P)),
        eT P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ K L : schemeDerivedCategory S,
        (a.homEquiv
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))
            ((derivedInternalHom (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
                (op ((derivedPullback g).obj K), (derivedPullback g).obj L))).symm
            (γ.app (op K, L)) =
          (bT ((derivedPullback g).obj K)).homEquiv
            ((derivedPullback g).obj
              ((derivedInternalHom (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).obj (op K, L))) ((derivedPullback g).obj L)
            (t.inv.app
                ((derivedInternalHom (Opens.grothendieckTopology S)
                  S.toRingedSpace.sheaf).obj (op K, L), K) ≫
              (derivedPullback g).map ((bS K).counit.app L))) ∧
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op M, (schemeDerivedDirectImage g).obj E))),
        eT (op ((derivedPullback g).obj M), E)
          ((z.hom.app
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).obj (op ((derivedPullback g).obj M), E)))
            ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).map (γ.app (op M, (schemeDerivedDirectImage g).obj E) ≫
                  (schemeDerivedDirectImage g).map
                    ((derivedInternalHom (Opens.grothendieckTopology T)
                      T.toRingedSpace.sheaf).map
                      (X := (op ((derivedPullback g).obj M),
                        (derivedPullback g).obj ((schemeDerivedDirectImage g).obj E)))
                      (Y := (op ((derivedPullback g).obj M), E))
                      ((𝟙 ((derivedPullback g).obj M)).op, a.counit.app E))) x)) =
          (derivedPullback g).map
              (eS (op M, (schemeDerivedDirectImage g).obj E) x) ≫
            a.counit.app E) := by
  classical
  let H := derivedInternalHom.{u, w} (Opens.grothendieckTopology S) S.toRingedSpace.sheaf
  let J := derivedInternalHom.{u, w} (Opens.grothendieckTopology T) T.toRingedSpace.sheaf
  let F := derivedPullback.{u, w} g
  let R := schemeDerivedDirectImage.{u, w, w} g
  let QS := ringedSiteZerothHypercohomology.{u, w} (Opens.grothendieckTopology S)
    S.toRingedSpace.sheaf
  let QT := ringedSiteZerothHypercohomology.{u, w} (Opens.grothendieckTopology T)
    T.toRingedSpace.sheaf
  refine (exists_derivedPullbackMonoidalModel.{u, w} g).elim fun m _ ↦ ?_
  refine (exists_canonicalDerivedTensorHom.{u, w} S).elim fun qS hqS ↦ ?_
  refine (exists_canonicalDerivedTensorHom.{u, w} T).elim fun qT hqT ↦ ?_
  refine (exists_derivedPullback_evaluation_sections.{u, w} g m qS hqS qT hqT).elim
    fun a ha ↦ ?_
  refine ha.elim fun z hz ↦ ?_
  refine hz.elim fun eS hS ↦ ?_
  refine hS.elim fun eT hT ↦ ?_
  have hnS := hT.1
  have hnT := hT.2.1
  have hs := hT.2.2
  let bS := tensorHomAdjunction H qS hqS.1
  let bT := tensorHomAdjunction J qT hqT.1
  let := m.toMonoidal
  let t := (Functor.Monoidal.μNatIso F).symm
  refine (pullbackEvaluationMate_exists H J F R a m qS qT hqS.1 hqT.1).elim
    fun γ hγ ↦ ?_
  refine ⟨a, bS, bT, t, γ, z, eS, eT, hnS, hnT, ?_, ?_⟩
  · intro K L
    have hbS := tensorHomAdjunction_counit H qS hqS.1 K L
    have hbT := tensorHomAdjunction_homEquiv J qT hqT.1
      (F.obj (H.obj (op K, L))) (F.obj K) (F.obj L)
    change (bS K).counit.app L = _ at hbS
    change (bT (F.obj K)).homEquiv (F.obj (H.obj (op K, L))) (F.obj L) = _ at hbT
    have hv : t.inv.app (H.obj (op K, L), K) ≫ F.map ((bS K).counit.app L) =
        (m.μIso _ K).hom ≫ F.map (qS _ K L (𝟙 _)) :=
      congrArg (fun v ↦ (m.μIso (H.obj (op K, L)) K).hom ≫ F.map v) hbS
    have hr := (congrArg (fun e : _ ≃ _ ↦ e
      (t.inv.app (H.obj (op K, L), K) ≫ F.map ((bS K).counit.app L))) hbT).trans
        (congrArg (qT _ (F.obj K) (F.obj L)).symm hv)
    exact (congrArg (a.homEquiv _ _).symm (hγ K L)).trans
      ((Equiv.symm_apply_apply _ _).trans hr.symm)
  · apply counitSections H J F R a γ QS QT z eS eT hnT
    intro K L x
    exact (congrArg (fun v ↦ eT (op (F.obj K), F.obj L)
      ((z.hom.app (J.obj (op (F.obj K), F.obj L))) (QS.map v x)))
        (hγ K L)).trans (hs K L x)

end AlgebraicGeometry
