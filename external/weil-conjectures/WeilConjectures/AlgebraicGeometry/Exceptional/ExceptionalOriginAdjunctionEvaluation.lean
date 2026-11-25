/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluation of the origin adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
private instance (priority := 20000) cachedProSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] exceptionalTransportProEtaleCommRingSheafify
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  exceptionalTransportProEtaleTypeSheafify exceptionalTransportProEtaleRingCompose
  exceptionalTransportProEtaleRingSetCompose exceptionalTransportProEtaleAddCommGrpSetCompose
  strictEtaleRingCompose strictEtaleRingSetCompose strictEtaleAddCommGrpSetCompose
  strictEtaleAddCommGrpSheafify strictEtaleCommRingSheafify strictEtaleTypeSheafify
  strictEtaleAddCommGrpLocal
-- Reduce only the small data wrappers; keep derived localizations and mate words sealed.
attribute [local implicit_reducible] ExceptionalProCompactSupport StrictEtaleExceptionalAdjoint
  ExceptionalSystemCompactificationComparison exceptionalSystemRight exceptionalProSupport
attribute [local irreducible] exceptionalSystemComparison exceptionalSystemOriginComparison
  exceptionalSystemLevelComparison exceptionalSystemLevelOriginComparison
  exceptionalProSupportEvaluation exceptionalSystemRightEvaluation
  exceptionalSystemRightEtaleEvaluation
attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q
  CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

section MateCalculus
universe a av b bv c cv d dv e ev f fv
variable {A : Type a} [Category.{av} A] {B₀ : Type b} [Category.{bv} B₀]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]

private theorem conjugate_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (P : A) (Q : B₀) (f : L.obj P ⟶ Q) :
    b.homEquiv P Q (e.hom.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateIsoEquiv a b e).hom.app Q := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show R.map f ≫ (conjugateIsoEquiv a b e).hom.app Q =
    (conjugateIsoEquiv a b e).hom.app (L.obj P) ≫ R'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem conjugate_of_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (δ : R ≅ R')
    (h : ∀ P Q (f : L'.obj P ⟶ Q),
      b.homEquiv P Q f = a.homEquiv P Q (e.inv.app P ≫ f) ≫ δ.hom.app Q) :
    conjugateIsoEquiv a b e = δ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  have hh := h (R.obj Q) Q (e.hom.app _ ≫ a.counit.app Q)
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hc := conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

private theorem mate_of_unit
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {F : A ⥤ C} {G : B₀ ⥤ D}
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (h : ∀ P, b.homEquiv _ _ (α.app P) =
      F.map (a.unit.app P) ≫ β.app (L.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ α)) = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext P
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ (α.app P) = b.homEquiv _ _
    ((((mateEquiv a b).symm (.mk _ _ _ _ β))).app P)
  exact (h P).trans (unit_mateEquiv_symm a b (.mk _ _ _ _ β) P)

private theorem scalar_inverse_mate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (β : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hc : conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ)
    (hβ : ∀ P, am.homEquiv _ _ (β.hom.app P) =
      RA.map (an.unit.app P) ≫ δ.inv.app (Fn.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ γ.inv)) = β.hom := by
  apply (mateEquiv an am).injective
  have hh := iterated_mateEquiv_conjugateEquiv a b am an
    (.mk _ _ _ _ γ.inv)
  have hi : conjugateEquiv (a.comp an) (am.comp b) γ.inv = δ.inv := by
    exact congrArg Iso.inv hc
  rw [hi] at hh
  exact hh.trans (mate_of_unit an am β.hom δ.inv hβ).symm

private theorem inverse_transition_transpose
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Fn : B₀ ⥤ D}
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hmate : (mateEquiv a b (.mk _ _ _ _ γ.inv)) = δ.hom)
    {Nm : C} {Nn : D} {Mm : A} {Mn : B₀}
    (em : Nm ≅ Fm.obj Mm) (en : Nn ≅ Fn.obj Mn)
    (τM : Mm ⟶ RA.obj Mn) (τN : Nm ⟶ RB.obj Nn)
    (hτ : τN ≫ RB.map en.hom = em.hom ≫ Fm.map τM ≫ δ.hom.app Mn) :
    TB.map em.hom ≫ γ.inv.app Mm ≫ Fn.map ((a.homEquiv _ _).symm τM) =
      (b.homEquiv _ _).symm τN ≫ en.hom := by
  apply (b.homEquiv _ _).injective
  rw [b.homEquiv_naturality_right _ en.hom, Equiv.apply_symm_apply]
  rw [b.homEquiv_naturality_left em.hom]
  have he : (mateEquiv a b).symm (.mk _ _ _ _ δ.hom) =
      .mk _ _ _ _ γ.inv := by
    rw [← hmate]
    exact Equiv.symm_apply_apply _ _
  have hm := adjunctionMate_transpose a b (.mk _ _ _ _ δ.hom) Mm Mn
    ((a.homEquiv _ _).symm τM)
  rw [he, Equiv.apply_symm_apply] at hm
  rw [hm]
  simpa only [Category.assoc] using hτ.symm

private theorem evaluation_hom
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R)
    {l : C ⥤ D} {r : D ⥤ C} (b : l ⊣ r)
    {E : A ⥤ C} {F : B₀ ⥤ D}
    (α : L ⋙ F ≅ E ⋙ l) (β : R ⋙ E ≅ F ⋙ r)
    (hu : ∀ M, E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      r.map (α.hom.app M) = b.unit.app (E.obj M))
    {M : A} {N : B₀} (h : L.obj M ⟶ N) :
    E.map (a.homEquiv M N h) ≫ β.hom.app N =
      b.homEquiv (E.obj M) (F.obj N) (α.inv.app M ≫ F.map h) := by
  rw [a.homEquiv_unit, E.map_comp, Category.assoc]
  have hn := β.hom.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc]
  have he : E.map (a.unit.app M) ≫ β.hom.app (L.obj M) =
      b.unit.app (E.obj M) ≫ r.map (α.inv.app M) := by
    apply (cancel_mono (r.map (α.hom.app M))).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [r.map_id ((E ⋙ l).obj M), Category.comp_id]
    exact hu M
  rw [he, Category.assoc, ← r.map_comp, ← b.homEquiv_unit]

private theorem evaluation_hom_of_mate
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R)
    {l : C ⥤ D} {r : D ⥤ C} (b : l ⊣ r)
    {E : A ⥤ C} {F : B₀ ⥤ D}
    (α : L ⋙ F ≅ E ⋙ l) (β : R ⋙ E ≅ F ⋙ r)
    (hβ : β.hom = (mateEquiv a b (.mk _ _ _ _ α.inv)))
    {M : A} {N : B₀} (h : L.obj M ⟶ N) :
    E.map (a.homEquiv M N h) ≫ β.hom.app N =
      b.homEquiv (E.obj M) (F.obj N) (α.inv.app M ≫ F.map h) := by
  rw [hβ]
  simpa only [Equiv.symm_apply_apply] using (adjunctionMate_transpose a b
    (mateEquiv a b (.mk _ _ _ _ α.inv)) M N h).symm

-- Evaluation of the two successive Hom transposes uses only these mate equations.
private theorem iterated_evaluation_hom
    {E₀ : Type e} [Category.{ev} E₀] {F₀ : Type f} [Category.{fv} F₀]
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R)
    {l : C ⥤ D} {r : D ⥤ C} (b : l ⊣ r)
    {I : B₀ ⥤ E₀} {J : E₀ ⥤ B₀} (c : I ⊣ J)
    {i : D ⥤ F₀} {j : F₀ ⥤ D} (d : i ⊣ j)
    {EX : A ⥤ C} {EY : B₀ ⥤ D} {EP : E₀ ⥤ F₀}
    (α : L ⋙ EY ≅ EX ⋙ l) (β : R ⋙ EX ≅ EY ⋙ r)
    (σ : I ⋙ EP ≅ EY ⋙ i) (τ : J ⋙ EY ≅ EP ⋙ j)
    (hβ : β.hom = (mateEquiv a b (.mk _ _ _ _ α.inv)))
    (hu : ∀ M, EY.map (c.unit.app M) ≫ τ.hom.app (I.obj M) ≫
      j.map (σ.hom.app M) = d.unit.app (EY.obj M))
    {M : A} {H N : E₀} {P : C}
    (f : I.obj (L.obj M) ⟶ H) (h : H ⟶ N)
    (g : i.obj (l.obj P) ⟶ EP.obj H) (t : EX.obj M ⟶ P)
    (hk : i.map (α.inv.app M) ≫ σ.inv.app (L.obj M) ≫ EP.map f =
      i.map (l.map t) ≫ g) :
    EX.map (a.homEquiv _ _ (c.homEquiv _ _ (f ≫ h))) ≫
        β.hom.app (J.obj N) ≫ r.map (τ.hom.app N) =
      t ≫ b.homEquiv P (j.obj (EP.obj N))
        (d.homEquiv (l.obj P) (EP.obj N) (g ≫ EP.map h)) := by
  have hy := evaluation_hom c d σ τ hu (f ≫ h)
  have hg := evaluation_hom_of_mate a b α β hβ (c.homEquiv _ _ (f ≫ h))
  rw [← Category.assoc, hg, ← b.homEquiv_naturality_right, Category.assoc, hy]
  erw [← d.homEquiv_naturality_left (α.inv.app M)]
  simp only [Functor.map_comp]
  rw [reassoc_of% hk, d.homEquiv_naturality_left, b.homEquiv_naturality_left]
  rfl

-- Cancel the evaluated source counit in abstract categories, before specializing sites.
private theorem transpose_evaluation
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R)
    {l : C ⥤ D} {r : D ⥤ C} (b : l ⊣ r)
    {E : A ⥤ C} {F : B₀ ⥤ D}
    (α : L ⋙ F ≅ E ⋙ l) (β : R ⋙ E ≅ F ⋙ r)
    {M : B₀} {H : A} {K : C}
    (q : R.obj M ⟶ H) (qn : r.obj (F.obj M) ⟶ K) (δ : E.obj H ⟶ K)
    (t : M ⟶ L.obj H) (tn : F.obj M ⟶ l.obj K)
    (hs : L.map q = a.counit.app M ≫ t)
    (hn : l.map qn = b.counit.app (F.obj M) ≫ tn)
    (hq : E.map q ≫ δ = β.hom.app M ≫ qn)
    (hc : α.hom.app (R.obj M) ≫ l.map (β.hom.app M) ≫
      b.counit.app (F.obj M) = F.map (a.counit.app M))
    [Epi (F.map (a.counit.app M))] :
    F.map t ≫ α.hom.app H ≫ l.map δ = tn := by
  apply (cancel_epi (F.map (a.counit.app M))).1
  rw [← F.map_comp_assoc, ← hs]
  have he := α.hom.naturality q
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he, ← l.map_comp, hq, l.map_comp, hn, reassoc_of% hc]

private abbrev leftOf {L : A ⥤ B₀} {R : B₀ ⥤ A} (_a : L ⊣ R) := L
private abbrev rightOf {L : A ⥤ B₀} {R : B₀ ⥤ A} (_a : L ⊣ R) := R

-- The origin comparison is obtained by pasting these four component squares.
private theorem paste_origin_evaluation
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ : A}
    {x : P₀ ⟶ P₁} {y : P₁ ⟶ P₂} {z : P₂ ⟶ P₃}
    {a : P₁ ⟶ P₄} {b : P₄ ⟶ P₅} {c : P₅ ⟶ P₆} {d : P₆ ⟶ P₃}
    {e : P₀ ⟶ P₇} {f : P₇ ⟶ P₈} {g : P₈ ⟶ P₅}
    {h : P₈ ⟶ P₉} {i : P₉ ⟶ P₆} {w : P₄ ⟶ P₃}
    (hn : y ≫ z = a ≫ w) (hc : b ≫ c ≫ d = w)
    (he : x ≫ a ≫ b = e ≫ f ≫ g) (hk : h ≫ i = g ≫ c) :
    x ≫ y ≫ z = e ≫ f ≫ h ≫ i ≫ d := by
  rw [hn, ← hc, reassoc_of% he, ← reassoc_of% hk]

-- Specialize compatibility of Hom transposes to the unit and counit.
private theorem origin_unit_counit
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {l : C ⥤ D} {r : D ⥤ C}
    {PA : ObjectProperty A} {PB : ObjectProperty B₀}
    {PC : ObjectProperty C} {PD : ObjectProperty D}
    {ls : ∀ M, PA M → PB (L.obj M)} {rs : ∀ N, PB N → PA (R.obj N)}
    {ll : ∀ M, PC M → PD (l.obj M)} {rr : ∀ N, PD N → PC (r.obj N)}
    (s : PB.lift (PA.ι ⋙ L) (fun M ↦ ls M.obj M.property) ⊣
      PA.lift (PB.ι ⋙ R) (fun N ↦ rs N.obj N.property))
    (t : PD.lift (PC.ι ⋙ l) (fun M ↦ ll M.obj M.property) ⊣
      PC.lift (PD.ι ⋙ r) (fun N ↦ rr N.obj N.property))
    {E : A ⥤ C} {F : B₀ ⥤ D}
    (α : L ⋙ F ≅ E ⋙ l) (β : R ⋙ E ≅ F ⋙ r)
    (hE : ∀ M, PA M → PC (E.obj M)) (hF : ∀ N, PB N → PD (F.obj N))
    (hhom : ∀ (M : PA.FullSubcategory) (N : PB.FullSubcategory)
      (h : L.obj M.obj ⟶ N.obj),
      E.map (s.homEquiv M N (ObjectProperty.homMk h)).hom ≫ β.hom.app N.obj =
        (t.homEquiv ⟨E.obj M.obj, hE M.obj M.property⟩
          ⟨F.obj N.obj, hF N.obj N.property⟩
          (ObjectProperty.homMk (α.inv.app M.obj ≫ F.map h))).hom) :
    -- unitEvaluation
    (∀ M,
    E.map (s.unit.app M).hom ≫
      β.hom.app
        (L.obj M.obj) ≫
      r.map
        (α.hom.app M.obj) =
    (t.unit.app
      ⟨E.obj M.obj,
        hE M.obj M.property⟩).hom) ∧
    -- counitEvaluation
    (∀ N,
    α.hom.app
        (R.obj N.obj) ≫
      l.map
        (β.hom.app N.obj) ≫
      (t.counit.app
        ⟨F.obj N.obj,
          hF N.obj N.property⟩).hom =
    F.map (s.counit.app N).hom) := by
  refine ⟨?_, ?_⟩
  · intro M
    let M' : PC.FullSubcategory :=
      ⟨E.obj M.obj,
        hE M.obj M.property⟩
    let N' : PD.FullSubcategory :=
      ⟨F.obj (L.obj M.obj),
        hF _ (ls _ M.property)⟩
    let u : ((leftOf t).obj M') ⟶ N' :=
      ObjectProperty.homMk (α.inv.app M.obj)
    let v : N' ⟶ ((leftOf t).obj M') :=
      ObjectProperty.homMk (α.hom.app M.obj)
    have huv : u ≫ v = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      exact Iso.inv_hom_id_app α M.obj
    have hn := t.homEquiv_naturality_right u v
    rw [huv, Adjunction.homEquiv_id] at hn
    have hh := hhom M
      ((leftOf s).obj M) (𝟙 _)
    change E.map
        (s.homEquiv M _ (𝟙 _)).hom ≫ _ = _ at hh
    rw [Adjunction.homEquiv_id] at hh
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
    rw [← Category.assoc]
    erw [hh]
    exact (congrArg (fun k ↦ k.hom) hn).symm
  · intro N
    let M := (rightOf s).obj N
    let M' : PC.FullSubcategory :=
      ⟨E.obj M.obj,
        hE M.obj M.property⟩
    let N' : PD.FullSubcategory :=
      ⟨F.obj N.obj,
        hF N.obj N.property⟩
    let u : (leftOf t).obj M' ⟶ N' :=
      ObjectProperty.homMk (α.inv.app M.obj ≫
        F.map
          (s.counit.app N).hom)
    let v : M' ⟶ (rightOf t).obj N' :=
      ObjectProperty.homMk (β.hom.app N.obj)
    have hh := hhom M N
      (s.counit.app N).hom
    change E.map
        (s.homEquiv M N
          (s.counit.app N)).hom ≫ _ = _ at hh
    have hε : s.homEquiv M N
        (s.counit.app N) = 𝟙 M := by
      have hi := (s.homEquiv M N).apply_symm_apply (𝟙 M)
      rw [s.homEquiv_symm_id] at hi
      exact hi
    erw [hε, ObjectProperty.FullSubcategory.id_hom,
      CategoryTheory.Functor.map_id, Category.id_comp] at hh
    have he : t.homEquiv M' N' u = v := by
      apply ObjectProperty.hom_ext
      exact hh.symm
    have ht := (Equiv.eq_symm_apply _).mpr he
    rw [Adjunction.homEquiv_counit] at ht
    apply (cancel_epi (α.inv.app M.obj)).1
    simp only [← Category.assoc]
    erw [Iso.inv_hom_id_app, Category.id_comp]
    exact (congrArg (fun k ↦ k.hom) ht).symm

end MateCalculus

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

variable (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
  (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)

private theorem site_inverse_transition {m n : ℕ} (h : n ≤ m) H :
    (CX.proEvaluation.scalar h).derived.map
        ((CX.image.inverseEvaluation m).hom.app H) ≫
      (CX.image.derivedTensor h).inv.app ((S.PX.evaluation m).obj H) ≫
      (CX.image.level n).inverse.map
        (((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app H)) =
    ((CX.proEvaluation.scalar h).derivedAdj.homEquiv _ _).symm
        ((CX.proEvaluation.transition h).app (CX.image.system.inverse.obj H)) ≫
      (CX.image.inverseEvaluation n).hom.app H := by
  have hc := scalar_conjugate (S.PX.scalar h).derivedAdj
    (CX.proEvaluation.scalar h).derivedAdj
    (CX.image.level m).adjunction (CX.image.level n).adjunction
    (CX.image.derivedTensor h) (CX.image.restrictedDirect h)
    (CX.image.restrictedDirect_mate h)
  have hm := scalar_inverse_mate (S.PX.scalar h).derivedAdj
    (CX.proEvaluation.scalar h).derivedAdj
    (CX.image.level m).adjunction (CX.image.level n).adjunction
    (CX.image.derivedTensor h) (CX.image.restrictedDirect h)
    (CX.image.restrictedInverse h) hc (CX.image.restrictedInverse_mate h)
  exact inverse_transition_transpose (S.PX.scalar h).derivedAdj
    (CX.proEvaluation.scalar h).derivedAdj
    (CX.image.derivedTensor h) (CX.image.restrictedInverse h) hm
    ((CX.image.inverseEvaluation m).app H) ((CX.image.inverseEvaluation n).app H)
    ((S.PX.transition h).app H)
    ((CX.proEvaluation.transition h).app (CX.image.system.inverse.obj H))
    (CX.image.inverseTransition h H)

private theorem origin_comparison_evaluation
    (hcomparison :
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)))
    (n : ℕ) M :
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemOriginComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app M =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj (CX.image.system.direct.obj M)) ≫
      (CY.image.level n).inverse.map
        ((S.evaluation n).hom.app (CX.image.system.direct.obj M)) ≫
      (CY.image.level n).inverse.map ((S.levelFunctor n).map
        ((CX.image.directEvaluation n).hom.app M)) ≫
      (exceptionalSystemLevelOriginComparison R n).app
        ((CX.proEvaluation.evaluation n).obj M) := by
  have hn := (exceptionalProSupportEvaluation P n).hom.naturality
    (CX.image.system.adjunction.counit.app M)
  dsimp only [Functor.comp_map] at hn
  have hk := (exceptionalSystemLevelComparison R n).naturality
    ((CX.image.directEvaluation n).hom.app M)
  dsimp only [Functor.comp_map] at hk
  have hc := congrArg
    (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
    (CX.image.counit n M)
  simp only [Functor.map_comp] at hc
  simp only [exceptionalSystemOriginComparison, exceptionalSystemLevelOriginComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact paste_origin_evaluation hn hc
    (hcomparison n (CX.image.system.direct.obj M)) hk

private theorem right_evaluation_app (n : ℕ) N :
    (exceptionalSystemRightEvaluation G CX CY n).hom.app N =
      (CX.image.inverseEvaluation n).hom.app (G.right.obj (CY.image.system.direct.obj N)) ≫
        (CX.image.level n).inverse.map ((G.evaluation n).hom.app
          (CY.image.system.direct.obj N)) ≫
        (CX.image.level n).inverse.map ((G.levelRight n).map
          ((CY.image.directEvaluation n).hom.app N)) := by
  simp only [exceptionalSystemRightEvaluation, exceptionalSystemRightEtaleEvaluation,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_map]
  erw [Category.id_comp]

-- Elaborating the three concrete site adjunctions needs extra heartbeats.
private theorem origin_hom_evaluation
    (record : ExceptionalSystemTransportData G CX CY CZ P R)
    (hcomparison :
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)))
    (n : ℕ) (M : CX.origin.FullSubcategory) (N : CY.origin.FullSubcategory)
    (h : (exceptionalProSupport P).obj M.obj ⟶ N.obj) :
    (CX.proEvaluation.evaluation n).map
        (record.systemAdjunction.adjunction.homEquiv M N (ObjectProperty.homMk h)).hom ≫
      (exceptionalSystemRightEvaluation G CX CY n).hom.app N.obj =
    ((record.finiteAdjunction n).adjunction.homEquiv
      ⟨(CX.proEvaluation.evaluation n).obj M.obj,
        record.evaluationOriginX n M.obj M.property⟩
      ⟨(CY.proEvaluation.evaluation n).obj N.obj,
        record.evaluationOriginY n N.obj N.property⟩
      (ObjectProperty.homMk ((exceptionalProSupportEvaluation P n).inv.app M.obj ≫
        (CY.proEvaluation.evaluation n).map h))).hom := by
  let q := G.adjunction.homEquiv (CX.image.system.direct.obj M.obj)
    (CY.image.system.direct.obj N.obj)
      (CY.image.system.adjunction.homEquiv _ _
        ((exceptionalSystemOriginComparison R).app M.obj ≫ h))
  let qn := (G.levelAdjunction n).homEquiv
    ((CX.image.level n).direct.obj ((CX.proEvaluation.evaluation n).obj M.obj))
    ((CY.image.level n).direct.obj ((CY.proEvaluation.evaluation n).obj N.obj))
      ((CY.image.level n).adjunction.homEquiv _ _
        ((exceptionalSystemLevelOriginComparison R n).app
          ((CX.proEvaluation.evaluation n).obj M.obj) ≫
        (exceptionalProSupportEvaluation P n).inv.app M.obj ≫
        (CY.proEvaluation.evaluation n).map h))
  have hk := origin_comparison_evaluation CX CY CZ P R hcomparison n M.obj
  have hki :
      (CY.image.level n).inverse.map
          ((S.evaluation n).inv.app (CX.image.system.direct.obj M.obj)) ≫
        (CY.image.inverseEvaluation n).inv.app
          (S.functor.obj (CX.image.system.direct.obj M.obj)) ≫
        (CY.proEvaluation.evaluation n).map
          ((exceptionalSystemOriginComparison R).app M.obj) =
      (CY.image.level n).inverse.map ((S.levelFunctor n).map
          ((CX.image.directEvaluation n).hom.app M.obj)) ≫
        (exceptionalSystemLevelOriginComparison R n).app
          ((CX.proEvaluation.evaluation n).obj M.obj) ≫
        (exceptionalProSupportEvaluation P n).inv.app M.obj := by
    have hh := congrArg (fun z ↦
      (CY.image.level n).inverse.map
          ((S.evaluation n).inv.app (CX.image.system.direct.obj M.obj)) ≫
        (CY.image.inverseEvaluation n).inv.app
          (S.functor.obj (CX.image.system.direct.obj M.obj)) ≫ z ≫
        (exceptionalProSupportEvaluation P n).inv.app M.obj) hk
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hh
    erw [Category.comp_id] at hh
    exact hh
  have hq : (S.PX.evaluation n).map q ≫
      (G.evaluation n).hom.app (CY.image.system.direct.obj N.obj) ≫
      (G.levelRight n).map ((CY.image.directEvaluation n).hom.app N.obj) =
      (CX.image.directEvaluation n).hom.app M.obj ≫ qn := by
    simpa only [Category.assoc] using iterated_evaluation_hom G.adjunction (G.levelAdjunction n)
      CY.image.system.adjunction (CY.image.level n).adjunction
      (S.evaluation n) (G.evaluation n)
      (CY.image.inverseEvaluation n) (CY.image.directEvaluation n)
      (G.property.2.2.1 n) (CY.image.unit n)
      ((exceptionalSystemOriginComparison R).app M.obj) h
      ((exceptionalSystemLevelOriginComparison R n).app
        ((CX.proEvaluation.evaluation n).obj M.obj) ≫
        (exceptionalProSupportEvaluation P n).inv.app M.obj)
      ((CX.image.directEvaluation n).hom.app M.obj) hki
  have htS := record.systemAdjunction.transpose M N (ObjectProperty.homMk h)
  change CX.image.system.inverse.map q = CX.image.system.adjunction.counit.app M.obj ≫
    (record.systemAdjunction.adjunction.homEquiv M N (ObjectProperty.homMk h)).hom at htS
  have htN := (record.finiteAdjunction n).transpose
    ⟨(CX.proEvaluation.evaluation n).obj M.obj,
      record.evaluationOriginX n M.obj M.property⟩
    ⟨(CY.proEvaluation.evaluation n).obj N.obj,
      record.evaluationOriginY n N.obj N.property⟩
    (ObjectProperty.homMk ((exceptionalProSupportEvaluation P n).inv.app M.obj ≫
      (CY.proEvaluation.evaluation n).map h))
  change (CX.image.level n).inverse.map qn =
    (CX.image.level n).adjunction.counit.app ((CX.proEvaluation.evaluation n).obj M.obj) ≫
      _ at htN
  have := record.siteX.counit M.obj M.property
  rw [right_evaluation_app, ← Functor.map_comp]
  exact transpose_evaluation CX.image.system.adjunction (CX.image.level n).adjunction
    (CX.image.inverseEvaluation n) (CX.image.directEvaluation n) q qn _ _ _
    htS htN hq (CX.image.counit n M.obj)

-- The three concrete evaluation identities elaborate over large derived categories.
/-- Evaluation of origin-adjunction Hom words and quotient transitions.
Source: Zheng Lemmas 4.10 and 5.22 and Proposition 5.24; Stacks 0B65.
(blueprint: lem-sf-exceptional-origin-adjunction-evaluation).

Proof: the transpose equations determine the system and finite Hom maps after
precomposition with the respective source site counits. Evaluate these equations,
substitute the comparison evaluation square, and use the three evaluated
adjunctions. The evaluated source counit is the finite counit composed with the
two inverse/direct evaluation comparisons; cancel it, using its invertibility on
origins. Hence evaluation intertwines the forward Hom maps. Apply this identity
to the identity of the left image for the unit, and to the counit for the counit,
using bijectivity of the finite Hom map. For quotient transitions use the actual
etale transition equation before evaluation, then apply the site inverse tensor
comparison. The scalar/site pullback cube identifies its derived tensor map and
the inverse-transition restriction comparison as scalar-adjunction mates. Moving
through this mate square gives exactly the displayed transpose. The intermediate
tensor object may be unbounded, so all transposes are taken in the unbounded
categories. No equality is inferred from agreement at every evaluation. -/
theorem exceptionalOriginAdjunctionEvaluation
    (record : ExceptionalSystemTransportData G CX CY CZ P R)
    (hfinite : ∀ n M, CX.levelOrigin n M →
      IsIso ((CX.image.level n).adjunction.counit.app M))
    (hcomparison :
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M))) :
    -- unitEvaluation
    (∀ n M,
    (CX.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.unit.app M).hom ≫
      (exceptionalSystemRightEvaluation G CX CY n).hom.app
        ((exceptionalProSupport P).obj M.obj) ≫
      ((CY.image.level n).direct ⋙ G.levelRight n ⋙ (CX.image.level n).inverse).map
        ((exceptionalProSupportEvaluation P n).hom.app M.obj) =
    ((record.finiteAdjunction n).adjunction.unit.app
      ⟨(CX.proEvaluation.evaluation n).obj M.obj,
        record.evaluationOriginX n M.obj M.property⟩).hom) ∧
    -- counitEvaluation
    (∀ n N,
    (exceptionalProSupportEvaluation P n).hom.app
        ((exceptionalSystemRight G CX CY).obj N.obj) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((exceptionalSystemRightEvaluation G CX CY n).hom.app N.obj) ≫
      ((record.finiteAdjunction n).adjunction.counit.app
        ⟨(CY.proEvaluation.evaluation n).obj N.obj,
          record.evaluationOriginY n N.obj N.property⟩).hom =
    (CY.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.counit.app N).hom) ∧
    -- quotientTransition
    (∀ {m n : ℕ} (h : n ≤ m) N,
    (CX.proEvaluation.scalar h).derived.map
        ((exceptionalSystemRightEtaleEvaluation G CX CY m).hom.app N) ≫
      (CX.image.derivedTensor h).inv.app
        ((G.levelRight m).obj ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map
        ((G.quotientComparison h).hom.app
          ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map ((G.levelRight n).map
        (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
          ((S.PY.transition h).app (CY.image.system.direct.obj N)))) =
    ((CX.proEvaluation.scalar h).derivedAdj.homEquiv _ _).symm
        ((CX.proEvaluation.transition h).app ((exceptionalSystemRight G CX CY).obj N)) ≫
      (exceptionalSystemRightEtaleEvaluation G CX CY n).hom.app N) := by
  have _ := hfinite
  have hu n := origin_unit_counit record.systemAdjunction.adjunction
    (record.finiteAdjunction n).adjunction
    (exceptionalProSupportEvaluation P n) (exceptionalSystemRightEvaluation G CX CY n)
    (record.evaluationOriginX n) (record.evaluationOriginY n)
    (origin_hom_evaluation G CX CY CZ P R record hcomparison n)
  refine ⟨fun n ↦ (hu n).1, fun n ↦ (hu n).2, ?_⟩
  intro m n h N
  have ht := G.property.2.2.2.2.2.2.2.2.2.1 h (CY.image.system.direct.obj N)
  have hs := site_inverse_transition CX h (G.right.obj (CY.image.system.direct.obj N))
  simp only [exceptionalSystemRightEtaleEvaluation, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    exceptionalSystemRight, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := (CX.image.derivedTensor h).inv.naturality
    ((G.evaluation m).hom.app (CY.image.system.direct.obj N))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [ht]
  simp only [Functor.map_comp]
  rw [reassoc_of% hs]
  rfl

end AlgebraicGeometry
