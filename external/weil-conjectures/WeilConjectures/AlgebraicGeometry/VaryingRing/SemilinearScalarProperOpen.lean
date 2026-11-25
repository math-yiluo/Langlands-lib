/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaRestriction
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaRestriction
public import WeilConjectures.CategoryTheory.ClopenAdjunctionUnitNormalization
public import WeilConjectures.CategoryTheory.SmoothPurity.ClopenMateComposite
public import WeilConjectures.CategoryTheory.TermwiseAdjunctionSquareUnit

/-! # Scalar restriction and proper/open coherence

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03D7 and 03DI
(blueprint: lem-sf-semilinear-scalar-proper-open). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

private abbrev termwiseIso := @CategoryTheory.termwiseAdjunctionIso

private theorem termwiseIso_square_eq {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
    (e : F ⋙ G ≅ H ⋙ K) :
    termwiseIso (I := ℕᵒᵖ) e = StrictTower.towerSquare F G H K e := by
  unfold termwiseIso StrictTower.towerSquare
  rfl

private theorem termwiseBetaUnit {I A B C D : Type*}
    [Category I] [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    (a : J ⊣ P) (a' : J' ⊣ P') (F : A ⥤ C) (G : B ⥤ D)
    (e : J ⋙ G ≅ F ⋙ J') (z : G ⋙ P' ≅ P ⋙ F)
    (h : ∀ M, a'.homEquiv _ _ (e.inv.app M) =
      F.map (a.unit.app M) ≫ z.inv.app (J.obj M)) (M : I ⥤ A) :
    (a'.whiskerRight I).homEquiv _ _ ((termwiseIso e).inv.app M) =
      ((Functor.whiskeringRight I _ _).obj F).map ((a.whiskerRight I).unit.app M) ≫
        (termwiseIso z).inv.app (((Functor.whiskeringRight I _ _).obj J).obj M) := by
  exact termwiseAdjunctionSquareUnit a a' F G e z h M

private theorem termwiseClopenUnit {I A X : Type*}
    [Category I] [Category A] [Category X]
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    (a : J ⊣ P) (b : P ⊣ D) (t : J ⟶ D)
    (h : ∀ N, a.unit.app N ≫ (b.homEquiv _ _).symm (t.app N) = 𝟙 N)
    (M : I ⥤ A) :
    (a.whiskerRight I).unit.app M ≫ ((b.whiskerRight I).homEquiv _ _).symm
      (((Functor.whiskeringRight I _ _).map t).app M) = 𝟙 M := by
  rw [Adjunction.homEquiv_counit]
  apply NatTrans.ext
  funext n
  have hn := h (M.obj n)
  rw [Adjunction.homEquiv_counit] at hn
  simpa only [NatTrans.comp_app, Adjunction.whiskerRight_unit_app_app,
    Adjunction.whiskerRight_counit_app_app, Functor.whiskeringRight,
    Functor.comp_obj, Functor.id_obj, Functor.whiskerRight_app, NatTrans.id_app] using hn

private theorem compIsoInvApp_eq {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (e e' : F ≅ G) (he : e = e') (M : A)
    {N : B} (f : N ⟶ G.obj M) : f ≫ e.inv.app M = f ≫ e'.inv.app M := by
  rw [he]

private theorem clopenComparison
    {A X A' X' : Type*} [Category A] [Category X] [Category A'] [Category X']
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    {J' : A' ⥤ X'} {P' : X' ⥤ A'} {D' : A' ⥤ X'}
    (o : J ⊣ P) (v : P ⊣ D) (o' : J' ⊣ P') (v' : P' ⊣ D')
    [IsIso o.unit] [IsIso o'.unit]
    (F : A ⥤ A') (H : X ⥤ X')
    (a : J ⋙ H ≅ F ⋙ J') (b : P ⋙ F ≅ H ⋙ P') (d : D ⋙ H ≅ F ⋙ D')
    (hu : ∀ N, F.map (o.unit.app N) ≫ b.hom.app (J.obj N) ≫
      P'.map (a.hom.app N) = o'.unit.app (F.obj N))
    (hv : ∀ M, H.map (v.unit.app M) ≫ d.hom.app (P.obj M) ≫
      D'.map (b.hom.app M) = v'.unit.app (H.obj M))
    (t : J ⟶ D) (t' : J' ⟶ D')
    (ht : ∀ N, t.app N = v.unit.app (J.obj N) ≫ D.map (inv (o.unit.app N)))
    (ht' : ∀ N, t'.app N = v'.unit.app (J'.obj N) ≫ D'.map (inv (o'.unit.app N)))
    (N : A) : H.map (t.app N) ≫ d.hom.app N =
      a.hom.app N ≫ t'.app (F.obj N) := by
  have hk : P'.map (a.hom.app N) ≫ inv (o'.unit.app (F.obj N)) =
      b.inv.app (J.obj N) ≫ F.map (inv (o.unit.app N)) := by
    apply (cancel_epi (F.map (o.unit.app N) ≫ b.hom.app (J.obj N))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp,
      IsIso.hom_inv_id, F.map_id]
    rw [reassoc_of% (hu N), IsIso.hom_inv_id]
    rfl
  have hη : H.map (v.unit.app (J.obj N)) ≫ d.hom.app (P.obj (J.obj N)) =
      v'.unit.app (H.obj (J.obj N)) ≫ D'.map (b.inv.app (J.obj N)) := by
    apply (cancel_mono (D'.map (b.hom.app (J.obj N)))).1
    simp only [Category.assoc, ← D'.map_comp, Iso.inv_hom_id_app]
    erw [D'.map_id, Category.comp_id]
    exact hv (J.obj N)
  rw [ht, ht', H.map_comp, Category.assoc]
  erw [d.hom.naturality]
  simp only [Functor.comp_map]
  rw [← Category.assoc, hη, Category.assoc, ← D'.map_comp, ← hk, D'.map_comp,
    ← Category.assoc]
  have hn := v'.unit.naturality (a.hom.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  exact Category.assoc _ _ _

private theorem clopenWordOfUnit
    {A X : Type*} [Category A] [Category X]
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    (o : J ⊣ P) (v : P ⊣ D) [IsIso o.unit] (t : J ⟶ D)
    (ht : ∀ N, o.unit.app N ≫ (v.homEquiv _ _).symm (t.app N) = 𝟙 N) (N : A) :
    t.app N = v.unit.app (J.obj N) ≫ D.map (inv (o.unit.app N)) := by
  apply (v.homEquiv _ _).symm.injective
  change (v.homEquiv _ _).symm (t.app N) =
    (v.homEquiv _ _).symm ((v.homEquiv _ _) (inv (o.unit.app N)))
  rw [Equiv.symm_apply_apply]
  apply (cancel_epi (o.unit.app N)).1
  rw [ht, IsIso.hom_inv_id]
  rfl

private theorem betaWordOfInverse
    {D : Type*} [Category D] {A B C E F H : D}
    (β : A ⟶ B) (t : H ⟶ E) (a : C ≅ B) (b : E ≅ C)
    (c : F ≅ A) (d : H ≅ F)
    (h : β ≫ a.inv ≫ b.inv = c.inv ≫ d.inv ≫ t) :
    t ≫ b.hom ≫ a.hom = d.hom ≫ c.hom ≫ β := by
  apply (cancel_epi d.inv).1
  apply (cancel_epi c.inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem termwiseCompMate {I A B C : Type*}
    [Category I] [Category A] [Category B] [Category C]
    {F : A ⥤ B} {P : B ⥤ A} {G : B ⥤ C} {Q : C ⥤ B}
    {H : A ⥤ C} {T : C ⥤ A}
    (a : F ⊣ P) (b : G ⊣ Q) (c : H ⊣ T) (e : Q ⋙ P ≅ T) :
    conjugateEquiv ((a.whiskerRight I).comp (b.whiskerRight I)) (c.whiskerRight I)
      (((Functor.whiskeringRight I _ _).mapIso (a.leftAdjointCompIso b c e).symm) ≪≫
        Functor.whiskeringRightObjCompIso F G).hom =
      (Functor.whiskeringRightObjCompIso Q P ≪≫ (Functor.whiskeringRight I _ _).mapIso e).hom := by
  have hm := Adjunction.conjugateEquiv_leftAdjointCompIso_inv a b c e
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simpa only [conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Adjunction.comp_counit_app, Adjunction.whiskerRight_unit_app_app,
    Adjunction.whiskerRight_counit_app_app, Functor.whiskeringRightObjCompIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom, Functor.whiskeringRight,
    Iso.refl_hom, NatTrans.id_app, Functor.comp_map, Functor.comp_obj, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Functor.map_id, Category.id_comp, Category.comp_id]
    using congrArg (fun t ↦ t.app (M.obj n)) hm

private lemma forwardMateCube
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (sr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (bs : Mf ⋙ Hs ≅ Gs ⋙ Mf')
    (f : PY ⋙ Mf ≅ Lf ⋙ PX) (f' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (g : PY ⋙ Gs ≅ Gr ⋙ PY') (g' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (r : PX ⋙ Sf ≅ Rf ⋙ PY) (r' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (tr : Rf ⋙ Gr ⟶ Hr ⋙ Rf') (ts : Sf ⋙ Gs ⟶ Hs ⋙ Sf')
    (hf : mateEquiv af bf f.hom = TwoSquare.mk _ _ _ _ r.inv)
    (hf' : mateEquiv af' bf' f'.hom = TwoSquare.mk _ _ _ _ r'.inv)
    (hsr : mateEquiv af af' sr.hom = TwoSquare.mk _ _ _ _ tr)
    (hbs : mateEquiv bf bf' bs.inv = TwoSquare.mk _ _ _ _ ts)
    (h : ∀ K, ts.app (PX.obj K) ≫ Sf'.map (g'.hom.app K) ≫
      r'.hom.app (Hr.obj K) = Gs.map (r.hom.app K) ≫
        g.hom.app (Rf.obj K) ≫ PY'.map (tr.app K)) (M : DY) :
    PX'.map (sr.inv.app M) ≫ f'.inv.app (Gr.obj M) ≫ Mf'.map (g.inv.app M) =
      g'.inv.app (Lf.obj M) ≫ Hs.map (f.inv.app M) ≫ bs.hom.app (PY.obj M) := by
  exact betaWordOfInverse (bs.hom.app (PY.obj M)) (PX'.map (sr.inv.app M))
    (Mf'.mapIso (g.symm.app M)) (f'.symm.app (Gr.obj M))
    (Hs.mapIso (f.symm.app M)) (g'.symm.app (Lf.obj M))
    (StrictTower.finiteMateCube af af' bf bf' sr bs f f' g g' r r' tr ts
      hf hf' hsr hbs h M)

private theorem projectorWordComparison
    {A X A' X' : Type*} [Category A] [Category X] [Category A'] [Category X']
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    {J' : A' ⥤ X'} {P' : X' ⥤ A'} {D' : A' ⥤ X'}
    (v : P ⊣ D) (v' : P' ⊣ D') (F : A ⥤ A') (H : X ⥤ X')
    (a : J ⋙ H ≅ F ⋙ J') (b : P ⋙ F ≅ H ⋙ P') (d : D ⋙ H ≅ F ⋙ D')
    (t : J ≅ D) (t' : J' ≅ D')
    (ht : ∀ N, H.map (t.hom.app N) ≫ d.hom.app N = a.hom.app N ≫ t'.hom.app (F.obj N))
    (hv : ∀ M, H.map (v.unit.app M) ≫ d.hom.app (P.obj M) ≫
      D'.map (b.hom.app M) = v'.unit.app (H.obj M)) (M : X) :
    H.map (v.unit.app M ≫ t.inv.app (P.obj M)) ≫
      a.hom.app (P.obj M) ≫ J'.map (b.hom.app M) =
        v'.unit.app (H.obj M) ≫ t'.inv.app (P'.obj (H.obj M)) := by
  apply (cancel_mono (t'.hom.app (P'.obj (H.obj M)))).1
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [t'.hom.naturality]
  rw [← reassoc_of% (ht (P.obj M)), ← H.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  erw [H.map_id, Category.id_comp]
  exact hv M

private theorem projectorMapWordApp
    {A X : Type*} [Category A] [Category X]
    {P : X ⥤ A} {J D : A ⥤ X} (v : P ⊣ D) (e : D ⟶ J) (M : X) :
    (v.unit ≫ Functor.whiskerLeft P e).app M =
      v.unit.app M ≫ e.app (P.obj M) := by
  rfl

private theorem projectorComparisonOfWords
    {A X A' X' : Type*} [Category A] [Category X] [Category A'] [Category X']
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    {J' : A' ⥤ X'} {P' : X' ⥤ A'} {D' : A' ⥤ X'}
    (v : P ⊣ D) (v' : P' ⊣ D') (F : A ⥤ A') (H : X ⥤ X')
    (a : J ⋙ H ≅ F ⋙ J') (b : P ⋙ F ≅ H ⋙ P') (d : D ⋙ H ≅ F ⋙ D')
    (t : J ≅ D) (t' : J' ≅ D')
    (ht : ∀ N, H.map (t.hom.app N) ≫ d.hom.app N =
      a.hom.app N ≫ t'.hom.app (F.obj N))
    (hv : ∀ M, H.map (v.unit.app M) ≫ d.hom.app (P.obj M) ≫
      D'.map (b.hom.app M) = v'.unit.app (H.obj M))
    (π : 𝟭 X ⟶ P ⋙ J) (π' : 𝟭 X' ⟶ P' ⋙ J')
    (hπ : ∀ M, π.app M = v.unit.app M ≫ t.inv.app (P.obj M))
    (hπ' : ∀ M, π'.app M = v'.unit.app M ≫ t'.inv.app (P'.obj M)) (M : X) :
    H.map (π.app M) ≫ a.hom.app (P.obj M) ≫ J'.map (b.hom.app M) =
      π'.app (H.obj M) := by
  rw [hπ, hπ']
  exact projectorWordComparison v v' F H a b d t t' ht hv M

private theorem clopenWordApp
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    {U : A ⥤ E} {P : E ⥤ D} {Q : A ⥤ B} {S : B ⥤ C}
    {J : C ⥤ B} {B₀ : B ⥤ D} {K₀ K : C ⥤ D} {R₀ R : A ⥤ C}
    (β : U ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c₁ : J ⋙ B₀ ⟶ K₀) (c₂ : K₀ ⟶ K)
    (d₁ : Q ⋙ S ⟶ R₀) (d₂ : R₀ ⟶ R) (M : A) :
    (clopenMateComposite U P Q S J B₀ K R β π (c₁ ≫ c₂) (d₁ ≫ d₂)).app M =
      β.app M ≫ B₀.map (π.app (Q.obj M)) ≫ c₁.app (S.obj (Q.obj M)) ≫
        c₂.app (S.obj (Q.obj M)) ≫ K.map (d₁.app M ≫ d₂.app M) := by
  rw [clopenMateComposite_app]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem mapWordOfTail {A D : Type*} [Category A] [Category D]
    (H : A ⥤ D) {X Y Z : A} {P Q T L E F : D}
    (α : X ⟶ Z) (β : X ⟶ Y) (v : Y ⟶ Z)
    (k : H.obj Z ⟶ P) (r : P ⟶ L)
    (b : H.obj Y ⟶ Q) (q : Q ⟶ T) (tail : T ⟶ L)
    (e₁ : H.obj X ⟶ E) (e₂ : E ⟶ F) (γ : F ⟶ T) (α' : F ⟶ L)
    (hα : α = β ≫ v) (htail : H.map v ≫ k ≫ r = b ≫ q ≫ tail)
    (hβ : H.map β ≫ b ≫ q = e₁ ≫ e₂ ≫ γ) (hα' : α' = γ ≫ tail) :
    H.map α ≫ k ≫ r = e₁ ≫ e₂ ≫ α' := by
  calc
    _ = H.map β ≫ (H.map v ≫ k ≫ r) := by
      rw [hα, H.map_comp, Category.assoc]
    _ = H.map β ≫ (b ≫ q ≫ tail) := congrArg (fun z ↦ H.map β ≫ z) htail
    _ = (H.map β ≫ b ≫ q) ≫ tail := by simp only [Category.assoc]
    _ = (e₁ ≫ e₂ ≫ γ) ≫ tail := congrArg (fun z ↦ z ≫ tail) hβ
    _ = e₁ ≫ e₂ ≫ α' := by rw [hα']; simp only [Category.assoc]

private theorem normalizedSquareNaturality {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
    (α : F ⋙ G ⟶ H ⋙ K) {M N : A} (f : M ⟶ N) :
    G.map (F.map f) ≫ α.app N = α.app M ≫ K.map (H.map f) := α.naturality f

private theorem normalizedLeftNaturality {A B C : Type*}
    [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    (α : F ⋙ G ⟶ H) {M N : A} (f : M ⟶ N) :
    G.map (F.map f) ≫ α.app N = α.app M ≫ H.map f := α.naturality f

private theorem normalizedIdentityNaturality {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (α : 𝟭 A ⟶ F ⋙ G) {M N : A} (f : M ⟶ N) :
    f ≫ α.app N = α.app M ≫ G.map (F.map f) := α.naturality f

private theorem normalizedMapTwoThree {A D : Type*} [Category A] [Category D]
    (H : A ⥤ D) {X Y Z P Q : A}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ P} {d : P ⟶ Q} {e : Q ⟶ Z}
    (h : a ≫ b = c ≫ d ≫ e) :
    H.map a ≫ H.map b = H.map c ≫ H.map d ≫ H.map e := by
  simpa only [H.map_comp] using congrArg H.map h

private theorem normalizedMapThreeOne {A D : Type*} [Category A] [Category D]
    (H : A ⥤ D) {X Y Z P : A}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ P} {d : X ⟶ P}
    (h : a ≫ b ≫ c = d) : H.map a ≫ H.map b ≫ H.map c = H.map d := by
  simpa only [H.map_comp] using congrArg H.map h

private theorem normalizedMapTwoTwo {A D : Type*} [Category A] [Category D]
    (H : A ⥤ D) {X Y Z P : A}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ P} {d : P ⟶ Z}
    (h : a ≫ b = c ≫ d) : H.map a ≫ H.map b = H.map c ≫ H.map d := by
  simpa only [H.map_comp] using congrArg H.map h

private theorem normalizedMapTriple {A D : Type*} [Category A] [Category D]
    (H : A ⥤ D) {X Y Z P : A} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ P) :
    H.map (a ≫ b ≫ c) = H.map a ≫ H.map b ≫ H.map c := by
  simp only [H.map_comp]

private theorem tailHomWord {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ C₀ C₁ C₂ C₃ E Q L : D}
    (v : A₀ ⟶ A₃) (a : A₀ ⟶ A₁) (c : A₁ ⟶ A₂) (d : A₂ ⟶ A₃)
    (k : A₃ ⟶ B₃) (r : B₃ ⟶ L) (k₀ : A₂ ⟶ B₂) (gd : B₂ ⟶ B₃)
    (t : A₀ ⟶ B₀) (t₁ : A₁ ⟶ B₁) (fp : B₀ ⟶ B₁)
    (j : B₁ ⟶ C₀) (cc : C₀ ⟶ B₂) (ss : B₂ ⟶ C₂)
    (jj : C₀ ⟶ C₁) (cc₂ : C₁ ⟶ C₂) (π : B₀ ⟶ C₁)
    (sq : C₂ ⟶ Q) (dd : Q ⟶ L) (jq : C₁ ⟶ C₃)
    (cc₃ : C₃ ⟶ Q) (tq : B₀ ⟶ E) (πq : E ⟶ C₃)
    (hv : v = a ≫ c ≫ d) (hc : c ≫ k₀ = t₁ ≫ j ≫ cc)
    (hn₁ : a ≫ t₁ = t ≫ fp) (hn₂ : d ≫ k = k₀ ≫ gd)
    (hd : gd ≫ r = ss ≫ sq ≫ dd) (hn₃ : cc ≫ ss = jj ≫ cc₂)
    (hπ : fp ≫ j ≫ jj = π) (hn₄ : cc₂ ≫ sq = jq ≫ cc₃)
    (hn₅ : π ≫ jq = tq ≫ πq) :
    v ≫ k ≫ r = t ≫ tq ≫ πq ≫ cc₃ ≫ dd := by
  rw [hv]
  simp only [Category.assoc]
  rw [reassoc_of% hn₂, hd, reassoc_of% hc, reassoc_of% hn₁,
    reassoc_of% hn₃, reassoc_of% hπ, reassoc_of% hn₄, reassoc_of% hn₅]

/-- The intrinsic ordinary projector is an actual composite of natural transformations.
Source: Stacks 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
def scalarOrdinaryPi
    (κ : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
      StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (StrictTower.Towers B X) ⟶
      StrictTower.towerPullback B s ⋙ StrictTower.towerJ B s :=
  (scalarTowerAdj B s).unit ≫
    Functor.whiskerLeft (StrictTower.towerPullback B s) (κ s).inv

/-- The intrinsic proper/open arrows and their compatibility with scalar restriction.
Source: Stacks 03D8, 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
structure OrdinaryScalarProperOpen (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) where
  /-- The constant-tower cartesian open comparison, fixed by its transpose below. -/
  beta : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : gU ≫ j = j' ≫ g) (_hsq : IsPullback gU j' j g),
    StrictTower.towerJ B j ⋙ StrictTower.towerPullback B g ≅
      StrictTower.towerPullback B gU ⋙ StrictTower.towerJ B j'
  /-- The inverse beta is exactly the open-unit transpose. -/
  beta_unit : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : StrictTower.Towers B U),
    ((scalarTowerOpenAdj B j').homEquiv _ _)
        ((beta gU j' j g h hsq).inv.app M) =
      (StrictTower.towerPullback B gU).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((StrictTower.towerJ B j).obj M)
  /-- Restriction preserves that canonical beta, before deriving or evaluation. -/
  beta_comparison : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U),
    (C.rho X').map ((moduleBeta R φ gU j' j g h hsq).hom.app M) ≫
        (G.a j').hom.app ((pull R φ gU).obj M) ≫
        (StrictTower.towerJ B j').map ((G.b gU).hom.app M) =
      (G.b g).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
        (beta gU j' j g h hsq).hom.app ((C.rho U).obj M)
  /-- The clopen extension/direct comparison, normalized by the inverse open unit. -/
  clopen : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
    StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s
  /-- This equation specifies the canonical open-to-direct map, rather than an arbitrary iso. -/
  clopen_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (N : StrictTower.Towers B U),
    (scalarTowerOpenAdj B s).unit.app N ≫
        ((scalarTowerAdj B s).homEquiv _ _).symm ((clopen s).hom.app N) = 𝟙 N
  /-- Preservation of the actual ordinary clopen projector. -/
  pi_comparison : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (M : Modules R φ X),
    (C.rho X).map ((modulePi R φ s).app M) ≫
        (G.a s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.towerJ B s).map ((G.b s).hom.app M) =
      (scalarOrdinaryPi B clopen s).app ((C.rho X).obj M)
  /-- The constant ordinary alpha, specified by its full clopen word below. -/
  alpha : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k
  /-- Alpha is beta, then the clopen projector, then the canonical compositors. -/
  alpha_eq : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S),
    (alpha k r p i h).app M =
      (beta (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B clopen (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app M)
  /-- Preservation of the intrinsic ordinary alpha for every proper/open square. -/
  alpha_comparison : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S),
    (C.rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
        (G.a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
      (G.b p).hom.app ((extension R φ i).obj M) ≫
        (StrictTower.towerPullback B p).map ((G.a i).hom.app M) ≫
        (alpha k r p i h).app ((C.rho S).obj M)

private def scalarBeta {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) :
    StrictTower.towerJ B j ⋙ StrictTower.towerPullback B g ≅
      StrictTower.towerPullback B a ⋙ StrictTower.towerJ B j' :=
  StrictTower.openBetaTower B a j' j g h sq

private theorem scalarSquare_termwise {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (h : a ≫ j = j' ≫ g) :
    termwiseIso (I := ℕᵒᵖ) (StrictTower.moduleSquareG B a j' j g h) =
      scalarTowerSquare B a j' j g h := by
  unfold scalarTowerSquare
  exact (termwiseIso_square_eq (StrictTower.moduleSquareG B a j' j g h)).trans
    (StrictTower.towerSquare_moduleSquareG B a j' j g h)

private theorem scalarBeta_unit {U' U X' X : Scheme.{u}} (a : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (M : StrictTower.Towers B U) :
    (scalarTowerOpenAdj B j').homEquiv _ _ ((scalarBeta B a j' j g h sq).inv.app M) =
      (StrictTower.towerPullback B a).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B a j' j g h).inv.app ((StrictTower.towerJ B j).obj M) := by
  have ht := termwiseBetaUnit (StrictTower.moduleJAdj B j) (StrictTower.moduleJAdj B j')
    (StrictTower.modulePullback B a) (StrictTower.modulePullback B g)
    (StrictTower.openBetaModule B a j' j g h sq)
    (StrictTower.moduleSquareG B a j' j g h)
    (StrictTower.openBetaModule_normalized B a j' j g h sq).2 M
  exact ht.trans (compIsoInvApp_eq
    (termwiseIso (I := ℕᵒᵖ) (StrictTower.moduleSquareG B a j' j g h))
    (scalarTowerSquare B a j' j g h) (scalarSquare_termwise B a j' j g h)
    ((StrictTower.towerJ B j).obj M)
    ((StrictTower.towerPullback B a).map ((scalarTowerOpenAdj B j).unit.app M)))

private def scalarClopen {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (@asIso _ _ _ _ (StrictTower.clopenModuleToDirect B s)
      (StrictTower.clopenModuleToDirect_isIso B s))

private theorem scalarClopen_unit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : StrictTower.Towers B U) :
    (scalarTowerOpenAdj B s).unit.app N ≫
        ((scalarTowerAdj B s).homEquiv _ _).symm ((scalarClopen B s).hom.app N) = 𝟙 N := by
  have h (M : StrictTower.Modules B U) :
      (StrictTower.moduleJAdj B s).unit.app M ≫
        ((StrictTower.clopenModuleAdj B s).homEquiv _ _).symm
          ((StrictTower.clopenModuleToDirect B s).app M) = 𝟙 M := by
    have := StrictTower.clopenModule_openUnit_isIso B s
    unfold StrictTower.clopenModuleToDirect
    exact clopenAdjunctionUnitNormalization (StrictTower.moduleJAdj B s)
      (StrictTower.clopenModuleAdj B s) M
  exact termwiseClopenUnit (I := ℕᵒᵖ) (StrictTower.moduleJAdj B s)
    (StrictTower.clopenModuleAdj B s) (StrictTower.clopenModuleToDirect B s) h N

private def scalarRComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    StrictTower.towerDirectImage B f ⋙ StrictTower.towerDirectImage B g ≅
      StrictTower.towerDirectImage B (f ≫ g) :=
  (Functor.whiskeringRightObjCompIso _ _) ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (StrictTower.moduleRComp B f g)

private theorem scalarRComp_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : StrictTower.Towers B X) (n : ℕᵒᵖ) :
    ((scalarRComp B f g).hom.app M).app n =
      (StrictTower.moduleRComp B f g).hom.app (M.obj n) := by
  change 𝟙 _ ≫ (StrictTower.moduleRComp B f g).hom.app (M.obj n) = _
  exact Category.id_comp _

private def scalarSection (C : OrdinaryScalarRestriction R φ B ψ)
    (X : Scheme.{u}) (n : ℕ) (M : Modules R φ X) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) :
    M.val.obj (op (n, H.unop)) :=
  ((C.level X n).hom.app M).val.app H x

private theorem scalarSection_map (C : OrdinaryScalarRestriction R φ B ψ)
    {X : Scheme.{u}} (n : ℕ) {M N : Modules R φ X} (q : M ⟶ N) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) :
    scalarSection R φ B ψ C X n N H ((((C.rho X).map q).app (op n)).val.app H x) =
      q.val.app (op (n, H.unop)) (scalarSection R φ B ψ C X n M H x) := by
  exact ConcreteCategory.congr_hom (C := ModuleCat ((StrictTower.coefficients B X).obj.obj H))
    (congrArg (fun t ↦ t.val.app H) ((C.level X n).hom.naturality q)) x

private theorem scalarSection_restrict (C : OrdinaryScalarRestriction R φ B ψ)
    {X : Scheme.{u}} (n : ℕ) (M : Modules R φ X) {H K : X.ProEtᵒᵖ} (q : H ⟶ K)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) :
    scalarSection R φ B ψ C X n M K
        ((((C.rho X).obj M).obj (op n)).val.map q x) =
      M.val.map (Prod.mkHom (𝟙 n) q.unop).op
        (scalarSection R φ B ψ C X n M H x) := by
  exact PresheafOfModules.naturality_apply ((C.level X n).hom.app M).val q x

private theorem scalarSection_direct (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H) :
    scalarSection R φ B ψ C X n M ((Scheme.proEtaleBaseChange f).op.obj H)
        ((((G.d f).hom.app M).app (op n)).val.app H x) =
      scalarSection R φ B ψ C Y n ((push R φ f).obj M) H x := by
  apply eq_of_heq
  exact (C.level_sections X n M ((Scheme.proEtaleBaseChange f).op.obj H) _).trans
    ((G.d_sections f M n H x).trans (C.level_sections Y n _ H x).symm)

private theorem scalarDirect_comp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules R φ X) :
    (C.rho Z).map ((modulePComp R φ f g).hom.app M) ≫
        (G.d (f ≫ g)).hom.app M =
      (G.d g).hom.app ((push R φ f).obj M) ≫
        (StrictTower.towerDirectImage B g).map ((G.d f).hom.app M) ≫
        (scalarRComp B f g).hom.app ((C.rho X).obj M) := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono ((StrictTower.moduleDirectImage B (f ≫ g)).map
    ((C.level X n.unop).hom.app M))).1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro H
  ext x
  simp only [NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change scalarSection R φ B ψ C X n.unop M
      ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj H)
      (((((G.d (f ≫ g)).hom.app M).app n).val.app H)
        (((((C.rho Z).map ((modulePComp R φ f g).hom.app M)).app n).val.app H) x)) = _
  rw [scalarSection_direct, scalarSection_map]
  erw [(modulePComp_existsUnique R φ f g).choose_spec.1]
  change _ = scalarSection R φ B ψ C X n.unop M
    ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj H) _
  rw [scalarRComp_hom_app]
  change _ = scalarSection R φ B ψ C X n.unop M
    ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj H)
    (((StrictTower.moduleRComp B f g).hom.app (((C.rho X).obj M).obj n)).val.app H
      (((((G.d f).hom.app M).app n).val.app
        ((Scheme.proEtaleBaseChange g).op.obj H))
        (((((G.d g).hom.app ((push R φ f).obj M)).app n).val.app H) x)))
  rw [StrictTower.directComp_hom_apply f g B]
  erw [scalarSection_restrict]
  erw [scalarSection_direct, scalarSection_direct]
  rfl

private theorem scalarTowerComp_mate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((scalarTowerAdj B g).comp (scalarTowerAdj B f))
      (scalarTowerAdj B (f ≫ g)) (StrictTower.towerGComp B f g).hom =
        (scalarRComp B f g).hom := by
  unfold scalarTowerAdj scalarRComp StrictTower.towerGComp StrictTower.moduleGComp
  exact termwiseCompMate (I := ℕᵒᵖ)
    (Scheme.proEtaleRingModuleAdjunction g (StrictTower.coefficients B Z)
      (StrictTower.coefficients B Y) (StrictTower.constantRingIso B g))
    (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (StrictTower.coefficients B Z)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B (f ≫ g)))
    (StrictTower.moduleRComp B f g)

private theorem scalarPull_compSquare (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((TwoSquare.mk _ _ _ _ (G.b g).inv).vComp
      (TwoSquare.mk _ _ _ _ (G.b f).inv)).whiskerRight
        (StrictTower.towerGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (G.b (f ≫ g)).inv).whiskerLeft
        (moduleGComp R φ f g).hom := by
  refine StrictTower.finiteMateSquare
    ((moduleAdj R φ g).comp (moduleAdj R φ f)) (moduleAdj R φ (f ≫ g))
    ((scalarTowerAdj B g).comp (scalarTowerAdj B f)) (scalarTowerAdj B (f ≫ g))
    ((TwoSquare.mk _ _ _ _ (G.b g).inv).vComp
      (TwoSquare.mk _ _ _ _ (G.b f).inv))
    (TwoSquare.mk _ _ _ _ (G.b (f ≫ g)).inv)
    (StrictTower.towerGComp B f g).hom (moduleGComp R φ f g).hom ?_
  rw [mateEquiv_hcomp]
  have hb {A D : Scheme.{u}} (q : A ⟶ D) :
      mateEquiv (moduleAdj R φ q) (scalarTowerAdj B q) (G.b q).inv =
        TwoSquare.mk _ _ _ _ (G.d q).hom := by
    exact NatTrans.ext (funext (fun M ↦ NatTrans.congr_app (G.mate q) M))
  rw [hb g, hb f, hb (f ≫ g), scalarTowerComp_mate]
  have hc : conjugateEquiv ((moduleAdj R φ g).comp (moduleAdj R φ f))
      (moduleAdj R φ (f ≫ g)) (moduleGComp R φ f g).hom =
        (modulePComp R φ f g).hom := by
    unfold moduleGComp
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  rw [hc]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
    using (scalarDirect_comp R φ B ψ C G f g M).symm

private theorem scalarPull_square (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X)
    (g : X' ⟶ X) (h : a ≫ j = j' ≫ g) (M : Modules R φ X) :
    (scalarTowerSquare B a j' j g h).inv.app ((C.rho X).obj M) ≫
      (StrictTower.towerPullback B j').map ((G.b g).inv.app M) ≫
      (G.b j').inv.app ((pull R φ g).obj M) =
    (StrictTower.towerPullback B a).map ((G.b j).inv.app M) ≫
      (G.b a).inv.app ((pull R φ j).obj M) ≫
      (C.rho U').map ((moduleSquareG R φ a j' j g h).inv.app M) := by
  let p := (TwoSquare.mk _ _ _ _ (G.b j).inv).vComp
    (TwoSquare.mk _ _ _ _ (G.b a).inv)
  let p' := (TwoSquare.mk _ _ _ _ (G.b g).inv).vComp
    (TwoSquare.mk _ _ _ _ (G.b j').inv)
  have hw : (moduleSquareG R φ a j' j g h).symm =
      (moduleGComp R φ a j).symm ≪≫ eqToIso (congrArg (pull R φ) h) ≪≫
        moduleGComp R φ j' g := by
    rw [moduleSquareG_eq]
    have he : (eqToIso (congrArg (pull R φ) h.symm)).symm =
        eqToIso (congrArg (pull R φ) h) := by
      rfl
    simp only [Iso.trans_symm, Iso.symm_symm_eq, he, Iso.trans_assoc]
  have hs := StrictTower.finiteSquareTransport (StrictTower.towerPullback B) (pull R φ)
    (C.rho X) (C.rho U') (fun f ↦ TwoSquare.mk _ _ _ _ (G.b f).inv) h
    (StrictTower.towerGComp B a j) (StrictTower.towerGComp B j' g)
    (moduleGComp R φ a j) (moduleGComp R φ j' g) p p'
    (scalarPull_compSquare R φ B ψ C G a j) (scalarPull_compSquare R φ B ψ C G j' g)
    (scalarTowerSquare B a j' j g h) (moduleSquareG R φ a j' j g h).symm rfl hw
  exact StrictTower.finiteSquareComponents
    (C.rho X) (C.rho U) (C.rho X') (C.rho U')
    (pull R φ j) (pull R φ g) (pull R φ a) (pull R φ j')
    (StrictTower.towerPullback B j) (StrictTower.towerPullback B g)
    (StrictTower.towerPullback B a) (StrictTower.towerPullback B j')
    (G.b j).inv (G.b g).inv (G.b a).inv (G.b j').inv
    (scalarTowerSquare B a j' j g h) (moduleSquareG R φ a j' j g h).symm hs M

private theorem scalarPull_comp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules R φ Z) :
    (C.rho X).map ((moduleGComp R φ f g).inv.app M) ≫ (G.b (f ≫ g)).hom.app M =
      (G.b f).hom.app ((pull R φ g).obj M) ≫
        (StrictTower.towerPullback B f).map ((G.b g).hom.app M) ≫
        (StrictTower.towerGComp B f g).inv.app ((C.rho Z).obj M) := by
  have he :
      (Functor.isoWhiskerLeft (C.rho Z) (StrictTower.towerGComp B f g)) ≪≫
        Functor.isoWhiskerRight (G.b g).symm (StrictTower.towerPullback B f) ≪≫
        Functor.isoWhiskerLeft (pull R φ g) (G.b f).symm =
      (G.b (f ≫ g)).symm ≪≫ Functor.isoWhiskerRight (moduleGComp R φ f g) (C.rho X) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      TwoSquare.mk, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
      using congrArg (fun t ↦ t.app N) (scalarPull_compSquare R φ B ψ C G f g)
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Category.assoc] using congrArg (fun e ↦ e.inv.app M) he.symm

private theorem scalarOpen_mate (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv (moduleJAdj R φ j) (scalarTowerOpenAdj B j)
      (TwoSquare.mk _ _ _ _ (G.a j).inv) =
      TwoSquare.mk _ _ _ _ (G.b j).hom := by
  apply (mateEquiv (moduleJAdj R φ j) (scalarTowerOpenAdj B j)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext M
  apply ((scalarTowerOpenAdj B j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm (moduleJAdj R φ j) (scalarTowerOpenAdj B j)
    (TwoSquare.mk _ _ _ _ (G.b j).hom) M
  change (C.rho U).map ((moduleJAdj R φ j).unit.app M) ≫
      (G.b j).hom.app ((extension R φ j).obj M) =
    (scalarTowerOpenAdj B j).unit.app ((C.rho U).obj M) ≫
      (StrictTower.towerPullback B j).map
        (((mateEquiv (moduleJAdj R φ j) (scalarTowerOpenAdj B j)).symm
          (TwoSquare.mk _ _ _ _ (G.b j).hom)).app M) at hu
  rw [← hu]
  apply (cancel_mono ((StrictTower.towerPullback B j).map ((G.a j).hom.app M))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(StrictTower.towerPullback B j).map_id, Category.comp_id]
  exact (G.open_unit j M).symm

private theorem varyingOpenComp_mate {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv ((moduleJAdj R φ j).comp (moduleJAdj R φ k))
      (moduleJAdj R φ (j ≫ k)) (moduleJComp R φ j k).inv =
        (moduleGComp R φ j k).inv := by
  unfold moduleJComp
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

private theorem scalarOpenComp_mate {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv ((scalarTowerOpenAdj B j).comp (scalarTowerOpenAdj B k))
      (scalarTowerOpenAdj B (j ≫ k)) (scalarTowerOpenComp B j k).inv =
        (StrictTower.towerGComp B j k).inv := by
  unfold scalarTowerOpenComp
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

private theorem scalarOpen_comp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : Modules R φ U) :
    (C.rho X).map ((moduleJComp R φ j k).hom.app M) ≫ (G.a (j ≫ k)).hom.app M =
      (G.a k).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerJ B k).map ((G.a j).hom.app M) ≫
        (scalarTowerOpenComp B j k).hom.app ((C.rho U).obj M) := by
  have hc : ((TwoSquare.mk _ _ _ _ (G.a j).inv).vComp
      (TwoSquare.mk _ _ _ _ (G.a k).inv)).whiskerRight
        (scalarTowerOpenComp B j k).inv =
      (TwoSquare.mk _ _ _ _ (G.a (j ≫ k)).inv).whiskerLeft
        (moduleJComp R φ j k).inv := by
    apply StrictTower.finiteMateSquare
      ((moduleJAdj R φ j).comp (moduleJAdj R φ k)) (moduleJAdj R φ (j ≫ k))
      ((scalarTowerOpenAdj B j).comp (scalarTowerOpenAdj B k))
      (scalarTowerOpenAdj B (j ≫ k))
    rw [mateEquiv_hcomp, scalarOpen_mate, scalarOpen_mate, scalarOpen_mate]
    rw [scalarOpenComp_mate, varyingOpenComp_mate]
    refine NatTrans.ext (funext fun N ↦ ?_)
    simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
      using (scalarPull_comp R φ B ψ C G j k N).symm
  have he : Functor.isoWhiskerLeft (C.rho U) (scalarTowerOpenComp B j k).symm ≪≫
        Functor.isoWhiskerRight (G.a j).symm (StrictTower.towerJ B k) ≪≫
        Functor.isoWhiskerLeft (extension R φ j) (G.a k).symm =
      (G.a (j ≫ k)).symm ≪≫
        Functor.isoWhiskerRight (moduleJComp R φ j k).symm (C.rho X) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      TwoSquare.mk, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
      using congrArg (fun t ↦ t.app N) hc
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Category.assoc] using congrArg (fun e ↦ e.inv.app M) he.symm

private theorem scalarBeta_mate {U' U X' X : Scheme.{u}} (a : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    mateEquiv (scalarTowerOpenAdj B j) (scalarTowerOpenAdj B j')
      (TwoSquare.mk _ _ _ _ (scalarBeta B a j' j g h sq).inv) =
        TwoSquare.mk _ _ _ _ (scalarTowerSquare B a j' j g h).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  have ht := scalarBeta_unit B a j' j g h sq M
  rw [Adjunction.homEquiv_unit] at ht
  exact ht.symm

private theorem varyingBeta_mate {U' U X' X : Scheme.{u}} (a : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    mateEquiv (moduleJAdj R φ j) (moduleJAdj R φ j')
      (TwoSquare.mk _ _ _ _ (moduleBeta R φ a j' j g h sq).inv) =
        TwoSquare.mk _ _ _ _ (moduleSquareG R φ a j' j g h).inv := by
  apply mateEquiv_eq_of_unit
  intro N
  have hh := ((moduleJAdj R φ j').homEquiv _ _).apply_symm_apply
    ((pull R φ a).map ((moduleJAdj R φ j).unit.app N) ≫
      (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj N))
  simpa only [Adjunction.homEquiv_unit, moduleBeta, Iso.symm_inv, asIso_hom,
    moduleBetaInv, moduleBetaInvApp, TwoSquare.mk, Functor.id_obj,
    Functor.comp_obj] using hh.symm

private theorem scalarBeta_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X)
    (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (M : Modules R φ U) :
    (C.rho X').map ((moduleBeta R φ a j' j g h sq).hom.app M) ≫
      (G.a j').hom.app ((pull R φ a).obj M) ≫
      (StrictTower.towerJ B j').map ((G.b a).hom.app M) =
    (G.b g).hom.app ((extension R φ j).obj M) ≫
      (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
      (scalarBeta B a j' j g h sq).hom.app ((C.rho U).obj M) := by
  exact (forwardMateCube
      (DY := Modules R φ U) (DX := Modules R φ X)
      (DY' := Modules R φ U') (DX' := Modules R φ X')
      (EY := StrictTower.Towers B U) (EX := StrictTower.Towers B X)
      (EY' := StrictTower.Towers B U') (EX' := StrictTower.Towers B X')
      (Lf := extension R φ j) (Rf := pull R φ j)
      (Lf' := extension R φ j') (Rf' := pull R φ j')
      (Mf := StrictTower.towerJ B j) (Sf := StrictTower.towerPullback B j)
      (Mf' := StrictTower.towerJ B j') (Sf' := StrictTower.towerPullback B j')
      (Gr := pull R φ a) (Hr := pull R φ g)
      (Gs := StrictTower.towerPullback B a) (Hs := StrictTower.towerPullback B g)
      (PY := C.rho U) (PX := C.rho X) (PY' := C.rho U') (PX' := C.rho X')
    (moduleJAdj R φ j) (moduleJAdj R φ j')
    (scalarTowerOpenAdj B j) (scalarTowerOpenAdj B j')
    (moduleBeta R φ a j' j g h sq).symm (scalarBeta B a j' j g h sq)
    (G.a j).symm (G.a j').symm (G.b a).symm (G.b g).symm
    (G.b j).symm (G.b j').symm
    (moduleSquareG R φ a j' j g h).inv (scalarTowerSquare B a j' j g h).inv
    (scalarOpen_mate R φ B ψ C G j) (scalarOpen_mate R φ B ψ C G j')
    (varyingBeta_mate R φ a j' j g h sq)
    (scalarBeta_mate B a j' j g h sq)
    (scalarPull_square R φ B ψ C G a j' j g h) M)

private theorem scalarOpenUnit_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : IsIso (scalarTowerOpenAdj B s).unit := by
  have := StrictTower.clopenModule_openUnit_isIso B s
  unfold scalarTowerOpenAdj
  exact StrictTower.tower_unit_iso (StrictTower.moduleJAdj B s)

private theorem scalarClopen_word {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : StrictTower.Towers B U) :
    (scalarClopen B s).hom.app N =
      (scalarTowerAdj B s).unit.app ((StrictTower.towerJ B s).obj N) ≫
        (StrictTower.towerDirectImage B s).map
          (@inv _ _ _ _ ((scalarTowerOpenAdj B s).unit.app N)
            (by
              have := scalarOpenUnit_isIso B s
              infer_instance)) := by
  have := scalarOpenUnit_isIso B s
  exact clopenWordOfUnit (scalarTowerOpenAdj B s) (scalarTowerAdj B s)
    (scalarClopen B s).hom (scalarClopen_unit B s) N

private theorem scalarClopen_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (N : Modules R φ U) :
    (C.rho X).map ((moduleOpenToP R φ s).app N) ≫ (G.d s).hom.app N =
      (G.a s).hom.app N ≫ (scalarClopen B s).hom.app ((C.rho U).obj N) := by
  have := moduleJAdj_unit_isIso R φ s
  have := scalarOpenUnit_isIso B s
  refine clopenComparison (moduleJAdj R φ s) (moduleAdj R φ s)
    (scalarTowerOpenAdj B s) (scalarTowerAdj B s) (C.rho U) (C.rho X)
    (G.a s) (G.b s) (G.d s) (fun L ↦ G.open_unit s L)
    (fun L ↦ OrdinaryScalarAdjunctions.unit R φ B ψ C G s L)
    (moduleOpenToP R φ s) (scalarClopen B s).hom ?_
    (scalarClopen_word B s) N
  intro L
  simp only [moduleOpenToP, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, NatIso.isIso_inv_app, Category.id_comp]
  erw [Category.comp_id]

private theorem varyingPi_word {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (modulePi R φ s).app M = (moduleAdj R φ s).unit.app M ≫
      (@inv _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s)).app
        ((pull R φ s).obj M) := by
  unfold modulePi
  exact projectorMapWordApp (moduleAdj R φ s)
    (@inv _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s)) M

private theorem scalarPi_word {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : StrictTower.Towers B X) :
    (scalarOrdinaryPi B (scalarClopen B) s).app M =
      (scalarTowerAdj B s).unit.app M ≫
        (scalarClopen B s).inv.app ((StrictTower.towerPullback B s).obj M) := by
  unfold scalarOrdinaryPi
  exact projectorMapWordApp (scalarTowerAdj B s) (scalarClopen B s).inv M

private theorem scalarPi_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (M : Modules R φ X) :
    (C.rho X).map ((modulePi R φ s).app M) ≫
      (G.a s).hom.app ((pull R φ s).obj M) ≫
      (StrictTower.towerJ B s).map ((G.b s).hom.app M) =
        (scalarOrdinaryPi B (scalarClopen B) s).app ((C.rho X).obj M) := by
  have hi := moduleOpenToP_isIso R φ s
  exact projectorComparisonOfWords (moduleAdj R φ s) (scalarTowerAdj B s)
    (C.rho U) (C.rho X) (G.a s) (G.b s) (G.d s)
    (@asIso _ _ _ _ (moduleOpenToP R φ s) hi) (scalarClopen B s)
    (fun N ↦ scalarClopen_comparison R φ B ψ C G s N)
    (fun N ↦ OrdinaryScalarAdjunctions.unit R φ B ψ C G s N)
    (modulePi R φ s) (scalarOrdinaryPi B (scalarClopen B) s)
    (varyingPi_word R φ s) (scalarPi_word B s) M

private def scalarAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k :=
  clopenMateComposite (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (pullback.fst p i)) (StrictTower.towerJ B k)
    (StrictTower.towerPullback B r)
    (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (scalarOrdinaryPi B (scalarClopen B) (StrictTower.squareLift k r p i h))
    ((scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom)
    ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
      (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom)

private theorem scalarAlpha_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S) :
    (scalarAlpha B k r p i h).app M =
      (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B (scalarClopen B) (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B)
            (pullback.lift_snd k r h))).hom.app M)  := by
  exact clopenWordApp
    (U := StrictTower.towerJ B i) (P := StrictTower.towerPullback B p)
    (Q := StrictTower.towerPullback B (pullback.snd p i))
    (S := StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
    (J := StrictTower.towerJ B (StrictTower.squareLift k r p i h))
    (B₀ := StrictTower.towerJ B (pullback.fst p i))
    (K := StrictTower.towerJ B k) (R := StrictTower.towerPullback B r)
    (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (scalarOrdinaryPi B (scalarClopen B) (StrictTower.squareLift k r p i h))
    (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom
    (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom
    (StrictTower.towerGComp B (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv
    (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom M

private theorem scalarOpen_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U X : Scheme.{u}} {f g : U ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) (M : Modules R φ U) :
    (C.rho X).map ((moduleJCongr R φ h).hom.app M) ≫ (G.a g).hom.app M =
      (G.a f).hom.app M ≫
        (eqToIso (scalarTowerOpen_congr B h)).hom.app ((C.rho U).obj M) := by
  subst g
  dsimp only [moduleJCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  simp only [(C.rho X).map_id, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem scalarPull_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Modules R φ Y) :
    (C.rho X).map ((eqToIso (congrArg (pull R φ) h)).hom.app M) ≫
      (G.b g).hom.app M =
    (G.b f).hom.app M ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) h)).hom.app ((C.rho Y).obj M) := by
  subst g
  dsimp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  simp only [(C.rho X).map_id, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem scalarOpen_comp_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U V W : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (h : s ≫ b = k) (N : Modules R φ U) :
    (C.rho W).map (((moduleJComp R φ s b).hom ≫
      (moduleJCongr R φ h).hom).app N) ≫ (G.a k).hom.app N =
      (G.a b).hom.app ((extension R φ s).obj N) ≫
        (StrictTower.towerJ B b).map ((G.a s).hom.app N) ≫
        ((scalarTowerOpenComp B s b).hom ≫
          (eqToIso (scalarTowerOpen_congr B h)).hom).app ((C.rho U).obj N) := by
  dsimp only [NatTrans.comp_app]
  rw [Functor.map_comp, Category.assoc,
    scalarOpen_congr R φ B ψ C G, ← Category.assoc, scalarOpen_comp R φ B ψ C G]
  simp only [Category.assoc]

private theorem scalarPull_comp_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {U V W : Scheme.{u}} (s : U ⟶ V) (q : V ⟶ W) (r : U ⟶ W)
    (h : s ≫ q = r) (N : Modules R φ W) :
    (C.rho U).map (((moduleGComp R φ s q).inv ≫
      (eqToIso (congrArg (pull R φ) h)).hom).app N) ≫ (G.b r).hom.app N =
      (G.b s).hom.app ((pull R φ q).obj N) ≫
        (StrictTower.towerPullback B s).map ((G.b q).hom.app N) ≫
        ((StrictTower.towerGComp B s q).inv ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) h)).hom).app
            ((C.rho W).obj N) := by
  dsimp only [NatTrans.comp_app]
  rw [Functor.map_comp, Category.assoc,
    scalarPull_congr R φ B ψ C G h, ← Category.assoc, scalarPull_comp R φ B ψ C G]
  simp only [Category.assoc]

/-- Compare the projector/compositor tail. Eliminate the scheme equalities first,
so the remaining naturality calculation uses reflexive transports. -/
private theorem scalarAlpha_factorTail (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {V X W S : Scheme.{u}} (s : V ⟶ X) (b : X ⟶ W) (q : X ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion b] [IsOpenImmersion k] (ek : s ≫ b = k) (er : s ≫ q = r)
    (M : Modules R φ S) :
    let c : extension R φ s ⋙ extension R φ b ⟶ extension R φ k :=
      (moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom
    let c' : StrictTower.towerJ B s ⋙ StrictTower.towerJ B b ⟶ StrictTower.towerJ B k :=
      (scalarTowerOpenComp B s b).hom ≫
        (eqToIso (scalarTowerOpen_congr B ek)).hom
    let d : pull R φ q ⋙ pull R φ s ⟶ pull R φ r :=
      (moduleGComp R φ s q).inv ≫
        (eqToIso (congrArg (pull R φ) er)).hom
    let d' : StrictTower.towerPullback B q ⋙ StrictTower.towerPullback B s ⟶
        StrictTower.towerPullback B r :=
      (StrictTower.towerGComp B s q).inv ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) er)).hom
    (C.rho W).map
      ((extension R φ b).map ((modulePi R φ s).app ((pull R φ q).obj M)) ≫
        c.app ((pull R φ s).obj ((pull R φ q).obj M)) ≫
        (extension R φ k).map (d.app M)) ≫
      (G.a k).hom.app ((pull R φ r).obj M) ≫
      (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
    (G.a b).hom.app ((pull R φ q).obj M) ≫
      (StrictTower.towerJ B b).map ((G.b q).hom.app M) ≫
      (StrictTower.towerJ B b).map
        ((scalarOrdinaryPi B (scalarClopen B) s).app
          ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
      c'.app ((StrictTower.towerPullback B s).obj
        ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
      (StrictTower.towerJ B k).map (d'.app ((C.rho S).obj M)) := by
  subst k
  subst r
  let c : extension R φ s ⋙ extension R φ b ⟶ extension R φ (s ≫ b) :=
    (moduleJComp R φ s b).hom ≫ (moduleJCongr R φ rfl).hom
  let c' : StrictTower.towerJ B s ⋙ StrictTower.towerJ B b ⟶ StrictTower.towerJ B (s ≫ b) :=
    (scalarTowerOpenComp B s b).hom ≫
      (eqToIso (scalarTowerOpen_congr B rfl)).hom
  let d : pull R φ q ⋙ pull R φ s ⟶ pull R φ (s ≫ q) :=
    (moduleGComp R φ s q).inv ≫
      (eqToIso (congrArg (pull R φ) rfl)).hom
  let d' : StrictTower.towerPullback B q ⋙ StrictTower.towerPullback B s ⟶
      StrictTower.towerPullback B (s ≫ q) :=
    (StrictTower.towerGComp B s q).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) rfl)).hom
  let N := (pull R φ q).obj M
  let Q := (StrictTower.towerPullback B q).obj ((C.rho S).obj M)
  have hn₁ := normalizedSquareNaturality (G.a b).hom ((modulePi R φ s).app N)
  have hn₂ := normalizedSquareNaturality (G.a (s ≫ b)).hom (d.app M)
  have hc := scalarOpen_comp_congr R φ B ψ C G s b (s ≫ b)
    rfl ((pull R φ s).obj N)
  have hπ := normalizedMapThreeOne (StrictTower.towerJ B b)
    (scalarPi_comparison R φ B ψ C G s N)
  have hd := normalizedMapTwoThree (StrictTower.towerJ B (s ≫ b))
    (scalarPull_comp_congr R φ B ψ C G s q (s ≫ q) rfl M)
  have hn₃ := normalizedLeftNaturality c' ((G.b s).hom.app N)
  have hn₄ := normalizedLeftNaturality c'
    ((StrictTower.towerPullback B s).map ((G.b q).hom.app M))
  have hn₅ := normalizedMapTwoTwo (StrictTower.towerJ B b)
    (normalizedIdentityNaturality (scalarOrdinaryPi B (scalarClopen B) s)
      ((G.b q).hom.app M))
  exact tailHomWord (D := StrictTower.Towers B W)
    ((C.rho W).map
      ((extension R φ b).map ((modulePi R φ s).app N) ≫
        c.app ((pull R φ s).obj N) ≫ (extension R φ (s ≫ b)).map (d.app M)))
    ((C.rho W).map ((extension R φ b).map ((modulePi R φ s).app N)))
    ((C.rho W).map (c.app ((pull R φ s).obj N)))
    ((C.rho W).map ((extension R φ (s ≫ b)).map (d.app M)))
    ((G.a (s ≫ b)).hom.app ((pull R φ (s ≫ q)).obj M))
    ((StrictTower.towerJ B (s ≫ b)).map ((G.b (s ≫ q)).hom.app M))
    ((G.a (s ≫ b)).hom.app ((pull R φ s).obj N))
    ((StrictTower.towerJ B (s ≫ b)).map ((C.rho V).map (d.app M)))
    ((G.a b).hom.app N)
    ((G.a b).hom.app ((extension R φ s).obj ((pull R φ s).obj N)))
    ((StrictTower.towerJ B b).map ((C.rho X).map
      ((modulePi R φ s).app N)))
    ((StrictTower.towerJ B b).map ((G.a s).hom.app ((pull R φ s).obj N)))
    (c'.app ((C.rho V).obj ((pull R φ s).obj N)))
    ((StrictTower.towerJ B (s ≫ b)).map ((G.b s).hom.app N))
    ((StrictTower.towerJ B b).map
      ((StrictTower.towerJ B s).map ((G.b s).hom.app N)))
    (c'.app ((StrictTower.towerPullback B s).obj ((C.rho X).obj N)))
    ((StrictTower.towerJ B b).map
      ((scalarOrdinaryPi B (scalarClopen B) s).app ((C.rho X).obj N)))
    ((StrictTower.towerJ B (s ≫ b)).map
      ((StrictTower.towerPullback B s).map ((G.b q).hom.app M)))
    ((StrictTower.towerJ B (s ≫ b)).map (d'.app ((C.rho S).obj M)))
    ((StrictTower.towerJ B b).map ((StrictTower.towerJ B s).map
      ((StrictTower.towerPullback B s).map ((G.b q).hom.app M))))
    (c'.app ((StrictTower.towerPullback B s).obj Q))
    ((StrictTower.towerJ B b).map ((G.b q).hom.app M))
    ((StrictTower.towerJ B b).map
      ((scalarOrdinaryPi B (scalarClopen B) s).app Q))
    (normalizedMapTriple _ _ _ _) hc hn₁ hn₂ hd hn₃.symm hπ hn₄.symm hn₅.symm

/-- Combine tail compatibility with a compatible first factor. Composite functor
objects are retained in the input types to match the defining component equations. -/
private theorem scalarAlpha_factorWord (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {V X W S : Scheme.{u}} (s : V ⟶ X) (b : X ⟶ W) (q : X ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion b] [IsOpenImmersion k] (ek : s ≫ b = k) (er : s ≫ q = r)
    (M : Modules R φ S) :
    let c : extension R φ s ⋙ extension R φ b ⟶ extension R φ k :=
      (moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom
    let c' : StrictTower.towerJ B s ⋙ StrictTower.towerJ B b ⟶ StrictTower.towerJ B k :=
      (scalarTowerOpenComp B s b).hom ≫
        (eqToIso (scalarTowerOpen_congr B ek)).hom
    let d : pull R φ q ⋙ pull R φ s ⟶ pull R φ r :=
      (moduleGComp R φ s q).inv ≫
        (eqToIso (congrArg (pull R φ) er)).hom
    let d' : StrictTower.towerPullback B q ⋙ StrictTower.towerPullback B s ⟶
        StrictTower.towerPullback B r :=
      (StrictTower.towerGComp B s q).inv ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) er)).hom
    ∀ {Y : Modules R φ W} {Y' Z : StrictTower.Towers B W}
      (α : Y ⟶ (pull R φ r ⋙ extension R φ k).obj M)
      (α' : Y' ⟶ (StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k).obj
        ((C.rho S).obj M))
      (β : Y ⟶ (pull R φ q ⋙ extension R φ b).obj M)
      (β' : Y' ⟶ (StrictTower.towerPullback B q ⋙ StrictTower.towerJ B b).obj
        ((C.rho S).obj M))
      (e₁ : (C.rho W).obj Y ⟶ Z) (e₂ : Z ⟶ Y'),
      α = β ≫
        (extension R φ b).map ((modulePi R φ s).app ((pull R φ q).obj M)) ≫
        c.app ((pull R φ s).obj ((pull R φ q).obj M)) ≫
        (extension R φ k).map (d.app M) →
      α' = β' ≫
        (StrictTower.towerJ B b).map
          ((scalarOrdinaryPi B (scalarClopen B) s).app
            ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
        c'.app ((StrictTower.towerPullback B s).obj
          ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
        (StrictTower.towerJ B k).map (d'.app ((C.rho S).obj M)) →
      (C.rho W).map β ≫ (G.a b).hom.app ((pull R φ q).obj M) ≫
        (StrictTower.towerJ B b).map ((G.b q).hom.app M) = e₁ ≫ e₂ ≫ β' →
      (C.rho W).map α ≫ (G.a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((G.b r).hom.app M) = e₁ ≫ e₂ ≫ α' := by
  dsimp only
  intro Y Y' Z α α' β β' e₁ e₂ hα hα' hβ
  subst k
  subst r
  let c : extension R φ s ⋙ extension R φ b ⟶ extension R φ (s ≫ b) :=
    (moduleJComp R φ s b).hom ≫ (moduleJCongr R φ rfl).hom
  let c' : StrictTower.towerJ B s ⋙ StrictTower.towerJ B b ⟶ StrictTower.towerJ B (s ≫ b) :=
    (scalarTowerOpenComp B s b).hom ≫
      (eqToIso (scalarTowerOpen_congr B rfl)).hom
  let d : pull R φ q ⋙ pull R φ s ⟶ pull R φ (s ≫ q) :=
    (moduleGComp R φ s q).inv ≫
      (eqToIso (congrArg (pull R φ) rfl)).hom
  let d' : StrictTower.towerPullback B q ⋙ StrictTower.towerPullback B s ⟶
      StrictTower.towerPullback B (s ≫ q) :=
    (StrictTower.towerGComp B s q).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) rfl)).hom
  let N := (pull R φ q).obj M
  let Q := (StrictTower.towerPullback B q).obj ((C.rho S).obj M)
  have ht := scalarAlpha_factorTail R φ B ψ C G s b q (s ≫ b) (s ≫ q) rfl rfl M
  exact mapWordOfTail (A := Modules R φ W) (D := StrictTower.Towers B W) (C.rho W)
    α
    β
    ((extension R φ b).map ((modulePi R φ s).app ((pull R φ q).obj M)) ≫
      c.app ((pull R φ s).obj ((pull R φ q).obj M)) ≫
      (extension R φ (s ≫ b)).map (d.app M))
    ((G.a (s ≫ b)).hom.app ((pull R φ (s ≫ q)).obj M))
    ((StrictTower.towerJ B (s ≫ b)).map ((G.b (s ≫ q)).hom.app M))
    ((G.a b).hom.app ((pull R φ q).obj M))
    ((StrictTower.towerJ B b).map ((G.b q).hom.app M))
    ((StrictTower.towerJ B b).map
      ((scalarOrdinaryPi B (scalarClopen B) s).app
        ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
      c'.app ((StrictTower.towerPullback B s).obj
        ((StrictTower.towerPullback B q).obj ((C.rho S).obj M))) ≫
      (StrictTower.towerJ B (s ≫ b)).map (d'.app ((C.rho S).obj M)))
    e₁
    e₂
    β'
    α'
    hα ht hβ hα'

private theorem varyingAlpha_factorLift
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : k ≫ p = r ≫ i) :
    moduleAlpha R φ k r p i w = factor
      (pull R φ (pullback.snd p i)) (pull R φ (pullback.lift k r w))
      (extension R φ (pullback.lift k r w))
      (extension R φ (pullback.fst p i)) (extension R φ i ⋙ pull R φ p)
      (pull R φ r) (extension R φ k)
      (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
      (modulePi R φ (pullback.lift k r w))
      ((moduleJComp R φ (pullback.lift k r w) (pullback.fst p i)).hom ≫
        (moduleJCongr R φ (pullback.lift_fst k r w)).hom)
      ((moduleGComp R φ (pullback.lift k r w) (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r w))).hom) := by
  unfold moduleAlpha factor
  rfl

private theorem scalarAlpha_factorLift {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    scalarAlpha B k r p i h =
  clopenMateComposite (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (pullback.lift k r h))
    (StrictTower.towerJ B (pullback.lift k r h))
    (StrictTower.towerJ B (pullback.fst p i)) (StrictTower.towerJ B k)
    (StrictTower.towerPullback B r)
    (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (scalarOrdinaryPi B (scalarClopen B) (pullback.lift k r h))
    ((scalarTowerOpenComp B (pullback.lift k r h) (pullback.fst p i)).hom ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom)
    ((StrictTower.towerGComp B (pullback.lift k r h)
      (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom) := by
  unfold scalarAlpha
  rfl

private theorem varyingAlpha_liftWord {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Modules R φ S) :
    (moduleAlpha R φ k r p i h).app M =
      (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (extension R φ (pullback.fst p i)).map
        ((modulePi R φ (pullback.lift k r h)).app
          ((pull R φ (pullback.snd p i)).obj M)) ≫
      ((moduleJComp R φ (pullback.lift k r h) (pullback.fst p i)).hom ≫
        (moduleJCongr R φ (pullback.lift_fst k r h)).hom).app
          ((pull R φ (pullback.lift k r h)).obj
            ((pull R φ (pullback.snd p i)).obj M)) ≫
      (extension R φ k).map
        (((moduleGComp R φ (pullback.lift k r h) (pullback.snd p i)).inv ≫
          (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom).app M) := by
  exact (NatTrans.congr_app (varyingAlpha_factorLift R φ k r p i h) M).trans
    (factor_app _ _ _ _ _ _ _ _ _ _ _ M)

private theorem clopenWordOfEquality
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    (U : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : U ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) (α : U ⋙ P ⟶ R ⋙ K)
    (hα : α = clopenMateComposite U P Q S J B₀ K R β π c d) (M : A) :
    α.app M = β.app M ≫ B₀.map (π.app (Q.obj M)) ≫
      c.app (S.obj (Q.obj M)) ≫ K.map (d.app M) := by
  subst α
  exact clopenMateComposite_app U P Q S J B₀ K R β π c d M

private theorem scalarAlpha_liftWord {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S) :
    (scalarAlpha B k r p i h).app M =
      (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B (scalarClopen B) (pullback.lift k r h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      ((scalarTowerOpenComp B (pullback.lift k r h) (pullback.fst p i)).hom ≫
        (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom).app
          ((StrictTower.towerPullback B (pullback.lift k r h)).obj
            ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        (((StrictTower.towerGComp B (pullback.lift k r h) (pullback.snd p i)).inv ≫
          (eqToIso (congrArg (StrictTower.towerPullback B)
            (pullback.lift_snd k r h))).hom).app M) := by
  exact clopenWordOfEquality
    (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (pullback.lift k r h))
    (StrictTower.towerJ B (pullback.lift k r h))
    (StrictTower.towerJ B (pullback.fst p i)) (StrictTower.towerJ B k)
    (StrictTower.towerPullback B r)
    (scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (scalarOrdinaryPi B (scalarClopen B) (pullback.lift k r h))
    ((scalarTowerOpenComp B (pullback.lift k r h) (pullback.fst p i)).hom ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom)
    ((StrictTower.towerGComp B (pullback.lift k r h)
      (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom)
    (scalarAlpha B k r p i h) (scalarAlpha_factorLift B k r p i h) M

private theorem scalarAlpha_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S) :
    (C.rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
      (G.a k).hom.app ((pull R φ r).obj M) ≫
      (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
    (G.b p).hom.app ((extension R φ i).obj M) ≫
      (StrictTower.towerPullback B p).map ((G.a i).hom.app M) ≫
      (scalarAlpha B k r p i h).app ((C.rho S).obj M) := by
  exact scalarAlpha_factorWord R φ B ψ C G
    (pullback.lift k r h) (pullback.fst p i) (pullback.snd p i) k r
    (pullback.lift_fst k r h) (pullback.lift_snd k r h) M
    ((moduleAlpha R φ k r p i h).app M)
    ((scalarAlpha B k r p i h).app ((C.rho S).obj M))
    ((moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom.app M)
    ((scalarBeta B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom.app ((C.rho S).obj M))
    ((G.b p).hom.app ((extension R φ i).obj M))
    ((StrictTower.towerPullback B p).map ((G.a i).hom.app M))
    (varyingAlpha_liftWord R φ k r p i h M)
    (scalarAlpha_liftWord B k r p i h ((C.rho S).obj M))
    (scalarBeta_comparison R φ B ψ C G (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip M)

/-- The normalized adjunction comparisons preserve beta, the clopen projector and alpha.
Source: Stacks 03D8, 03DI and 0F7B; blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: choose the constant-tower cartesian beta as the inverse open-unit transpose.
The inverse-image compositor comparison follows by taking the mates of the
sectionwise direct-image compositor. The open compositor comparison follows from
uniqueness of the unit-preserving left-adjoint comparison. Transposing the two sides
of beta compatibility, substituting these compositor and open-unit equations,
gives identical morphisms; the adjunction bijection proves their equality.
For a clopen map, the open unit is invertible and its inverse transpose is the
extension/direct-image comparison. Take its inverse and compose with the
direct-image unit to define pi. The already established unit and mate comparisons
prove pi compatibility. Define alpha by the specified beta, pi and compositor
word. Substitute beta and pi compatibility and the two compositor equations into
this word. Naturality moves each coefficient comparison through the factors, and
the neighboring inverse comparisons cancel. The resulting equation is alpha
compatibility. None of these arguments assumes that the proper/open square is
cartesian or that a coefficient map is flat. -/
theorem ordinaryScalarProperOpen (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    (C : OrdinaryScalarRestriction R φ B ψ) (G : OrdinaryScalarAdjunctions R φ B ψ C) :
    Nonempty (OrdinaryScalarProperOpen R φ B ψ C G) := by
  have _hψ := hψ
  exact ⟨{
    beta := scalarBeta B
    beta_unit := scalarBeta_unit B
    beta_comparison := scalarBeta_comparison R φ B ψ C G
    clopen := scalarClopen B
    clopen_unit := scalarClopen_unit B
    pi_comparison := scalarPi_comparison R φ B ψ C G
    alpha := scalarAlpha B
    alpha_eq := scalarAlpha_eq B
    alpha_comparison := scalarAlpha_comparison R φ B ψ C G }⟩

end AlgebraicGeometry.ProEtale.VaryingRing
