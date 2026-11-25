/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient

/-! # Completion comparison from a normalized restriction functor

Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-completion-from-restriction).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

private theorem restriction_transition {C D E : Type*}
    [Category C] [Category D] [Category E]
    (B : D ⥤ E) (K : E ⥤ D) (a : B ⊣ K)
    (P : D ⥤ C) (Q : E ⥤ C) (d : K ⋙ P ≅ Q)
    {F S₁ S₀ : C} {U L : D} {V N : E}
    (r₁ : U ≅ L) (r₀ : V ≅ N) (b : B.obj U ≅ V) (c : B.obj L ≅ N)
    (β₁ : S₁ ≅ P.obj U) (β₀ : S₀ ≅ Q.obj V) (δ : S₁ ⟶ S₀)
    (u₁ : F ⟶ P.obj L) (u₀ : F ⟶ Q.obj N)
    (hb : b.hom ≫ r₀.hom = B.map r₁.hom ≫ c.hom)
    (hδ : δ ≫ β₀.hom = β₁.hom ≫ P.map (a.homEquiv _ _ b.hom) ≫ d.hom.app V)
    (hu : u₁ ≫ P.map (a.unit.app L) ≫ d.hom.app (B.obj L) ≫ Q.map c.hom = u₀) :
    u₁ ≫ P.map r₁.inv ≫ β₁.inv ≫ δ ≫ β₀.hom ≫ Q.map r₀.hom = u₀ := by
  have hw : a.homEquiv _ _ b.hom ≫ K.map r₀.hom =
      r₁.hom ≫ a.unit.app L ≫ K.map c.hom := by
    rw [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp, hb,
      Functor.map_comp]
    exact (a.unit.naturality_assoc r₁.hom _).symm
  rw [reassoc_of% hδ, Iso.inv_hom_id_assoc, ← d.hom.naturality]
  change u₁ ≫ P.map r₁.inv ≫ P.map (a.homEquiv _ _ b.hom) ≫
    P.map (K.map r₀.hom) ≫ d.hom.app N = u₀
  rw [← P.map_comp_assoc (a.homEquiv _ _ b.hom) (K.map r₀.hom), hw,
    P.map_comp, P.map_comp]
  simp only [Category.assoc]
  rw [← P.map_comp_assoc r₁.inv r₁.hom]
  simp only [Iso.inv_hom_id, P.map_id, Category.id_comp]
  have hd := d.hom.naturality c.hom
  dsimp only [Functor.comp_map] at hd
  rw [hd]
  exact hu

private theorem quotient_comparison_naturality {C D : Type*}
    [Category C] [Category D] (L : C ⥤ D) (P : D ⥤ C) (a : L ⊣ P)
    {F G QF QG SF SG : C} {MF MG : D}
    (πF : F ⟶ QF) [Epi πF] (πG : G ⟶ QG)
    (eF : QF ≅ SF) (eG : QG ≅ SG) (βF : SF ≅ P.obj MF) (βG : SG ≅ P.obj MG)
    (rF : MF ≅ L.obj F) (rG : MG ≅ L.obj G)
    (x : F ⟶ G) (q : QF ⟶ QG) (m : SF ⟶ SG) (k : MF ⟶ MG)
    (hπ : πF ≫ q = x ≫ πG)
    (hF : πF ≫ eF.hom ≫ βF.hom ≫ P.map rF.hom = a.unit.app F)
    (hG : πG ≫ eG.hom ≫ βG.hom ≫ P.map rG.hom = a.unit.app G)
    (hβ : m ≫ βG.hom = βF.hom ≫ P.map k)
    (hr : k ≫ rG.hom = rF.hom ≫ L.map x) :
    q ≫ eG.hom = eF.hom ≫ m := by
  apply (cancel_epi πF).1
  apply (cancel_mono (βG.hom ≫ P.map rG.hom)).1
  simp only [Category.assoc]
  rw [reassoc_of% hβ, ← P.map_comp, hr, P.map_comp]
  rw [reassoc_of% hπ, hG]
  have hh := congrArg (· ≫ P.map (L.map x)) hF
  simp only [Category.assoc] at hh
  rw [hh]
  exact a.unit.naturality x

set_option backward.isDefEq.respectTransparency false in
/-- A restriction functor with unit-normalized pullback comparisons induces the
canonical comparison with completion.
Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-completion-from-restriction).

Proof:
For each coherent F and n, closedImmersion_unit_quotient applied to j_n identifies
F/J^(n+1)F with j_(n,*)j_n^*F. Identify the iterated ideal-module product defining
formalModuleQuotient with multiplication by J^(n+1), by induction on n using
associativity of multiplication (equivalently its affine tensor calculation).
Transport the quotient identification from the canonical tensor-pullback adjunction
to aj_n by the unit-normalized uniqueness isomorphism of left adjoints. Compose
with the inverse of j_(n,*)(r_n,F) and then the inverse of beta_n,R(F).
These are isomorphisms from the terms of completion(F) to the terms of Phi(R(F)).
The transition hypothesis for Phi, the comparison equation hr for R, and the unit
equation hc imply that adjacent transition squares commute after precomposition
with the quotient projection F -> F/J^(n+2)F. This map is epi, so the squares commute.
Every order map of natural numbers factors into adjacent maps, so the termwise
maps and their inverses define an isomorphism of inverse systems. Naturality in F
follows from naturality of quotient maps, adjunction units, beta and r, again
canceling the quotient projections. Lift this natural isomorphism through the full
subcategory of coherent formal modules. The definition of its terms gives the
asserted quotient-projection equation. No arbitrary existence witness is used to
define an object: R is supplied, and all quotient maps are uniquely determined.
-/
theorem completion_from_restriction {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)))
    (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (htransition : (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)))
    (c : ∀ n : ℕ,
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
              Scheme.Modules.tensorPullback (i n) ≅
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (R : CoherentModules X ⥤ CoherentThickeningSystem (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i)
          (r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ≅
            ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
              Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ (F : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app F ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app F) =
            (aj n).unit.app F)
    (hr : ∀ (F : CoherentModules X) (n : ℕ),
            ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
              (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
                (c n).hom.app F.obj) :
    ∃ (ρ : @completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f) ≅ R ⋙ Φ),
          (∀ (F : CoherentModules X) (n : ℕ),
            formalModuleQuotientπ ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                (CommRingCat.of A)).inv.hom)).comap f) (n + 1) F.obj ≫
              (ρ.hom.app F).hom.app (op n) ≫ (β n).hom.app (R.obj F) ≫
                (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                    (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((r n).hom.app F) =
            (aj n).unit.app F.obj) := by
  classical
  have _ := hi₂
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let P := fun n : ℕ ↦ Scheme.Modules.pushforward (j n)
  let L := fun n : ℕ ↦ Scheme.Modules.tensorPullback (j n)
  let S := R ⋙ Φ
  have hq (F : CoherentModules X) (n : ℕ) :
      ∃ e : formalModuleQuotient J (n + 1) F.obj ≅ (P n).obj ((L n).obj F.obj),
        formalModuleQuotientπ J (n + 1) F.obj ≫ e.hom = (aj n).unit.app F.obj := by
    have : IsClosedImmersion (j n) := (hgeom n).1
    exact closedImmersion_power_quotient J (n + 1) (j n) (hgeom n).2 (aj n) F.obj
  choose q hq using hq
  let e (F : CoherentModules X) (n : ℕ) :
      formalModuleQuotient J (n + 1) F.obj ≅ (S.obj F).obj.obj (op n) :=
    q F n ≪≫ (P n).mapIso ((r n).app F).symm ≪≫ ((β n).app (R.obj F)).symm
  have he (F : CoherentModules X) (n : ℕ) :
      formalModuleQuotientπ J (n + 1) F.obj ≫ (e F n).hom ≫
        (β n).hom.app (R.obj F) ≫ (P n).map ((r n).hom.app F) =
      (aj n).unit.app F.obj := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.app_inv]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp]
    simp only [Iso.inv_hom_id_app]
    exact hq F n
  have hs (F : CoherentModules X) (n : ℕ) :
      formalModuleQuotientπ J (n + 2) F.obj ≫ (e F (n + 1)).hom ≫
        (S.obj F).obj.map (homOfLE (Nat.le_succ n)).op =
      formalModuleQuotientπ J (n + 1) F.obj ≫ (e F n).hom := by
    let d := Scheme.Modules.pushforwardComp (i n) (j (n + 1)) ≪≫
      Scheme.Modules.pushforwardCongr (hi n)
    have htr := htransition (R.obj F) n
    dsimp only [Functor.comp_obj, CoherentThickeningSystem.evaluation] at htr
    have hcn := hc F.obj n
    have hcalc := restriction_transition
      (Scheme.Modules.tensorPullback (i n)) (Scheme.Modules.pushforward (i n)) (ai n)
      (P (n + 1)) (P n) d ((r (n + 1)).app F) ((r n).app F)
      ((R.obj F).comparison n) ((c n).app F.obj)
      ((β (n + 1)).app (R.obj F)) ((β n).app (R.obj F))
      ((S.obj F).obj.map (homOfLE (Nat.le_succ n)).op)
      ((aj (n + 1)).unit.app F.obj) ((aj n).unit.app F.obj) (hr F n)
      (by
        dsimp only [d, P, j, S, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
          Functor.comp_obj, ObjectProperty.ι_obj, CategoryTheory.evaluation,
          CoherentThickeningSystem.evaluation]
        simpa only [Category.assoc] using htr)
      (by
        dsimp only [d, P, j, S, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
          Functor.comp_obj, ObjectProperty.ι_obj, CategoryTheory.evaluation,
          CoherentThickeningSystem.evaluation]
        simpa only [Category.assoc] using hcn)
    apply (cancel_mono ((β n).hom.app (R.obj F) ≫
      (P n).map ((r n).hom.app F))).1
    calc
      _ = (aj (n + 1)).unit.app F.obj ≫
          (P (n + 1)).map ((r (n + 1)).inv.app F) ≫
          (β (n + 1)).inv.app (R.obj F) ≫
          (S.obj F).obj.map (homOfLE (Nat.le_succ n)).op ≫
          (β n).hom.app (R.obj F) ≫ (P n).map ((r n).hom.app F) := by
        dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv]
        simp only [← Category.assoc]
        rw [hq F (n + 1)]
      _ = (aj n).unit.app F.obj := hcalc
      _ = _ := (he F n).symm
  have hn (F G : CoherentModules X) (a : F ⟶ G) (n : ℕ) :
      formalModuleQuotientMap J a.hom (Nat.le_refl (n + 1)) ≫ (e G n).hom =
        (e F n).hom ≫ (S.map a).hom.app (op n) := by
    have hπ : formalModuleQuotientπ J (n + 1) F.obj ≫
        formalModuleQuotientMap J a.hom (Nat.le_refl (n + 1)) =
        a.hom ≫ formalModuleQuotientπ J (n + 1) G.obj := by
      simp [formalModuleQuotientπ, formalModuleQuotientMap]
    have : Epi (formalModuleQuotientπ J (n + 1) F.obj) :=
      inferInstanceAs (Epi (cokernel.π _))
    apply quotient_comparison_naturality (L n) (P n) (aj n)
      (formalModuleQuotientπ J (n + 1) F.obj) (formalModuleQuotientπ J (n + 1) G.obj)
      (e F n) (e G n) ((β n).app (R.obj F)) ((β n).app (R.obj G))
      ((r n).app F) ((r n).app G) a.hom
      (formalModuleQuotientMap J a.hom (Nat.le_refl (n + 1)))
      ((S.map a).hom.app (op n)) ((R.map a).app n) hπ (he F n) (he G n)
    · have hb := (β n).hom.naturality (R.map a)
      dsimp only [Functor.comp_map, CategoryTheory.evaluation,
        CoherentThickeningSystem.evaluation, ObjectProperty.ι_map] at hb
      exact hb
    · exact (r n).hom.naturality a
  have ht (F : CoherentModules X) (a b : ℕ) (h : b ≤ a) :
      (formalCompletionSystem J F.obj).map (homOfLE h).op ≫ (e F b).hom =
        (e F a).hom ≫ (S.obj F).obj.map (homOfLE h).op := by
    induction h with
    | refl => simp
    | @step a h ih =>
      have hh : (homOfLE (Nat.le_succ_of_le h)).op =
          (homOfLE (Nat.le_succ a)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [hh, Functor.map_comp, Functor.map_comp, Category.assoc, ih]
      rw [← Category.assoc]
      rw [← Category.assoc (e F a.succ).hom]
      apply congrArg (· ≫ (S.obj F).obj.map (homOfLE h).op)
      apply (cancel_epi (cokernel.π
        (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (a + 2)).2
          F.obj))).1
      simpa [formalCompletionSystem, formalModuleQuotientMap, formalModuleQuotientπ,
        Category.assoc] using (hs F a).symm
  let eF (F : CoherentModules X) : (formalCompletionSystem J F.obj) ≅ (S.obj F).obj :=
    NatIso.ofComponents (fun n ↦ e F n.unop) (by
      intro a b g
      have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
      simpa only [hg] using ht F a.unop b.unop (leOfHom g.unop))
  let ρ : completion X J ≅ S := NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (eF F)) (by
      intro F G a
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext n
      exact hn F G a n.unop)
  exact ⟨ρ, he⟩

end
end AlgebraicGeometry
