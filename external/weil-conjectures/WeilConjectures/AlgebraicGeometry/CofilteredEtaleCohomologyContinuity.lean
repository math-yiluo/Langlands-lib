/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Ordinary etale continuity for cofiltered categories

Source: Stacks Project, Tags 09YQ and 0032.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem transport_proposition {T : Type*} (P : T → Prop) {s t : T}
    (h : s = t) (ht : P t) : P s := by
  cases h
  exact ht

private theorem cast_app_equation_iff
    {C D : Type*} [Category C] [Category D] {K L : C ⥤ D}
    (h : K = L) (X : C) {Y : D} (f : K.obj X ⟶ Y) (g : L.obj X ⟶ Y) :
    (f = (eqToIso h).hom.app X ≫ g) ↔
      (f = eqToHom (Functor.congr_obj h X) ≫ g) := by
  simp only [eqToIso.hom, eqToHom_app]

private theorem eq_comp_inv_of_comp_hom_eq
    {C : Type*} [Category C] {X Y Z T W : C}
    (e : T ≅ W) (f : X ⟶ T) (a : X ⟶ Y) (b : Y ⟶ Z) (d : Z ⟶ W)
    (h : f ≫ e.hom = a ≫ b ≫ d) : f = a ≫ b ≫ d ≫ e.inv := by
  apply (cancel_mono e.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Ordinary continuity extends from directed orders to small cofiltered categories.
Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ) and Tag 0032.

Proof: Choose a small nonempty directed partial order A and a final R : A to I.op
using IsFiltered.exists_directed. The left opposite of R is initial, so whiskering
c gives a limiting cone. Compactness, quasi-separatedness, and affine transitions
are inherited. Reindex F and its transition maps along R. The identity law follows
from R.map_id, the composition law from R.map_comp and reversal by unop; equality
proof arguments agree by proof irrelevance. Reindex G, H, L, and B, together with
their object isomorphisms. Finality preserves the colimit of L, and the supplied
arrow and leg equations give those required for directed continuity. Apply
nonempty_isColimit_etale_cohomology_of_isLimit and transport the resulting colimit
of B.whisker R back by Functor.Final.isColimitWhiskerEquiv. Cofilteredness ensures
nonemptiness; degree zero and zero sheaves are included without extra hypotheses.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-continuity). -/
theorem nonempty_isColimit_etale_cohomology_of_cofiltered_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : j ⟶ i),
      (upperStar AddCommGrpCat.{u + 1} (D.map f)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj i)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j), φ (g ≫ f) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
        (D.map (g ≫ f)) (D.map_comp g f)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj (op i) ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app i)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op = (eG i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
        (c.π.app i) (c.w f).symm).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app j)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (r : ℕ)
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅ AddCommGrpCat.of (Sheaf.H (F i) r))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (eH j).hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f) (F i) r) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) r))
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt r))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app i) (F i) r) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app (op i)) r)) :
    Nonempty (IsColimit B) := by
  set_option backward.isDefEq.respectTransparency true in
    obtain ⟨A, hA, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Iᵒᵖ
    let := hA
    let := hdir
    let := hne
    let := hR
    let D' : Aᵒᵖ ⥤ Scheme.{u} :=
      { obj := fun a ↦ D.obj (R.obj a.unop).unop
        map := fun f ↦ D.map (R.map f.unop).unop
        map_id := by
          intro a
          dsimp
          rw [R.map_id, unop_id, D.map_id]
        map_comp := by
          intro a b d f g
          dsimp
          rw [R.map_comp, unop_comp, D.map_comp] }
    let (a : Aᵒᵖ) : CompactSpace (D'.obj a) := inferInstanceAs
      (CompactSpace (D.obj (R.obj a.unop).unop))
    let (a : Aᵒᵖ) : QuasiSeparatedSpace (D'.obj a) := inferInstanceAs
      (QuasiSeparatedSpace (D.obj (R.obj a.unop).unop))
    let (a b : Aᵒᵖ) (f : a ⟶ b) : IsAffineHom (D'.map f) := inferInstanceAs
      (IsAffineHom (D.map (R.map f.unop).unop))
    let c' := c.whisker R.leftOp
    have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c).symm hc
    let F' := fun a : A ↦ F (R.obj a).unop
    let φ' := fun {a b : A} (f : a ⟶ b) ↦ φ (R.map f).unop
    have hid : ∀ a : A, φ' (𝟙 a) =
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D'.map_id (op a)))).hom.app
          (F' a) ≫ (upperStarId AddCommGrpCat.{u + 1} (D'.obj (op a))).hom.app (F' a) := by
      intro a
      apply (cast_app_equation_iff
        (congrArg (upperStar AddCommGrpCat.{u + 1}) (D'.map_id (op a))) (F' a)
        (φ' (𝟙 a))
        ((upperStarId AddCommGrpCat.{u + 1} (D'.obj (op a))).hom.app (F' a))).2
      let P := fun t : (R.obj a).unop ⟶ (R.obj a).unop ↦
        (upperStar AddCommGrpCat.{u + 1} (D.map t)).obj (F (R.obj a).unop)
      let T := (upperStar AddCommGrpCat.{u + 1} (𝟙 (D.obj (R.obj a).unop))).obj
        (F (R.obj a).unop)
      let k : T ⟶ F (R.obj a).unop :=
        (upperStarId AddCommGrpCat.{u + 1} (D.obj (R.obj a).unop)).hom.app
          (F (R.obj a).unop)
      have aux := transport_proposition
        (fun t : (R.obj a).unop ⟶ (R.obj a).unop ↦
          ∀ h : P t = T, φ t = eqToHom h ≫ k)
        (s := (R.map (𝟙 a)).unop) (t := 𝟙 (R.obj a).unop)
        (by rw [R.map_id]; rfl)
        (fun _ ↦ (cast_app_equation_iff
          (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (R.obj a).unop))
          (F (R.obj a).unop) (φ (𝟙 (R.obj a).unop)) k).1 (hidentity (R.obj a).unop))
      exact aux (Functor.congr_obj
        (congrArg (upperStar AddCommGrpCat.{u + 1}) (D'.map_id (op a))) (F' a))
    have hcomp : ∀ (a b d : A) (f : a ⟶ b) (g : b ⟶ d), φ' (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D'.map g.op) (D'.map f.op)
          (D'.map (f ≫ g).op) (D'.map_comp g.op f.op)).hom.app (F' a) ≫
        (upperStar AddCommGrpCat.{u + 1} (D'.map g.op)).map (φ' f) ≫ φ' g := by
      intro a b d f g
      have aux := transport_proposition
        (fun t : (R.obj d).unop ⟶ (R.obj a).unop ↦
          ∀ hD : D.map t = D.map (R.map g).unop ≫ D.map (R.map f).unop,
          φ t = (upperStarComp AddCommGrpCat.{u + 1} (D.map (R.map g).unop)
            (D.map (R.map f).unop) (D.map t) hD).hom.app (F (R.obj a).unop) ≫
            (upperStar AddCommGrpCat.{u + 1} (D.map (R.map g).unop)).map
              (φ (R.map f).unop) ≫ φ (R.map g).unop)
        (s := (R.map (f ≫ g)).unop) (t := (R.map g).unop ≫ (R.map f).unop)
        (by rw [R.map_comp]; rfl)
        (fun _ ↦ hcomposition (R.obj a).unop (R.obj b).unop (R.obj d).unop
          (R.map f).unop (R.map g).unop)
      exact aux (D'.map_comp g.op f.op)
    have hG' : ∀ (a b : A) (f : a ⟶ b), (R ⋙ G).map f =
        (eG (R.obj a).unop).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c'.π.app (op b)) (D'.map f.op)
          (c'.π.app (op a)) (c'.w f.op).symm).hom.app (F' a) ≫
        (upperStar AddCommGrpCat.{u + 1} (c'.π.app (op b))).map (φ' f) ≫
          (eG (R.obj b).unop).inv := by
      intro a b f
      exact hG (R.obj a).unop (R.obj b).unop (R.map f).unop
    have hH' : ∀ (a b : A) (f : a ⟶ b), (R ⋙ H).map f =
        (eH (R.obj a).unop).hom ≫
        AddCommGrpCat.ofHom (cohomologyMap (D'.map f.op) (F' a) r) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ' f) r) ≫ (eH (R.obj b).unop).inv := by
      intro a b f
      exact eq_comp_inv_of_comp_hom_eq (eH (R.obj b).unop) ((R ⋙ H).map f)
        (eH (R.obj a).unop).hom
        (AddCommGrpCat.ofHom (cohomologyMap (D'.map f.op) (F' a) r))
        (AddCommGrpCat.ofHom (Sheaf.H.map (φ' f) r))
        (hH (R.obj a).unop (R.obj b).unop (R.map f).unop)
    obtain ⟨hB'⟩ := nonempty_isColimit_etale_cohomology_of_isLimit D' c' hc'
      F' φ' hid hcomp (R ⋙ G) (fun a ↦ eG (R.obj a).unop) hG' (L.whisker R)
      ((Functor.Final.isColimitWhiskerEquiv R L).symm hL) r (R ⋙ H)
      (fun a ↦ eH (R.obj a).unop) hH' (B.whisker R) eB (fun a ↦ hB (R.obj a).unop)
    exact ⟨Functor.Final.isColimitWhiskerEquiv R B hB'⟩

end AlgebraicGeometry.Etale
