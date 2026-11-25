/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-! # The concrete directed category colimit and comparison

Given a directed system of categories `C i` (`i` in a directed preorder `I`) with coherent
transition functors, this file builds the explicit filtered 2-colimit category: its objects are
pairs `(i, x)` with `x : C i`, and its Hom sets are the filtered set colimits, over the common
upper stages `k ≥ i, j`, of the Hom sets `T_ik x ⟶ T_jk y`. Composition and identities are
defined on representatives and descend to the colimit. For a coherent cocone
`Φ i : C i ⥤ D` with vertex `D` the file also defines the comparison functor `Object c ⥤ D`,
which sends `(i, x)` to `Φ_i x` and a class `[k, g]` to `θ_jk ∘ Φ_k g ∘ θ_ik⁻¹`.
`FilteredTwoColimitCharacterization.lean` shows that the cocone is a filtered 2-colimit exactly
when this comparison is an equivalence.

(blueprint: proposition-dctf-x-qbar-2-colimit--1).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : Type u'} [Category.{v'} D]

/-- Normalized coherent cocone. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
structure CoherentCategoryCocone extends CategoryCocone C D where
  tau : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    T hij ⋙ T hjk ≅ T (hij.trans hjk)
  transition_identity : ∀ i : I, T (le_refl i) = 𝟭 (C i)
  cocone_identity : ∀ i : I, HEq (iso (le_refl i)) (Iso.refl (Φ i))
  tau_identity_left : ∀ {i j : I} (h : i ≤ j),
    HEq (tau (le_refl i) h) (Iso.refl (T h))
  tau_identity_right : ∀ {i j : I} (h : i ≤ j),
    HEq (tau h (le_refl j)) (Iso.refl (T h))
  tau_cocycle : ∀ {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (x : C i),
    (T hkl).map ((tau hij hjk).hom.app x) ≫
        (tau (hij.trans hjk) hkl).hom.app x =
      (tau hjk hkl).hom.app ((T hij).obj x) ≫
        (tau hij (hjk.trans hkl)).hom.app x
  compatibility : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i),
    (iso (hij.trans hjk)).hom.app x =
      (Φ k).map ((tau hij hjk).inv.app x) ≫
        (iso hjk).hom.app ((T hij).obj x) ≫ (iso hij).hom.app x

namespace FilteredTwoColimit

variable (c : CoherentCategoryCocone (C := C) (D := D))

/-- Pair objects. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def Object (_c : CoherentCategoryCocone (C := C) (D := D)) : Type (max w u) :=
  Σ i : I, C i

/-- Common upper stages with the inherited preorder.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def CommonStage (i j : I) := {k : I // i ≤ k ∧ j ≤ k}

/-- The inherited order. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
instance commonStagePreorder (i j : I) : Preorder (CommonStage i j) :=
  inferInstanceAs (Preorder {k : I // i ≤ k ∧ j ≤ k})

/-- Hom at a common stage. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def HomAt (a b : Object c) (k : CommonStage a.1 b.1) : Type v :=
  (c.T k.2.1).obj a.2 ⟶ (c.T k.2.2).obj b.2

/-- Transition by conjugating the transition functor by tau.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def homTransition {a b : Object c} {k l : CommonStage a.1 b.1}
    (h : k ≤ l) (g : HomAt c a b k) : HomAt c a b l :=
  (c.tau k.2.1 h).inv.app a.2 ≫ (c.T h).map g ≫ (c.tau k.2.2 h).hom.app b.2

private theorem normalized_transport {A B E : Type*} [Category A] [Category B]
    [Category E] (F : E ⥤ E) (hF : F = 𝟭 E) (P : A ⥤ E) (Q : B ⥤ E)
    (eP : P ⋙ F ≅ P) (eQ : Q ⋙ F ≅ Q)
    (hP : HEq eP (Iso.refl P)) (hQ : HEq eQ (Iso.refl Q))
    (x : A) (y : B) (g : P.obj x ⟶ Q.obj y) :
    eP.inv.app x ≫ F.map g ≫ eQ.hom.app y = g := by
  subst F
  have hP' := eq_of_heq hP
  have hQ' := eq_of_heq hQ
  rw [hP', hQ']
  simp

/-- Normalization of tau and T gives identity.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem homTransition_id (a b : Object c) (k : CommonStage a.1 b.1)
    (g : HomAt c a b k) : homTransition c (le_refl k) g = g := by
  exact normalized_transport (c.T (le_refl k.1)) (c.transition_identity k.1)
    (c.T k.2.1) (c.T k.2.2) (c.tau k.2.1 (le_refl k.1))
    (c.tau k.2.2 (le_refl k.1)) (c.tau_identity_right k.2.1)
    (c.tau_identity_right k.2.2) a.2 b.2 g

/-- Transitions compose: `t_lm ∘ t_kl = t_km` on Hom sets at common stages.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem homTransition_comp (a b : Object c) {k l m : CommonStage a.1 b.1}
    (h : k ≤ l) (h' : l ≤ m) (g : HomAt c a b k) :
    homTransition c h' (homTransition c h g) = homTransition c (h.trans h') g := by
  have ha :
      (c.tau l.2.1 h').inv.app a.2 ≫ (c.T h').map ((c.tau k.2.1 h).inv.app a.2) =
        (c.tau k.2.1 (h.trans h')).inv.app a.2 ≫
          (c.tau h h').inv.app ((c.T k.2.1).obj a.2) := by
    exact congrArg Iso.inv (show
      (c.T h').mapIso ((c.tau k.2.1 h).app a.2) ≪≫ (c.tau l.2.1 h').app a.2 =
        (c.tau h h').app ((c.T k.2.1).obj a.2) ≪≫
          (c.tau k.2.1 (h.trans h')).app a.2 from
      Iso.ext (c.tau_cocycle k.2.1 h h' a.2))
  have hb := c.tau_cocycle k.2.2 h h' b.2
  dsimp [homTransition]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [hb]
  have hn := (c.tau h h').hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((c.T h').map ((c.T h).map g)), hn]
  simp

/-- The Hom diagram. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def homDiagram (a b : Object c) : CommonStage a.1 b.1 ⥤ Type v where
  obj k := HomAt c a b k
  map h := TypeCat.ofHom (homTransition c (leOfHom h))
  map_id k := ConcreteCategory.hom_ext _ _ (homTransition_id c a b k)
  map_comp h h' := ConcreteCategory.hom_ext _ _
    (fun g => (homTransition_comp c a b (leOfHom h) (leOfHom h') g).symm)

/-- The actual set colimit, with no smallness restriction on the index.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def HomSet (a b : Object c) : Type (max w v) := (homDiagram c a b).ColimitType

/-- A representative consists of a common stage and an arrow there.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def HomRepresentative (a b : Object c) := Σ k, HomAt c a b k

/-- The class of a representative. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def homClass {a b : Object c} (k : CommonStage a.1 b.1) (g : HomAt c a b k) :
    HomSet c a b := (homDiagram c a b).ιColimitType k g

/-- The canonical colimit classes identify an arrow
with its transition image, by the generating relation of the colimit quotient.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem homClass_transition {a b : Object c} {k l : CommonStage a.1 b.1}
    (h : k ≤ l) (g : HomAt c a b k) :
    homClass c l (homTransition c h g) = homClass c k g := by
  exact (homDiagram c a b).ιColimitType_map (homOfLE h) g

/-- The normalized identity class. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def identityHom (a : Object c) : HomSet c a a :=
  homClass c ⟨a.1, le_refl a.1, le_refl a.1⟩ (𝟙 _)

/-- The common upper stages of two indices form a filtered preorder.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem commonStage_isFiltered [IsDirected I (· ≤ ·)] (i j : I) :
    IsFiltered (CommonStage i j) := by
  obtain ⟨k, hi, hj⟩ := exists_ge_ge i j
  have : Nonempty (CommonStage i j) := ⟨⟨k, hi, hj⟩⟩
  have : IsDirectedOrder (CommonStage i j) := ⟨fun a b ↦ by
    obtain ⟨m, ha, hb⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨m, a.2.1.trans ha, a.2.2.trans ha⟩, ha, hb⟩⟩
  infer_instance

/-- Two representatives define the same class exactly when they agree after transition to a
common later stage (Stacks 04AX).
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem homClass_eq_iff [IsDirected I (· ≤ ·)] {a b : Object c} (k l : CommonStage a.1 b.1)
    (f : HomAt c a b k) (g : HomAt c a b l) :
    homClass c k f = homClass c l g ↔
      ∃ (m : CommonStage a.1 b.1) (hk : k ≤ m) (hl : l ≤ m),
        homTransition c hk f = homTransition c hl g := by
  have := commonStage_isFiltered (I := I) a.1 b.1
  exact ((homDiagram c a b).ιColimitType_eq_iff_of_isFiltered f g).trans
    ⟨fun ⟨m, hk, hl, h⟩ ↦ ⟨m, leOfHom hk, leOfHom hl, h⟩,
      fun ⟨m, hk, hl, h⟩ ↦ ⟨m, homOfLE hk, homOfLE hl, h⟩⟩

variable [IsDirected I (· ≤ ·)]

/-- Composition at a specified common stage. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def compAt {a b d : Object c} (f : HomRepresentative c a b)
    (g : HomRepresentative c b d) (m : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) :
    HomSet c a d :=
  homClass c ⟨m, f.1.2.1.trans hf, g.1.2.2.trans hg⟩
    (homTransition c (a := a) (b := b)
        (l := ⟨m, f.1.2.1.trans hf, f.1.2.2.trans hf⟩) hf f.2 ≫
      homTransition c (a := b) (b := d)
        (l := ⟨m, g.1.2.1.trans hg, g.1.2.2.trans hg⟩) hg g.2)

/-- Choose an upper bound of two representative stages, then use the displayed composition.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
noncomputable def compRepresentative {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d) : HomSet c a d :=
  compAt c f g (Classical.choose (exists_ge_ge f.1.1 g.1.1))
    (Classical.choose_spec (exists_ge_ge f.1.1 g.1.1)).1
    (Classical.choose_spec (exists_ge_ge f.1.1 g.1.1)).2

omit [IsDirected I (· ≤ ·)] in
private theorem homTransition_product {a b d : Object c} {k l : I}
    (ha : a.1 ≤ k) (hb : b.1 ≤ k) (hd : d.1 ≤ k) (h : k ≤ l)
    (f : (c.T ha).obj a.2 ⟶ (c.T hb).obj b.2)
    (g : (c.T hb).obj b.2 ⟶ (c.T hd).obj d.2) :
    homTransition c (k := ⟨k, ha, hd⟩) (l := ⟨l, ha.trans h, hd.trans h⟩) h (f ≫ g) =
      homTransition c (a := a) (b := b) (k := ⟨k, ha, hb⟩)
          (l := ⟨l, ha.trans h, hb.trans h⟩) h f ≫
        homTransition c (a := b) (b := d) (k := ⟨k, hb, hd⟩)
          (l := ⟨l, hb.trans h, hd.trans h⟩) h g := by
  simp [homTransition, Functor.map_comp, Category.assoc]

omit [IsDirected I (· ≤ ·)] in
private theorem compAt_transition {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d)
    (m n : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) (h : m ≤ n) :
    compAt c f g m hf hg = compAt c f g n (hf.trans h) (hg.trans h) := by
  unfold compAt
  rw [← homClass_transition c
    (k := ⟨m, f.1.2.1.trans hf, g.1.2.2.trans hg⟩)
    (l := ⟨n, f.1.2.1.trans (hf.trans h), g.1.2.2.trans (hg.trans h)⟩) h]
  congr 1
  rw [homTransition_product c _ (f.1.2.2.trans hf), homTransition_comp,
    homTransition_comp]

/-- The composite class does not depend on the common stage at which it is computed.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem compRepresentative_eq_compAt {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d)
    (m : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) :
    compRepresentative c f g = compAt c f g m hf hg := by
  let n := Classical.choose (exists_ge_ge f.1.1 g.1.1)
  have hn := Classical.choose_spec (exists_ge_ge f.1.1 g.1.1)
  change compAt c f g n hn.1 hn.2 = _
  obtain ⟨p, hnp, hmp⟩ := exists_ge_ge n m
  exact (compAt_transition c f g n p hn.1 hn.2 hnp).trans
    (compAt_transition c f g m p hf hg hmp).symm

/-- A generating relation in the
second input transports it to a later stage. Move both products to one upper stage and use the
transition law and preservation of products to identify them.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem compRepresentative_rel_right {a b d : Object c}
    (f : HomRepresentative c a b) (g g' : HomRepresentative c b d)
    (h : (homDiagram c b d).ColimitTypeRel g g') :
    compRepresentative c f g = compRepresentative c f g' := by
  rcases f with ⟨k, f⟩
  rcases g with ⟨l, g⟩
  rcases g' with ⟨l', g'⟩
  obtain ⟨h, e⟩ := h
  dsimp only at h e
  rw [e]
  obtain ⟨m, hk, hl'⟩ := exists_ge_ge k.1 l'.1
  rw [compRepresentative_eq_compAt c _ _ m hk ((show l.1 ≤ l'.1 from leOfHom h).trans hl'),
    compRepresentative_eq_compAt c _ _ m hk hl']
  unfold compAt
  congr 1
  dsimp [homDiagram]
  rw [homTransition_comp]

/-- For a generating relation in
first input, transport both products to a common upper stage and apply the transition law and
preservation of products. This gives equality of the two classes.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem compRepresentative_rel_left {a b d : Object c}
    (f f' : HomRepresentative c a b) (g : HomRepresentative c b d)
    (h : (homDiagram c a b).ColimitTypeRel f f') :
    compRepresentative c f g = compRepresentative c f' g := by
  rcases f with ⟨k, f⟩
  rcases f' with ⟨k', f'⟩
  rcases g with ⟨l, g⟩
  obtain ⟨h, e⟩ := h
  dsimp only at h e
  rw [e]
  obtain ⟨m, hk', hl⟩ := exists_ge_ge k'.1 l.1
  rw [compRepresentative_eq_compAt c _ _ m ((show k.1 ≤ k'.1 from leOfHom h).trans hk') hl,
    compRepresentative_eq_compAt c _ _ m hk' hl]
  unfold compAt
  congr 1
  dsimp [homDiagram]
  rw [homTransition_comp]

/-- Composition descended to the two set colimits.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
noncomputable def compHom {a b d : Object c}
    (f : HomSet c a b) (g : HomSet c b d) : HomSet c a d :=
  Quot.liftOn₂ f g (compRepresentative c)
    (fun f g g' h => compRepresentative_rel_right c f g g' h)
    (fun f f' g h => compRepresentative_rel_left c f f' g h)

/-- The identity class is a left identity for composition.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem id_compHom {a b : Object c} (f : HomSet c a b) :
    compHom c (identityHom c a) f = f := by
  induction f using Quot.inductionOn with
  | h f =>
    rcases f with ⟨k, f⟩
    change compRepresentative c ⟨⟨a.1, le_refl _, le_refl _⟩, 𝟙 _⟩ ⟨k, f⟩ =
      homClass c k f
    rw [compRepresentative_eq_compAt c _ _ k.1 k.2.1 (le_refl _)]
    dsimp only [compAt]
    rw [homTransition_id]
    simp [homTransition]
    rfl

/-- The identity class is a right identity for composition.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem compHom_id {a b : Object c} (f : HomSet c a b) :
    compHom c f (identityHom c b) = f := by
  induction f using Quot.inductionOn with
  | h f =>
    rcases f with ⟨k, f⟩
    change compRepresentative c ⟨k, f⟩ ⟨⟨b.1, le_refl _, le_refl _⟩, 𝟙 _⟩ =
      homClass c k f
    rw [compRepresentative_eq_compAt c _ _ k.1 (le_refl _) k.2.2]
    dsimp only [compAt]
    rw [homTransition_id]
    simp [homTransition]
    rfl

private theorem compHom_same {a b d : Object c} (m : I)
    (ha : a.1 ≤ m) (hb : b.1 ≤ m) (hd : d.1 ≤ m)
    (f : (c.T ha).obj a.2 ⟶ (c.T hb).obj b.2)
    (g : (c.T hb).obj b.2 ⟶ (c.T hd).obj d.2) :
    compHom c (homClass c ⟨m, ha, hb⟩ f) (homClass c ⟨m, hb, hd⟩ g) =
      homClass c ⟨m, ha, hd⟩ (f ≫ g) := by
  change compRepresentative c ⟨⟨m, ha, hb⟩, f⟩ ⟨⟨m, hb, hd⟩, g⟩ = _
  rw [compRepresentative_eq_compAt c _ _ m (le_refl _) (le_refl _)]
  simp only [compAt, homTransition_id]

/-- Choose one stage above three representatives;
independence of stages identifies both bracketings with the products there. Apply associativity
in that stage category.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem comp_assoc {a b d e : Object c} (f : HomSet c a b)
    (g : HomSet c b d) (h : HomSet c d e) :
    compHom c (compHom c f g) h = compHom c f (compHom c g h) := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      induction h using Quot.inductionOn with
      | h h =>
        rcases f with ⟨k, f⟩
        rcases g with ⟨l, g⟩
        rcases h with ⟨n, h⟩
        obtain ⟨p, hkp, hlp⟩ := exists_ge_ge k.1 l.1
        obtain ⟨m, hpm, hnm⟩ := exists_ge_ge p n.1
        have hkm := hkp.trans hpm
        have hlm := hlp.trans hpm
        change compHom c (compHom c (homClass c k f) (homClass c l g))
          (homClass c n h) = compHom c (homClass c k f)
            (compHom c (homClass c l g) (homClass c n h))
        rw [← homClass_transition c
          (l := ⟨m, k.2.1.trans hkm, k.2.2.trans hkm⟩) hkm f,
          ← homClass_transition c (l := ⟨m, l.2.1.trans hlm, l.2.2.trans hlm⟩) hlm g,
          ← homClass_transition c (l := ⟨m, n.2.1.trans hnm, n.2.2.trans hnm⟩) hnm h]
        simp only [compHom_same, Category.assoc]

/-- The category with pair objects and filtered-colimit Hom sets.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
noncomputable instance category : Category (Object c) where
  Hom := HomSet c
  id := identityHom c
  comp := compHom c
  id_comp := id_compHom c
  comp_id := compHom_id c
  assoc := comp_assoc c

/-- The comparison formula on representatives.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def mapHomRepresentative {a b : Object c} (f : HomRepresentative c a b) :
    (c.Φ a.1).obj a.2 ⟶ (c.Φ b.1).obj b.2 :=
  (c.iso f.1.2.1).inv.app a.2 ≫ (c.Φ f.1.1).map f.2 ≫ (c.iso f.1.2.2).hom.app b.2

omit [IsDirected I (· ≤ ·)] in
private theorem mapHomRepresentative_transition {a b : Object c}
    {k l : CommonStage a.1 b.1} (h : k ≤ l) (f : HomAt c a b k) :
    mapHomRepresentative c ⟨l, homTransition c h f⟩ =
      mapHomRepresentative c ⟨k, f⟩ := by
  have ha : (c.iso (k.2.1.trans h)).inv.app a.2 =
      (c.iso k.2.1).inv.app a.2 ≫ (c.iso h).inv.app ((c.T k.2.1).obj a.2) ≫
        (c.Φ l.1).map ((c.tau k.2.1 h).hom.app a.2) := by
    have he : (c.iso (k.2.1.trans h)).app a.2 =
        (c.Φ l.1).mapIso ((c.tau k.2.1 h).app a.2).symm ≪≫
          (c.iso h).app ((c.T k.2.1).obj a.2) ≪≫ (c.iso k.2.1).app a.2 :=
      Iso.ext (c.compatibility k.2.1 h a.2)
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
      Iso.app_hom, Category.assoc] using congrArg Iso.inv he
  dsimp only [mapHomRepresentative]
  rw [ha, c.compatibility k.2.2 h b.2]
  simp only [homTransition, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  have hn := (c.iso h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((c.Φ l.1).map ((c.T h).map f)), hn]
  simp

omit [IsDirected I (· ≤ ·)] in
/-- The comparison formula is constant on the classes of the Hom colimit.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem mapHomRepresentative_rel {a b : Object c}
    (f g : HomRepresentative c a b) (h : (homDiagram c a b).ColimitTypeRel f g) :
    mapHomRepresentative c f = mapHomRepresentative c g := by
  rcases f with ⟨k, f⟩
  rcases g with ⟨l, g⟩
  obtain ⟨h, e⟩ := h
  dsimp only at h e
  rw [e]
  exact (mapHomRepresentative_transition c (leOfHom h) f).symm

/-- Comparison on the set-colimit Hom. (blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
def mapHom {a b : Object c} (f : HomSet c a b) :
    (c.Φ a.1).obj a.2 ⟶ (c.Φ b.1).obj b.2 :=
  Quot.liftOn f (mapHomRepresentative c) (mapHomRepresentative_rel c)

omit [IsDirected I (· ≤ ·)] in
/-- The comparison sends the identity class to the identity morphism.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem mapHom_id (a : Object c) : mapHom c (identityHom c a) = 𝟙 _ := by
  change mapHomRepresentative c ⟨⟨a.1, le_refl _, le_refl _⟩, 𝟙 _⟩ = _
  simp [mapHomRepresentative]

/-- Represent the two arrows at one
stage, cancel the middle theta and its inverse, and use that Phi at that stage preserves products.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
theorem mapHom_comp {a b d : Object c} (f : HomSet c a b) (g : HomSet c b d) :
    mapHom c (compHom c f g) = mapHom c f ≫ mapHom c g := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      rcases f with ⟨k, f⟩
      rcases g with ⟨l, g⟩
      obtain ⟨m, hk, hl⟩ := exists_ge_ge k.1 l.1
      change mapHom c (compHom c (homClass c k f) (homClass c l g)) =
        mapHom c (homClass c k f) ≫ mapHom c (homClass c l g)
      rw [← homClass_transition c
        (l := ⟨m, k.2.1.trans hk, k.2.2.trans hk⟩) hk f,
        ← homClass_transition c (l := ⟨m, l.2.1.trans hl, l.2.2.trans hl⟩) hl g,
        compHom_same]
      change mapHomRepresentative c ⟨_, _ ≫ _⟩ =
        mapHomRepresentative c ⟨_, _⟩ ≫ mapHomRepresentative c ⟨_, _⟩
      simp [mapHomRepresentative, Functor.map_comp, Category.assoc]

/-- The canonical comparison with the cocone vertex.
(blueprint: proposition-dctf-x-qbar-2-colimit--1). -/
noncomputable def comparison : Object c ⥤ D where
  obj a := (c.Φ a.1).obj a.2
  map := mapHom c
  map_id := mapHom_id c
  map_comp := mapHom_comp c

end FilteredTwoColimit
end CategoryTheory
