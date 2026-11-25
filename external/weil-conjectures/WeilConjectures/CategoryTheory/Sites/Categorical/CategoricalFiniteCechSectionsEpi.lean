/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Refinements
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCoverLocalEpi

/-! # Lifting categorical sections from finite Čech exactness

Source: Stacks Project, Tag 03F8, with finite products and exact
filtered colimits in the coefficient category replacing elementwise lifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

private theorem categorical_zero_cocycle_compatibility
    (P : Cᵒᵖ ⥤ A) (X : C)
    {ι : Type} (U : ι → Over X)
    {E : A}
    (z : E ⟶ ∏ᶜ (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)))
    (hz : z ≫ ((cechComplexFunctor U).obj
      ((Over.forget X).op ⋙ P)).d 0 1 = 0)
    {W : C} {i j : ι} (a : W ⟶ (U i).left) (b : W ⟶ (U j).left)
    (hab : a ≫ (U i).hom = b ≫ (U j).hom) :
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) (fun _ ↦ i) ≫
        P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).left.op ≫ P.map a.op =
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) (fun _ ↦ j) ≫
        P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U j))).left.op ≫ P.map b.op := by
  let T := (FormalCoproduct.mk _ U).cech
  let Q := (FormalCoproduct.cosimplicialObjectFunctor T).obj ((Over.forget X).op ⋙ P)
  rw [cechComplexFunctor_obj_d] at hz
  change z ≫ (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • Q.δ k) = 0 at hz
  simp only [Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero] at hz
  let t : Fin 2 → ι := Fin.cases i (fun _ ↦ j)
  have h := congrArg (fun f ↦ f ≫ Pi.π (fun s : Fin 2 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) t) hz
  dsimp [Q, T, FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    CosimplicialObject.δ,
    FormalCoproduct.cech, FormalCoproduct.mapPower,
    FormalCoproduct.power, SimplexCategory.δ] at h
  erw [Category.assoc, Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π] at h
  change z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ U (s k))).left))
      (t ∘ ⇑(Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom) ≫
      P.map (Pi.lift (fun k : Fin 1 ↦ Pi.π
        (fun k : Fin 2 ↦ U (t k))
        ((Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom k))).left.op =
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ U (s k))).left))
      (t ∘ ⇑(Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom) ≫
      P.map (Pi.lift (fun k : Fin 1 ↦ Pi.π
        (fun k : Fin 2 ↦ U (t k))
        ((Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom k))).left.op at h
  have h0 : (⇑(Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (1 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  have h1 : (⇑(Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (0 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  rw [h0, h1] at h
  dsimp [Function.comp_def, t] at h
  let B := Over.mk (a ≫ (U i).hom)
  let aa : B ⟶ U i := Over.homMk a rfl
  let bb : B ⟶ U j := Over.homMk b hab.symm
  let l : B ⟶ ∏ᶜ (fun k : Fin 2 ↦ U (t k)) :=
    Pi.lift (Fin.cases aa (fun _ ↦ bb))
  let di : (∏ᶜ (fun k : Fin 2 ↦ U (t k))) ⟶
      ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift (fun _ ↦ Pi.π _ 0)
  let dj : (∏ᶜ (fun k : Fin 2 ↦ U (t k))) ⟶
      ∏ᶜ (fun _ : Fin 1 ↦ U j) := Pi.lift (fun _ ↦ Pi.π _ 1)
  let qi : U i ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) :=
    Pi.lift (fun _ ↦ 𝟙 _)
  let qj : U j ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U j) :=
    Pi.lift (fun _ ↦ 𝟙 _)
  have hi : l ≫ di = aa ≫ qi := by
    apply Pi.hom_ext
    intro k
    simp [l, di, qi]
  have hj : l ≫ dj = bb ≫ qj := by
    apply Pi.hom_ext
    intro k
    simp [l, dj, qj]
    rfl
  change z ≫ Pi.π (fun s : Fin 1 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) (fun _ ↦ j) ≫
      P.map dj.left.op = z ≫ Pi.π (fun s : Fin 1 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) (fun _ ↦ i) ≫
      P.map di.left.op at h
  have hi' : l.left ≫ di.left = a ≫ qi.left := congrArg Over.Hom.left hi
  have hj' : l.left ≫ dj.left = b ≫ qj.left := congrArg Over.Hom.left hj
  have hh := congrArg (fun f ↦ f ≫ P.map l.left.op) h
  simp only [Category.assoc] at hh
  rw [← P.map_comp, ← op_comp, hj'] at hh
  conv at hh => rhs; rw [← P.map_comp, ← op_comp, hi']
  simpa only [op_comp, P.map_comp, Category.assoc, qi, qj] using hh.symm

omit [HasSheafify J A] in
private theorem lift_categoricalCech_zero (P : Sheaf J A)
    {V : C} {n : ℕ} (U : Fin n → Over V)
    (hU : Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    {E : A} (z : E ⟶ ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P.obj)).X 0)
    (hz : z ≫ ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P.obj)).d 0 1 = 0) :
    ∃ t : E ⟶ P.obj.obj (op V),
      t ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P.obj) = z := by
  let x := fun i ↦ z ≫ Pi.π (fun s : Fin 1 → Fin n ↦
    P.obj.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) (fun _ ↦ i) ≫
      P.obj.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).left.op
  have hx : ∀ ⦃W : C⦄ ⦃i j : Fin n⦄ (a : W ⟶ (U i).left) (b : W ⟶ (U j).left),
      a ≫ (U i).hom = b ≫ (U j).hom →
        x i ≫ P.obj.map a.op = x j ≫ P.obj.map b.op := by
    intro W i j a b hab
    simpa only [x, Category.assoc] using
      categorical_zero_cocycle_compatibility P.obj V U z hz a b hab
  let t := P.property.amalgamateOfArrows (fun i ↦ (U i).hom) hU x hx
  refine ⟨t, ?_⟩
  apply Pi.hom_ext
  intro y
  change Fin 1 → Fin n at y
  change (t ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P.obj)) ≫
    Pi.π (fun s : Fin 1 → Fin n ↦ P.obj.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) y =
      z ≫ Pi.π (fun s : Fin 1 → Fin n ↦ P.obj.obj (op (∏ᶜ (fun k ↦ U (s k))).left)) y
  have hy : y = fun _ ↦ y 0 := by
    funext k
    congr 1
    exact Subsingleton.elim _ _
  rw [hy]
  generalize y 0 = i
  let q : U i ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift (fun _ ↦ 𝟙 _)
  let r : (∏ᶜ (fun _ : Fin 1 ↦ U i)) ⟶ U i := Pi.π _ 0
  have hrq : r ≫ q = 𝟙 _ := by
    apply Pi.hom_ext
    intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp [q, r]
  have hw : (∏ᶜ (fun _ : Fin 1 ↦ U i)).hom = r.left ≫ (U i).hom := r.w.symm
  rw [Category.assoc]
  erw [cechAugmentation_π]
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op,
    Over.mkIdTerminal_from_left]
  change t ≫ P.obj.map (∏ᶜ (fun _ : Fin 1 ↦ U i)).hom.op = _
  rw [hw, op_comp, P.obj.map_comp, ← Category.assoc]
  rw [P.property.amalgamateOfArrows_map (fun i ↦ (U i).hom) hU x hx]
  dsimp [x]
  rw [Category.assoc, Category.assoc, ← P.obj.map_comp, ← op_comp]
  have hleft : r.left ≫ q.left = 𝟙 _ := congrArg Over.Hom.left hrq
  rw [hleft, op_id, P.obj.map_id, Category.comp_id]

omit [HasSheafify J A] in
private theorem mono_categoricalCech_augmentation (P : Sheaf J A)
    {V : C} {n : ℕ} (U : Fin n → Over V)
    (hU : Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V) :
    Mono (cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P.obj)) := by
  constructor
  intro E x y hxy
  apply P.property.hom_ext_ofArrows (fun i ↦ (U i).hom) hU
  intro i
  let q : U i ⟶ Presheaf.cechNerveObj U (fun _ : Fin 1 ↦ i) := Pi.lift fun _ ↦ 𝟙 _
  have hi := congrArg (fun f ↦ f ≫ Pi.π (fun s : Fin 1 → Fin n ↦
    P.obj.obj (op (Presheaf.cechNerveObj U s).left)) (fun _ ↦ i) ≫ P.obj.map q.left.op) hxy
  simp only [Category.assoc] at hi
  erw [cechAugmentation_π_assoc] at hi
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op,
    Over.mkIdTerminal_from_left] at hi
  change x ≫ P.obj.map (Presheaf.cechNerveObj U (fun _ : Fin 1 ↦ i)).hom.op ≫
    P.obj.map q.left.op = y ≫
      P.obj.map (Presheaf.cechNerveObj U (fun _ : Fin 1 ↦ i)).hom.op ≫
        P.obj.map q.left.op at hi
  simpa only [← P.obj.map_comp, ← op_comp, q.w] using hi

private theorem glue_categoricalCech_lift
    {S : ShortComplex (Sheaf J A)} (hS : S.ShortExact)
    {V : C} {n : ℕ} (U : Fin n → Over V)
    (hU : Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    (hF : ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ S.X₁.obj)).ExactAt 1)
    {E : A}
    (a : E ⟶ ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ S.X₂.obj)).X 0)
    (y : E ⟶ S.X₃.obj.obj (op V))
    (ha : a ≫ Limits.Pi.map (fun s : Fin 1 → Fin n ↦
      S.g.hom.app (op (Presheaf.cechNerveObj U s).left)) =
        y ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ S.X₃.obj)) :
    ∃ (E' : A) (π : E' ⟶ E) (_ : Epi π) (t : E' ⟶ S.X₂.obj.obj (op V)),
      π ≫ y = t ≫ S.g.hom.app (op V) := by
  let W := (Over.forget V).op
  let KF := (cechComplexFunctor U).obj (W ⋙ S.X₁.obj)
  let KI := (cechComplexFunctor U).obj (W ⋙ S.X₂.obj)
  let KQ := (cechComplexFunctor U).obj (W ⋙ S.X₃.obj)
  let φ : KF ⟶ KI := (cechComplexFunctor U).map (Functor.whiskerLeft W S.f.hom)
  let ψ : KI ⟶ KQ := (cechComplexFunctor U).map (Functor.whiskerLeft W S.g.hom)
  have hleft (k : ℕ) (s : Fin (k + 1) → Fin n) :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj
        (op (Presheaf.cechNerveObj U s).left))).1 inferInstance S hS
  have hmono (k : ℕ) (s : Fin (k + 1) → Fin n) :
      Mono (S.f.hom.app (op (Presheaf.cechNerveObj U s).left)) := (hleft k s).2
  have hmonoMap (k : ℕ) (s : Fin (k + 1) → Fin n) :
      Mono (S.map (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj
        (op (Presheaf.cechNerveObj U s).left))).f := (hleft k s).2
  have hm (k : ℕ) : Mono (φ.f k) := by
    change Mono (Limits.Pi.map (fun s : Fin (k + 1) → Fin n ↦
      S.f.hom.app (op (Presheaf.cechNerveObj U s).left)))
    infer_instance
  have hfg (k : ℕ) : φ.f k ≫ ψ.f k = 0 := by
    apply Pi.hom_ext
    intro s
    change Fin (k + 1) → Fin n at s
    rw [zero_comp]
    change (Limits.Pi.map (fun s : Fin (k + 1) → Fin n ↦
      S.f.hom.app (op (Presheaf.cechNerveObj U s).left)) ≫
        Limits.Pi.map (fun s : Fin (k + 1) → Fin n ↦
          S.g.hom.app (op (Presheaf.cechNerveObj U s).left))) ≫ Pi.π _ s = 0
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc]
    have hw : S.f.hom.app (op (Presheaf.cechNerveObj U s).left) ≫
        S.g.hom.app (op (Presheaf.cechNerveObj U s).left) = 0 :=
      congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom.app
        (op (Presheaf.cechNerveObj U s).left)) S.zero
    rw [hw, comp_zero]
  have hac : (a ≫ KI.d 0 1) ≫ ψ.f 1 = 0 := by
    rw [Category.assoc, ← ψ.comm 0 1, ← Category.assoc]
    change (a ≫ Limits.Pi.map (fun s : Fin 1 → Fin n ↦
      S.g.hom.app (op (Presheaf.cechNerveObj U s).left))) ≫ KQ.d 0 1 = 0
    rw [ha, Category.assoc, cechAugmentation_d, comp_zero]
  have hb (s : Fin 2 → Fin n) :
      (a ≫ KI.d 0 1 ≫ Pi.π _ s) ≫
        S.g.hom.app (op (Presheaf.cechNerveObj U s).left) = 0 := by
    have h := congrArg (fun f ↦ f ≫ Pi.π
      (fun s : Fin 2 → Fin n ↦ S.X₃.obj.obj (op (Presheaf.cechNerveObj U s).left)) s) hac
    change ((a ≫ KI.d 0 1) ≫ Limits.Pi.map (fun s : Fin 2 → Fin n ↦
      S.g.hom.app (op (Presheaf.cechNerveObj U s).left))) ≫ Pi.π _ s = _ at h
    simpa only [Category.assoc, Limits.Pi.map_π, zero_comp] using h
  let c : E ⟶ KF.X 1 := Pi.lift fun s : Fin 2 → Fin n ↦
    (hleft 1 s).1.lift (a ≫ KI.d 0 1 ≫ Pi.π _ s) (hb s)
  have hc : c ≫ φ.f 1 = a ≫ KI.d 0 1 := by
    apply Pi.hom_ext
    intro s
    change Fin 2 → Fin n at s
    change (c ≫ Limits.Pi.map (fun s : Fin 2 → Fin n ↦
      S.f.hom.app (op (Presheaf.cechNerveObj U s).left))) ≫ Pi.π _ s = _
    rw [Category.assoc]
    erw [Limits.Pi.map_π, Pi.lift_comp_π_assoc]
    have hl := (hleft 1 s).1.lift_f (a ≫ KI.d 0 1 ≫ Pi.π _ s) (hb s)
    change (hleft 1 s).1.lift (a ≫ KI.d 0 1 ≫ Pi.π _ s) (hb s) ≫
      S.f.hom.app (op (Presheaf.cechNerveObj U s).left) = _ at hl
    simpa only [Category.assoc] using hl
  have hcc : c ≫ KF.d 1 2 = 0 := by
    apply (cancel_mono (φ.f 2)).1
    rw [zero_comp, Category.assoc, ← φ.comm 1 2, ← Category.assoc, hc,
      Category.assoc, KI.d_comp_d, comp_zero]
  have hex : (KF.sc' 0 1 2).Exact :=
    (HomologicalComplex.exactAt_iff' KF 0 1 2 (by simp) (by simp)).1 hF
  obtain ⟨E', π, hπ, b, hb⟩ := hex.exact_up_to_refinements c hcc
  change π ≫ c = b ≫ KF.d 0 1 at hb
  let a' := π ≫ a - b ≫ φ.f 0
  have ha' : a' ≫ KI.d 0 1 = 0 := by
    dsimp only [a']
    rw [Preadditive.sub_comp]
    calc
      (π ≫ a) ≫ KI.d 0 1 - (b ≫ φ.f 0) ≫ KI.d 0 1 =
          π ≫ (a ≫ KI.d 0 1) - (b ≫ KF.d 0 1) ≫ φ.f 1 := by
        simp only [Category.assoc, φ.comm 0 1]
      _ = π ≫ (c ≫ φ.f 1) - (π ≫ c) ≫ φ.f 1 := by rw [← hc, ← hb]
      _ = 0 := by rw [Category.assoc, sub_self]
  obtain ⟨t, ht⟩ := lift_categoricalCech_zero J S.X₂ U hU a' ha'
  refine ⟨E', π, hπ, t, ?_⟩
  have : Mono (cechAugmentation U Over.mkIdTerminal (W ⋙ S.X₃.obj)) :=
    mono_categoricalCech_augmentation J S.X₃ U hU
  apply (cancel_mono (cechAugmentation U Over.mkIdTerminal (W ⋙ S.X₃.obj))).1
  simp only [Category.assoc]
  have hn := cechAugmentation_naturality U Over.mkIdTerminal
    (Functor.whiskerLeft W S.g.hom)
  change cechAugmentation U Over.mkIdTerminal (W ⋙ S.X₂.obj) ≫ ψ.f 0 =
    S.g.hom.app (op V) ≫ cechAugmentation U Over.mkIdTerminal (W ⋙ S.X₃.obj) at hn
  erw [← hn]
  conv_rhs => rw [← Category.assoc]
  erw [ht]
  change π ≫ y ≫ cechAugmentation U Over.mkIdTerminal (W ⋙ S.X₃.obj) = a' ≫ ψ.f 0
  dsimp only [a']
  rw [Preadditive.sub_comp]
  simp only [Category.assoc, hfg, comp_zero, sub_zero]
  change π ≫ y ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ S.X₃.obj) =
    π ≫ a ≫ Limits.Pi.map (fun s : Fin 1 → Fin n ↦
      S.g.hom.app (op (Presheaf.cechNerveObj U s).left))
  simpa only [Category.assoc] using congrArg (fun f ↦ π ≫ f) ha.symm

/-- Vanishing of first finite Čech cohomology makes a short exact sheaf sequence
right exact on the specified objects.
Source: Stacks Project, Tag 03F8.
(blueprint: stage3-categorical-finite-cech-sections-epi).

Proof: Apply the local test for sheaf epimorphisms to the coefficient cokernel
projection of I(V) → Q(V). For any generalized Q(V)-section with simultaneous
local I-lifts, their Čech differential maps to zero in Q. Evaluation is left
exact, so lift its components uniquely to F. Their differential is zero by
monicity of the map on F-cochains. Exactness at degree one gives a Čech primitive
after an epimorphism of coefficient objects. Subtract its image from the local
I-lifts. Their differential is now zero. Projecting onto pairs proves ordinary
compatibility, so the sheaf axiom glues them uniquely to an I(V)-section. Its
image is the original Q(V)-section after the coefficient epimorphism, by monicity
of Q's augmentation. The cokernel projection therefore vanishes on each locally
liftable generalized section, and the local test makes it zero. Its vanishing
is equivalent to epimorphy of I(V) → Q(V). The argument works for empty covers:
degree-zero gluing and uniqueness use the empty-family sheaf axiom. -/
theorem epi_app_of_finite_cech_exact_one
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {S : ShortComplex (Sheaf J A)} (hS : S.ShortExact)
    (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ S.X₁.obj)).ExactAt 1)
    (V : C) (hV : B V) : Epi (S.g.hom.app (op V)) := by
  apply Abelian.epi_of_cokernel_π_eq_zero
  have : Epi S.g := hS.epi_g
  apply hom_eq_zero_of_finite_cover_lifts J B hcov S.g V hV
  intro n U hUB hU E a y ha
  obtain ⟨E', π, hπ, t, ht⟩ :=
    glue_categoricalCech_lift J hS U hU (hF V hV U hUB hU) a y ha
  apply (cancel_epi π).1
  rw [comp_zero, ← Category.assoc, ht, Category.assoc, cokernel.condition, comp_zero]

end CategoryTheory.Sheaf
