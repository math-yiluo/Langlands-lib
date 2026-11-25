/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Lifting a finite diagram with prescribed object models

Source: Stacks Project, Limits, Tag 01ZM (2), (3), and its closing colimit assertion.
(blueprint: lem-weil-pbc-finite-diagram-lift-of-models).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Generating arrows lift at one stage, with compatible objectwise comparisons.

Source: Stacks Project, Limits, Tag 01ZM (2), finite common-stage argument.

Proof: Conjugate each generating arrow by the given object isomorphisms. Apply
01ZM (2) to this morphism between the limit pullbacks of the two prescribed
finite-presentation models. There are finitely many generators, so directedness
provides a stage refining their stages and the original stage i. Pull every arrow
back to this common stage and identify iterated pullbacks by Over.pullbackComp.
Compose the canonical comparisons with alpha. Naturality of pullback composition
and the equations from 01ZM (2) give the displayed generator equations. If there
are no arrows, use i, the identity transition, and Over.pullbackId. -/
private theorem finite_generators_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Quiver.{v} A] [Finite (Σ a b : A, Quiver.Hom a b)]
    (F : Paths A ⥤ Over c.pt) (i : Iᵒᵖ) (V : A → Over (D.obj i))
    (hV : ∀ a, LocallyOfFinitePresentation (V a).hom ∧
      QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom)
    (α : ∀ a, (Over.pullback (c.π.app i)).obj (V a) ≅ F.obj a) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (e : ∀ {a b : A}, Quiver.Hom a b →
        ((Over.pullback (D.map h)).obj (V a) ⟶
          (Over.pullback (D.map h)).obj (V b)))
      (σ : ∀ a, (Over.pullback (c.π.app j)).obj
        ((Over.pullback (D.map h)).obj (V a)) ≅ F.obj a),
      ∀ {a b : A} (f : Quiver.Hom a b),
        (Over.pullback (c.π.app j)).map (e f) ≫ (σ b).hom =
          (σ a).hom ≫ F.map ((Paths.of A).map f) := by
  classical
  let B := Σ a b : A, Quiver.Hom a b
  let U : B → Over (D.obj i) := fun f ↦ V f.1
  let W : B → Over (D.obj i) := fun f ↦ V f.2.1
  let ψ (f : B) : (Over.pullback (c.π.app i)).obj (U f) ⟶
      (Over.pullback (c.π.app i)).obj (W f) :=
    (α f.1).hom ≫ F.map ((Paths.of A).map f.2.2) ≫ (α f.2.1).inv
  let θ (f : B) := (ψ f).left ≫ pullback.fst (W f).hom (c.π.app i)
  have hθ (f : B) : θ f ≫ (W f).hom =
      pullback.fst (U f).hom (c.π.app i) ≫ (U f).hom := by
    dsimp [θ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change ((ψ f).left ≫ ((Over.pullback (c.π.app i)).obj (W f)).hom) ≫
      c.π.app i = _
    rw [Over.w, pullback.condition]
    rfl
  have hex (f : B) : ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (θj : pullback (U f).hom (D.map h) ⟶ (W f).left),
      θj ≫ (W f).hom = pullback.fst (U f).hom (D.map h) ≫ (U f).hom ∧
      pullback.map (U f).hom (c.π.app i) (U f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj = θ f := by
    have := (hV f.1).1
    have := (hV f.1).2.1
    have := (hV f.1).2.2
    have := (hV f.2.1).1
    have := (hV f.2.1).2.1
    have := (hV f.2.1).2.2
    exact Scheme.exists_pullback_hom_of_isLimit hc (U f).hom (W f).hom (θ f) (hθ f)
  choose js fs θs hθs hdesc using hex
  obtain ⟨j, h, m, hm⟩ := IsCofiltered.wideCospan fs
  have hmap (f : B) : D.map h = D.map (m f) ≫ D.map (fs f) := by
    rw [← D.map_comp, hm]
  let M (f : B) := pullback.map (U f).hom (D.map h) (U f).hom (D.map (fs f))
    (𝟙 _) (D.map (m f)) (𝟙 _) (by simp) (by simp [hmap f])
  let θj (f : B) := M f ≫ θs f
  have hθj (f : B) : θj f ≫ (W f).hom =
      pullback.fst (U f).hom (D.map h) ≫ (U f).hom := by
    simp [θj, M, hθs f]
  have hj (f : B) : pullback.map (U f).hom (c.π.app i) (U f).hom (D.map h)
      (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj f = θ f := by
    have hM : pullback.map (U f).hom (c.π.app i) (U f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ M f =
        pullback.map (U f).hom (c.π.app i) (U f).hom (D.map (fs f))
          (𝟙 _) (c.π.app (js f)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext
      · simp [M]
      · simp [M, c.w (m f)]
    dsimp [θj]
    rw [← Category.assoc, hM]
    exact hdesc f
  let ej (f : B) : (Over.pullback (D.map h)).obj (U f) ⟶
      (Over.pullback (D.map h)).obj (W f) :=
    Over.homMk (pullback.lift (θj f) (pullback.snd (U f).hom (D.map h))
      ((hθj f).trans pullback.condition)) (by simp)
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  have hK (W : Over (D.obj i)) :
      (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) =
        pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
          pullback.fst W.hom (D.map h) :=
    by
      have hcomp (k : c.pt ⟶ D.obj i) (hk : c.π.app j ≫ D.map h = k) :
          ((((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
            eqToIso (congrArg (fun t : c.pt ⟶ D.obj i ↦ Over.pullback t) hk)).app W).hom).left ≫
              pullback.fst W.hom k =
            pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
              pullback.fst W.hom (D.map h) := by
        subst k
        simp [Over.pullbackComp, Adjunction.comp_counit_app]
      simpa [K] using hcomp (c.π.app i) (c.w h)
  have he (f : B) : (Over.pullback (c.π.app j)).map (ej f) ≫ K.hom.app (W f) =
      K.hom.app (U f) ≫ ψ f := by
    have hM : (K.hom.app (U f)).left ≫
        pullback.map (U f).hom (c.π.app i) (U f).hom (D.map h)
          (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) =
        pullback.fst (pullback.snd (U f).hom (D.map h)) (c.π.app j) := by
      apply pullback.hom_ext
      · simpa using hK (U f)
      · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
        change (K.hom.app (U f)).left ≫
          ((Over.pullback (c.π.app i)).obj (U f)).hom ≫ c.π.app j = _
        rw [← Category.assoc, Over.w]
        exact pullback.condition.symm
    ext1
    apply pullback.hom_ext
    · change (((Over.pullback (c.π.app j)).map (ej f)).left ≫
          (K.hom.app (W f)).left) ≫ pullback.fst (W f).hom (c.π.app i) =
        ((K.hom.app (U f)).left ≫ (ψ f).left) ≫
          pullback.fst (W f).hom (c.π.app i)
      rw [Category.assoc, hK (W f)]
      have hmapp : ((Over.pullback (c.π.app j)).map (ej f)).left ≫
          pullback.fst (pullback.snd (W f).hom (D.map h)) (c.π.app j) =
          pullback.fst (pullback.snd (U f).hom (D.map h)) (c.π.app j) ≫ (ej f).left := by
        simp
      rw [← Category.assoc, hmapp, Category.assoc]
      change pullback.fst _ _ ≫ (ej f).left ≫ pullback.fst (W f).hom (D.map h) =
        (K.hom.app (U f)).left ≫ θ f
      rw [show (ej f).left ≫ pullback.fst (W f).hom (D.map h) = θj f by simp [ej]]
      exact (congrArg (· ≫ θj f) hM).symm.trans
        ((Category.assoc _ _ _).trans (congrArg ((K.hom.app (U f)).left ≫ ·) (hj f)))
    · exact (Over.w (((Over.pullback (c.π.app j)).map (ej f)) ≫ K.hom.app (W f))).trans
        (Over.w (K.hom.app (U f) ≫ ψ f)).symm
  refine ⟨j, h, (fun {a b} f ↦ ej ⟨a, b, f⟩),
    (fun a ↦ K.app (V a) ≪≫ α a), ?_⟩
  intro a b f
  change (Over.pullback (c.π.app j)).map (ej ⟨a, b, f⟩) ≫
    K.hom.app (V b) ≫ (α b).hom = (K.hom.app (V a) ≫ (α a).hom) ≫ _
  rw [← Category.assoc, he]
  simp [ψ, U, Category.assoc, Paths.of]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite collection of equalities after limit pullback holds at one stage.

Source: Stacks Project, Limits, Tag 01ZM (3), finite common-stage argument.

Proof: For each r apply 01ZM (3) to x r and y r, obtaining a stage where their
pullbacks agree. Choose a common upper bound of these finitely many stages and i.
Pullback is functorial, so each equality persists at the common stage; naturality
of Over.pullbackComp transports it to the direct pullback along the transition.
For an empty family use i and its identity. -/
private theorem finite_morphism_equalities_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (R : Type v) [Finite R] (i : Iᵒᵖ) (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (x y : ∀ r, V r ⟶ W r)
    (hxy : ∀ r, (Over.pullback (c.π.app i)).map (x r) =
      (Over.pullback (c.π.app i)).map (y r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
  classical
  have hex : ∀ r, ∃ (j : Iᵒᵖ) (h : j ⟶ i),
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
    intro r
    have := (hV r).1
    have := (hV r).2.1
    have := (hV r).2.2
    have := (hW r).1
    have := (hW r).2.1
    have := (hW r).2.2
    have hfst : pullback.fst (V r).hom (c.π.app i) ≫ (x r).left =
        pullback.fst (V r).hom (c.π.app i) ≫ (y r).left := by
      have hh := congrArg
        (fun f ↦ f.left ≫ pullback.fst (W r).hom (c.π.app i)) (hxy r)
      simpa using hh
    obtain ⟨j, h, hh⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit
      hc (V r).hom (W r).hom (x r).left (y r).left
      (Over.w (x r)) (Over.w (y r)) hfst
    refine ⟨j, h, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa using hh
    · simp
  choose js fs hfs using hex
  obtain ⟨j, h, g, hg⟩ := IsCofiltered.wideCospan fs
  refine ⟨j, h, fun r ↦ ?_⟩
  let E : Over.pullback (D.map h) ≅
      Over.pullback (D.map (fs r)) ⋙ Over.pullback (D.map (g r)) :=
    eqToIso (congrArg (fun f : j ⟶ i ↦ Over.pullback (D.map f)) (hg r).symm) ≪≫
      eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp (g r) (fs r))) ≪≫
      Over.pullbackComp (D.map (g r)) (D.map (fs r))
  apply (cancel_mono (E.hom.app (W r))).mp
  rw [E.hom.naturality, E.hom.naturality]
  exact congrArg (E.hom.app (V r) ≫ ·)
    (congrArg (fun f ↦ (Over.pullback (D.map (g r))).map f) (hfs r))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Given object models at a single stage, the generating arrows and finitely many
relations lift after one further base change. No object descent or étaleness descent
is asserted here.

Source: Stacks Project, Limits, Tag 01ZM (2), (3), closing colimit assertion;
step 4 of lemma-acyclicity-pulled-back-injectives.
(blueprint: lem-weil-pbc-finite-diagram-lift-of-models).

Proof:
1. Conjugate each generating arrow of F by the supplied object isomorphisms.
   Apply 01ZM (2) to each resulting map between pullbacks of the specified models.
   A common upper bound of the finitely many arrow stages and i exists by directedness.
   Pull the maps to that bound, keeping their compatibility with the given limit maps.
2. Lift this quiver map by Paths.lift. The objectwise isomorphisms form a natural
   isomorphism on paths: prove the naturality equation by induction on a path, using
   the generator equations in the successor case and identities for the empty path.
3. The two composites of each relation agree after pullback, by naturality and
   cancellation of the comparison isomorphisms. Apply 01ZM (3) to these two maps.
   A common upper bound for the finitely many relation stages makes every relation
   hold simultaneously. Pull back the functor and comparisons to that stage.
4. At each change of stage the objects are the canonical pullbacks of V a, using
   pullback transitivity to identify iterated pullbacks with these specified objects.
   Transport the arrows through these identifications; functoriality and naturality
   preserve all equations. For an empty vertex, arrow, or relation type, choose i
   or the already chosen stage: the respective conditions are vacuous. -/
theorem finite_diagram_lift_of_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Finite A] [Quiver.{v} A]
    [Finite (Σ a b : A, Quiver.Hom a b)]
    (R : Type v) [Finite R] (s t : R → Paths A)
    (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt)
    (i : Iᵒᵖ) (V : A → Over (D.obj i))
    (hV : ∀ a, LocallyOfFinitePresentation (V a).hom ∧
      QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom)
    (α : ∀ a, (Over.pullback (c.π.app i)).obj (V a) ≅ F.obj a)
    (hR : ∀ r, F.map (p r) = F.map (q r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i) (G : Paths A ⥤ Over (D.obj j)),
      Nonempty (G ⋙ Over.pullback (c.π.app j) ≅ F) ∧
      (∀ a, G.obj a = (Over.pullback (D.map h)).obj (V a)) ∧
      (∀ r, G.map (p r) = G.map (q r)) := by
  classical
  obtain ⟨j, h, e, σ, he⟩ := finite_generators_lift D c hc A F i V hV α
  let φ : A ⥤q Over (D.obj j) :=
    { obj := fun a ↦ (Over.pullback (D.map h)).obj (V a)
      map := fun f ↦ e f }
  let H := Paths.lift φ
  have hn : ∀ {a b : Paths A} (f : a ⟶ b),
      (H ⋙ Over.pullback (c.π.app j)).map f ≫ (σ b).hom =
        (σ a).hom ≫ F.map f := by
    apply Paths.induction
    · intro a
      simp
    · intro a b d p f hp
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      change (Over.pullback (c.π.app j)).map (H.map p) ≫
          (Over.pullback (c.π.app j)).map (H.map ((Paths.of A).map f)) ≫ (σ d).hom = _
      rw [show H.map ((Paths.of A).map f) = e f from Paths.lift_toPath φ f, he]
      dsimp [Paths.of] at hp ⊢
      simpa only [Functor.comp_map, Category.assoc, Paths.of] using
        congrArg (· ≫ F.map ((Paths.of A).map f)) hp
  let γ : H ⋙ Over.pullback (c.π.app j) ≅ F := NatIso.ofComponents σ (fun f ↦ hn f)
  have hHR : ∀ r, (Over.pullback (c.π.app j)).map (H.map (p r)) =
      (Over.pullback (c.π.app j)).map (H.map (q r)) := by
    intro r
    apply (cancel_mono (σ (t r)).hom).mp
    exact (hn (p r)).trans ((congrArg ((σ (s r)).hom ≫ ·) (hR r)).trans
      (hn (q r)).symm)
  have hH : ∀ a, LocallyOfFinitePresentation (H.obj a).hom ∧
      QuasiCompact (H.obj a).hom ∧ QuasiSeparated (H.obj a).hom := by
    intro a
    have := (hV a).1
    have := (hV a).2.1
    have := (hV a).2.2
    change LocallyOfFinitePresentation (pullback.snd (V a).hom (D.map h)) ∧
      QuasiCompact (pullback.snd (V a).hom (D.map h)) ∧
      QuasiSeparated (pullback.snd (V a).hom (D.map h))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨k, l, hl⟩ := finite_morphism_equalities_lift D c hc R j
    (fun r ↦ H.obj (s r)) (fun r ↦ H.obj (t r))
    (fun r ↦ hH (s r)) (fun r ↦ hH (t r))
    (fun r ↦ H.map (p r)) (fun r ↦ H.map (q r)) hHR
  let K := H ⋙ Over.pullback (D.map l)
  let T : ∀ a, (Over.pullback (D.map (l ≫ h))).obj (V a) ≅ K.obj a :=
    fun a ↦ eqToIso (by rw [D.map_comp]) ≪≫
      (Over.pullbackComp (D.map l) (D.map h)).app (V a)
  let G := K.copyObj (fun a ↦ (Over.pullback (D.map (l ≫ h))).obj (V a))
    (fun a ↦ (T a).symm)
  have η : K ⋙ Over.pullback (c.π.app k) ≅ F :=
    (Functor.associator H (Over.pullback (D.map l)) (Over.pullback (c.π.app k))) ≪≫
      Functor.isoWhiskerLeft H (Over.pullbackComp (c.π.app k) (D.map l)).symm ≪≫
      Functor.isoWhiskerLeft H
        (eqToIso (congrArg (fun f : c.pt ⟶ D.obj j ↦ Over.pullback f) (c.w l))) ≪≫ γ
  refine ⟨k, l ≫ h, G,
    ⟨Functor.isoWhiskerRight (K.isoCopyObj _ (fun a ↦ (T a).symm)).symm
      (Over.pullback (c.π.app k)) ≪≫ η⟩, fun a ↦ rfl, ?_⟩
  intro r
  change (T (s r)).hom ≫ K.map (p r) ≫ (T (t r)).inv =
    (T (s r)).hom ≫ K.map (q r) ≫ (T (t r)).inv
  rw [show K.map (p r) = K.map (q r) from hl r]

end AlgebraicGeometry
