/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A finite family of persistent conditions, each enforceable after any refinement,
can be enforced simultaneously by successive refinements. -/
private theorem finite_refinement {J : Type z} [SmallCategory J]
    {α : Type} [Finite α] (j : J) (P : α → ∀ k : J, (j ⟶ k) → Prop)
    (hmono : ∀ a k l u v, P a k u → P a l (u ≫ v))
    (hex : ∀ a k u, ∃ (l : J) (v : k ⟶ l), P a l (u ≫ v)) :
    ∃ (k : J) (u : j ⟶ k), ∀ a, P a k u := by
  classical
  let _ := Fintype.ofFinite α
  have hs (s : Finset α) : ∃ (k : J) (u : j ⟶ k), ∀ a ∈ s, P a k u := by
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨k, u, hu⟩ := ih
      obtain ⟨l, v, hv⟩ := hex a k u
      refine ⟨l, u ≫ v, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hv
      · exact hmono b k l u v (hu b hb)
  obtain ⟨k, u, hu⟩ := hs Finset.univ
  exact ⟨k, u, fun a ↦ hu a (Finset.mem_univ a)⟩

/-- Joint surjectivity and a common upper stage give representatives of any finite list,
including an empty list. -/
private theorem finite_representatives {J : Type z} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ Type z) (t : Cocone G) (ht : IsColimit t)
    {α : Type} [Finite α] (x : α → t.pt) :
    ∃ (j : J) (y : α → G.obj j), ∀ a, t.ι.app j (y a) = x a := by
  classical
  let _ := Fintype.ofFinite α
  choose j y hy using fun a ↦ Types.jointly_surjective_of_isColimit ht (x a)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let u (a : α) : j a ⟶ k := (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨k, fun a ↦ G.map (u a) (y a), ?_⟩
  intro a
  exact (ConcreteCategory.congr_hom (t.w (u a)) (y a)).trans (hy a)

/-- A functor preserves arrow composites transported along equal middle endpoints. -/
private theorem map_arrow_composite {C D : Type z} [Category.{z} C] [Category.{z} D]
    (W : C ⥤ D) (b c : Arrow C) (h : b.right = c.left) :
    W.mapArrow.obj (Arrow.mk (b.hom ≫ eqToHom h ≫ c.hom)) =
      Arrow.mk ((W.mapArrow.obj b).hom ≫ eqToHom (congrArg W.obj h) ≫
        (W.mapArrow.obj c).hom) := by
  change Arrow.mk (W.map (b.hom ≫ eqToHom h ≫ c.hom)) =
    Arrow.mk (W.map b.hom ≫ eqToHom (congrArg W.obj h) ≫ W.map c.hom)
  simp only [Functor.map_comp, eqToHom_map]

/-- A functor sends the arrow of an identity to the arrow of the image identity. -/
private theorem map_arrow_identity {C D : Type z} [Category.{z} C] [Category.{z} D]
    (W : C ⥤ D) (x : C) :
    W.mapArrow.obj (Arrow.mk (𝟙 x)) = Arrow.mk (𝟙 (W.obj x)) := by
  exact congrArg Arrow.mk (W.map_id x)

/-- Equal arrow representatives have equal transported composites; endpoint equality
proofs do not affect the composite. -/
private theorem arrow_composite_congr {C : Type z} [Category.{z} C]
    {b c b' c' : Arrow C} (hb : b = b') (hc : c = c')
    (h : b.right = c.left) (h' : b'.right = c'.left) :
    Arrow.mk (b.hom ≫ eqToHom h ≫ c.hom) =
      Arrow.mk (b'.hom ≫ eqToHom h' ≫ c'.hom) := by
  subst b'
  subst c'
  rfl

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph;
Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-finite-lift).

Proof: Choose stage representatives of the objects and arrows using joint
surjectivity of their set colimits. Move the finitely many stages to a common
stage. For each arrow endpoint that equals a listed object in the colimit,
use eventual equality in the object colimit and refine until the equality holds.
Do the same for every pair of arrow endpoints that coincide. At this stage every
listed composite is defined. Functoriality identifies its colimit image with
the listed composite in O. Eventual equality in the arrow colimit now makes
each required composition and identity equation hold at a further stage.
There are finitely many of these equations; a common refinement preserves all
of them. The empty-list case uses the nonemptiness of the filtered category. -/
theorem filteredColimit_category_finite_lift
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O) (V : ∀ j : J, F.obj j ⥤ O),
      ((∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f)) →
      (∀ (n m : ℕ) (X : Fin n → O) (A : Fin m → Arrow O),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q, (V j).obj (Xj q) = X q) ∧
          (∀ p, (V j).mapArrow.obj (Aj p) = A p) ∧
          (∀ p q, (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ p q, (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ p q r (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ p q, A p = Arrow.mk (𝟙 (X q)) → Aj p = Arrow.mk (𝟙 (Xj q)))) := by
  classical
  dsimp only
  intro s V h n m X A
  obtain ⟨hobj, htrans, a, e, ⟨ha⟩, he⟩ := h
  have hvobj {j k : J} (u : j ⟶ k) (x : F.obj j) :
      (V k).obj ((F.map u).toFunctor.obj x) = (V j).obj x :=
    congrArg (fun W : F.obj j ⥤ colimit (F ⋙ Cat.objects) ↦ W.obj x) (htrans j k u)
  have hvarr {j k : J} (u : j ⟶ k) (b : Arrow (F.obj j)) :
      (V k).mapArrow.obj ((F.map u).toFunctor.mapArrow.obj b) = (V j).mapArrow.obj b :=
    congrArg (fun W : F.obj j ⥤ colimit (F ⋙ Cat.objects) ↦ W.mapArrow.obj b)
      (htrans j k u)
  have heqobj {j : J} (x y : F.obj j) (hxy : (V j).obj x = (V j).obj y) :
      ∃ (k : J) (u : j ⟶ k), (F.map u).toFunctor.obj x = (F.map u).toFunctor.obj y := by
    apply (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (F ⋙ Cat.objects)) x y).mp
    change colimit.ι (F ⋙ Cat.objects) j x = colimit.ι (F ⋙ Cat.objects) j y
    simpa only [← hobj] using hxy
  have heqarr {j : J} (b c : Arrow (F.obj j))
      (hbc : (V j).mapArrow.obj b = (V j).mapArrow.obj c) :
      ∃ (k : J) (u : j ⟶ k),
        (F.map u).toFunctor.mapArrow.obj b = (F.map u).toFunctor.mapArrow.obj c := by
    apply (Types.FilteredColimit.isColimit_eq_iff' ha b c).mp
    apply e.injective
    simpa only [he] using hbc
  obtain ⟨j₀, X₀, hX₀⟩ := finite_representatives (F ⋙ Cat.objects)
    (colimit.cocone (F ⋙ Cat.objects)) (colimit.isColimit _) X
  obtain ⟨j₁, A₁, hA₁⟩ := finite_representatives (F ⋙ Cat.arrows) a ha
    (fun p ↦ e.symm (A p))
  let j := IsFiltered.max j₀ j₁
  let Xj : Fin n → F.obj j := fun q ↦
    (F.map (IsFiltered.leftToMax j₀ j₁)).toFunctor.obj (X₀ q)
  let Aj : Fin m → Arrow (F.obj j) := fun p ↦
    (F.map (IsFiltered.rightToMax j₀ j₁)).toFunctor.mapArrow.obj (A₁ p)
  have hX (q : Fin n) : (V j).obj (Xj q) = X q := by
    rw [hvobj, hobj]
    exact hX₀ q
  have hA (p : Fin m) : (V j).mapArrow.obj (Aj p) = A p := by
    rw [hvarr, ← he, hA₁, e.apply_symm_apply]
  -- Align all equal endpoints, including middle endpoints of composites.
  let B : (Fin n ⊕ (Fin m × Bool)) → F.obj j := fun q ↦
    match q with
    | .inl q => Xj q
    | .inr (p, false) => (Aj p).left
    | .inr (p, true) => (Aj p).right
  let P (q : (Fin n ⊕ (Fin m × Bool)) × (Fin n ⊕ (Fin m × Bool)))
      (k : J) (u : j ⟶ k) : Prop :=
    (V j).obj (B q.1) = (V j).obj (B q.2) →
      (F.map u).toFunctor.obj (B q.1) = (F.map u).toFunctor.obj (B q.2)
  have hmono : ∀ q k l u v, P q k u → P q l (u ≫ v) := by
    intro q k l u v hu hq
    have hh := congrArg (F.map v).toFunctor.obj (hu hq)
    simpa using hh
  have hex : ∀ q k u, ∃ (l : J) (v : k ⟶ l), P q l (u ≫ v) := by
    intro q k u
    by_cases hq : (V j).obj (B q.1) = (V j).obj (B q.2)
    · have hh : (V k).obj ((F.map u).toFunctor.obj (B q.1)) =
          (V k).obj ((F.map u).toFunctor.obj (B q.2)) := by
        simpa only [hvobj] using hq
      obtain ⟨l, v, hv⟩ := heqobj _ _ hh
      refine ⟨l, v, fun _ ↦ ?_⟩
      simpa using hv
    · exact ⟨k, 𝟙 k, fun hh ↦ (hq hh).elim⟩
  obtain ⟨k, u, hu⟩ := finite_refinement j P hmono hex
  let Xk : Fin n → F.obj k := fun q ↦ (F.map u).toFunctor.obj (Xj q)
  let Ak : Fin m → Arrow (F.obj k) := fun p ↦
    (F.map u).toFunctor.mapArrow.obj (Aj p)
  have hXk (q : Fin n) : (V k).obj (Xk q) = X q := (hvobj u _).trans (hX q)
  have hAk (p : Fin m) : (V k).mapArrow.obj (Ak p) = A p :=
    (hvarr u _).trans (hA p)
  have hleft (p : Fin m) (q : Fin n) (h : (A p).left = X q) :
      (Ak p).left = Xk q := by
    apply hu (.inr (p, false), .inl q)
    change ((V j).mapArrow.obj (Aj p)).left = (V j).obj (Xj q)
    rw [hA, hX]
    exact h
  have hright (p : Fin m) (q : Fin n) (h : (A p).right = X q) :
      (Ak p).right = Xk q := by
    apply hu (.inr (p, true), .inl q)
    change ((V j).mapArrow.obj (Aj p)).right = (V j).obj (Xj q)
    rw [hA, hX]
    exact h
  have hmid (p q : Fin m) (h : (A p).right = (A q).left) :
      (Ak p).right = (Ak q).left := by
    apply hu (.inr (p, true), .inr (q, false))
    change ((V j).mapArrow.obj (Aj p)).right = ((V j).mapArrow.obj (Aj q)).left
    rw [hA, hA]
    exact h
  -- Refine once more to impose all composition and identity equations.
  let XL (l : J) (v : k ⟶ l) (q : Fin n) : F.obj l :=
    (F.map v).toFunctor.obj (Xk q)
  let AL (l : J) (v : k ⟶ l) (p : Fin m) : Arrow (F.obj l) :=
    (F.map v).toFunctor.mapArrow.obj (Ak p)
  have hALcomp {l l' : J} (v : k ⟶ l) (w : l ⟶ l') (p : Fin m) :
      AL l' (v ≫ w) p = (F.map w).toFunctor.mapArrow.obj (AL l v p) := by
    exact ConcreteCategory.congr_hom ((F ⋙ Cat.arrows).map_comp v w) (Ak p)
  have hXLcomp {l l' : J} (v : k ⟶ l) (w : l ⟶ l') (q : Fin n) :
      XL l' (v ≫ w) q = (F.map w).toFunctor.obj (XL l v q) := by
    exact ConcreteCategory.congr_hom ((F ⋙ Cat.objects).map_comp v w) (Xk q)
  let Q (t : (Fin m × Fin m × Fin m) ⊕ (Fin m × Fin n))
      (l : J) (v : k ⟶ l) : Prop :=
    match t with
    | .inl (p, q, r) => ∀ (h : (A p).right = (A q).left),
        Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
        ∃ hl : (AL l v p).right = (AL l v q).left,
          Arrow.mk ((AL l v p).hom ≫ eqToHom hl ≫ (AL l v q).hom) = AL l v r
    | .inr (p, q) => A p = Arrow.mk (𝟙 (X q)) →
        AL l v p = Arrow.mk (𝟙 (XL l v q))
  have hQmono : ∀ t l l' v w, Q t l v → Q t l' (v ≫ w) := by
    intro t l l' v w ht
    rcases t with ⟨p, q, r⟩ | ⟨p, q⟩
    · intro h hh
      obtain ⟨hl, hhl⟩ := ht h hh
      have hz := congrArg (F.map w).toFunctor.mapArrow.obj hhl
      rw [map_arrow_composite] at hz
      refine ⟨?_, ?_⟩
      · simpa [AL, F.map_comp] using congrArg (F.map w).toFunctor.obj hl
      · exact (arrow_composite_congr (hALcomp v w p) (hALcomp v w q) _ _).trans
          (hz.trans (hALcomp v w r).symm)
    · intro hh
      have hz := congrArg (F.map w).toFunctor.mapArrow.obj (ht hh)
      exact (hALcomp v w p).trans (hz.trans
        ((map_arrow_identity (F.map w).toFunctor _).trans
          (congrArg (fun x ↦ Arrow.mk (𝟙 x)) (hXLcomp v w q).symm)))
  have hQex : ∀ t l v, ∃ (l' : J) (w : l ⟶ l'), Q t l' (v ≫ w) := by
    intro t l v
    rcases t with ⟨p, q, r⟩ | ⟨p, q⟩
    · by_cases h : (A p).right = (A q).left
      · by_cases hh : Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r
        · have hl : (AL l v p).right = (AL l v q).left :=
            congrArg (F.map v).toFunctor.obj (hmid p q h)
          have hAL (p : Fin m) : (V l).mapArrow.obj (AL l v p) = A p :=
            (hvarr v _).trans (hAk p)
          have himage : (V l).mapArrow.obj
              (Arrow.mk ((AL l v p).hom ≫ eqToHom hl ≫ (AL l v q).hom)) =
                (V l).mapArrow.obj (AL l v r) := by
            rw [map_arrow_composite]
            exact (arrow_composite_congr (hAL p) (hAL q) _ h).trans
              (hh.trans (hAL r).symm)
          obtain ⟨l', w, hw⟩ := heqarr _ _ himage
          rw [map_arrow_composite] at hw
          refine ⟨l', w, fun _ _ ↦ ⟨?_, ?_⟩⟩
          · simpa [AL, F.map_comp] using congrArg (F.map w).toFunctor.obj hl
          · exact (arrow_composite_congr (hALcomp v w p) (hALcomp v w q) _ _).trans
              (hw.trans (hALcomp v w r).symm)
        · exact ⟨l, 𝟙 l, fun _ hh' ↦ (hh hh').elim⟩
      · exact ⟨l, 𝟙 l, fun h' _ ↦ (h h').elim⟩
    · by_cases hh : A p = Arrow.mk (𝟙 (X q))
      · have himage : (V l).mapArrow.obj (AL l v p) =
            (V l).mapArrow.obj (Arrow.mk (𝟙 (XL l v q))) := by
          calc
            _ = A p := (hvarr v _).trans (hAk p)
            _ = Arrow.mk (𝟙 (X q)) := hh
            _ = _ := by
              rw [map_arrow_identity]
              exact congrArg (fun x ↦ Arrow.mk (𝟙 x))
                ((hvobj v _).trans (hXk q)).symm
        obtain ⟨l', w, hw⟩ := heqarr _ _ himage
        refine ⟨l', w, fun _ ↦ ?_⟩
        exact (hALcomp v w p).trans (hw.trans
          ((map_arrow_identity (F.map w).toFunctor _).trans
            (congrArg (fun x ↦ Arrow.mk (𝟙 x)) (hXLcomp v w q).symm)))
      · exact ⟨l, 𝟙 l, fun hh' ↦ (hh hh').elim⟩
  obtain ⟨l, v, hv⟩ := finite_refinement k Q hQmono hQex
  refine ⟨l, XL l v, AL l v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (hvobj v _).trans (hXk q)
  · intro p
    exact (hvarr v _).trans (hAk p)
  · intro p q h
    exact congrArg (F.map v).toFunctor.obj (hleft p q h)
  · intro p q h
    exact congrArg (F.map v).toFunctor.obj (hright p q h)
  · intro p q r
    exact hv (.inl (p, q, r))
  · intro p q
    exact hv (.inr (p, q))

end CategoryTheory
