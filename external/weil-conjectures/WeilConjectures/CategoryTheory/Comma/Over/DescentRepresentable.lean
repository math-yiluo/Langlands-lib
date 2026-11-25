/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descending a representing object

Let `p : X ⟶ Y` be a morphism, `F` a presheaf on `Over Y`, and `V` an object over `X`
representing the restriction of `F` to `Over X`. Let `V₀` be an object over `Y` with
`V ≅ V₀ ×_Y X` through `q : V ⟶ V₀`, such that `q` is invariant under the canonical descent
datum of `V`. If the base changes `T ×_Y X ⟶ T` of `p` are epimorphisms along which the points
of `V₀` descend and for which `F` satisfies the sheaf condition, then `V₀` represents `F`.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.nonempty_representableBy_of_descent`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor.RepresentableBy

open Limits Opposite

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} {p : X ⟶ Y}
  {F : (Over Y)ᵒᵖ ⥤ Type w}

/-- The base change `T ×_Y X` of `p` along `T ⟶ Y`, as an object over `Y`. -/
noncomputable abbrev descentCover (p : X ⟶ Y) (T : Over Y) : Over Y :=
  Over.mk (pullback.snd T.hom p ≫ p)

/-- The projection `T ×_Y X ⟶ T`, as a morphism over `Y`. -/
noncomputable abbrev descentCoverπ (p : X ⟶ Y) (T : Over Y) : descentCover p T ⟶ T :=
  Over.homMk (pullback.fst T.hom p) pullback.condition

/-- The fibre product `(T ×_Y X) ×_T (T ×_Y X)`, as an object over `Y`. -/
noncomputable abbrev descentCover₂ (p : X ⟶ Y) (T : Over Y) : Over Y :=
  Over.mk (pullback.fst (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ pullback.fst T.hom p ≫
    T.hom)

/-- The two projections `(T ×_Y X) ×_T (T ×_Y X) ⟶ T ×_Y X`, as morphisms over `Y`. -/
noncomputable abbrev descentCoverPr₁ (p : X ⟶ Y) (T : Over Y) :
    descentCover₂ p T ⟶ descentCover p T :=
  Over.homMk (pullback.fst (pullback.fst T.hom p) (pullback.fst T.hom p)) (by
    simp only [Over.mk_hom]
    rw [pullback.condition])

/-- The second projection of the fibre product, as a morphism over `Y`. -/
noncomputable abbrev descentCoverPr₂ (p : X ⟶ Y) (T : Over Y) :
    descentCover₂ p T ⟶ descentCover p T :=
  Over.homMk (pullback.snd (pullback.fst T.hom p) (pullback.fst T.hom p)) (by
    simp only [Over.mk_hom]
    rw [pullback.condition_assoc, pullback.condition])


variable {V : Over X} (r : ((Over.map p).op ⋙ F).RepresentableBy V) {V₀ : Over Y}
  (q : V.left ⟶ V₀.left)
  (hq : IsPullback q V.hom V₀.hom p)
  (hinv : ∀ {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
    (r.overTransport f₁ f₂ h a).left ≫ q = a.left ≫ q)

include hq hinv in
/-- A point of `V` over `T ×_Y X` lies in the descent equaliser for `F` exactly when its image
in `V₀` lies in the descent equaliser for `V₀`. -/
lemma map_descentCoverPr_eq_iff (T : Over Y) (a : Over.mk (pullback.snd T.hom p) ⟶ V) :
    F.map (descentCoverPr₁ p T).op (r.homEquiv a) =
        F.map (descentCoverPr₂ p T).op (r.homEquiv a) ↔
      pullback.fst (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a.left ≫ q =
        pullback.snd (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a.left ≫ q := by
  let π := pullback.fst T.hom p
  let s := pullback.snd T.hom p
  let fst₂ := pullback.fst π π
  let snd₂ := pullback.snd π π
  have hc : π ≫ T.hom = s ≫ p := pullback.condition
  have hc₂ : fst₂ ≫ π = snd₂ ≫ π := pullback.condition
  have h : (fst₂ ≫ s) ≫ p = (snd₂ ≫ s) ≫ p := by
    simp only [Category.assoc]
    rw [← hc, ← Category.assoc, hc₂, Category.assoc]
  let a₁ : Over.mk (fst₂ ≫ s) ⟶ V :=
    (Over.homMk (U := Over.mk (fst₂ ≫ s)) (V := Over.mk s) fst₂ rfl) ≫ a
  let a₂ : Over.mk (snd₂ ≫ s) ⟶ V :=
    (Over.homMk (U := Over.mk (snd₂ ≫ s)) (V := Over.mk s) snd₂ rfl) ≫ a
  have w₁ : 𝟙 _ ≫ (fst₂ ≫ s) ≫ p = fst₂ ≫ π ≫ T.hom := by
    rw [Category.id_comp, Category.assoc, hc]
  have w₂ : 𝟙 _ ≫ (snd₂ ≫ s) ≫ p = fst₂ ≫ π ≫ T.hom := by
    rw [w₁.symm, Category.id_comp, Category.id_comp, h]
  let e₁ : descentCover₂ p T ⟶ (Over.map p).obj (Over.mk (fst₂ ≫ s)) := Over.homMk (𝟙 _) w₁
  let e₂ : descentCover₂ p T ⟶ (Over.map p).obj (Over.mk (snd₂ ≫ s)) := Over.homMk (𝟙 _) w₂
  have he₂ : IsIso e₂ := ⟨Over.homMk (𝟙 _) (by
      rw [Category.id_comp]
      exact (Category.id_comp _).symm.trans w₂ |>.symm), by ext; simp [e₂],
    by ext; simp [e₂]⟩
  have hPr₁ : descentCoverPr₁ p T =
      e₁ ≫ (Over.map p).map (Over.homMk (U := Over.mk (fst₂ ≫ s)) (V := Over.mk s) fst₂ rfl) := by
    ext; simp [e₁, fst₂, π]
  have hPr₂ : descentCoverPr₂ p T =
      e₂ ≫ (Over.map p).map (Over.homMk (U := Over.mk (snd₂ ≫ s)) (V := Over.mk s) snd₂ rfl) := by
    ext; simp [e₂, snd₂, π]
  have he : e₁ = e₂ ≫ overMapHomMkId (fst₂ ≫ s) (snd₂ ≫ s) h := by
    ext; simp [e₁, e₂]
  have hF₁ : F.map (descentCoverPr₁ p T).op (r.homEquiv a) =
      F.map e₂.op (r.homEquiv (r.overTransport _ _ h a₁)) := by
    erw [homEquiv_overTransport]
    rw [r.homEquiv_comp, hPr₁, he]
    simp only [Functor.comp_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  have hF₂ : F.map (descentCoverPr₂ p T).op (r.homEquiv a) = F.map e₂.op (r.homEquiv a₂) := by
    rw [r.homEquiv_comp, hPr₂]
    simp only [Functor.comp_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  have hinj : Function.Injective (F.map e₂.op) := by
    have : IsIso (F.map e₂.op) := inferInstance
    exact (isIso_iff_bijective _).1 this |>.1
  rw [hF₁, hF₂, hinj.eq_iff, r.homEquiv.injective.eq_iff]
  constructor
  · intro hta
    have := hinv _ _ h a₁
    rw [hta] at this
    simpa [a₁, a₂, fst₂, snd₂, π] using this.symm
  · intro hla
    refine Over.OverMorphism.ext (hq.hom_ext ?_ ?_)
    · rw [hinv]
      simpa [a₁, a₂, fst₂, snd₂, π] using hla
    · simp only [Over.w]

include hq hinv in
/-- **Descending a representing object.** Let `V` represent the restriction of `F` to `Over X`,
and let `q : V ⟶ V₀` exhibit `V` as `V₀ ×_Y X` compatibly with the canonical descent datum of
`V`:
```
  V ---q---> V₀
  |          |
  v          v
  X ---p---> Y
```
For `T` over `Y` consider the base change `π : T ×_Y X ⟶ T` of `p` and the two projections
```
                         pr₁
  (T ×_Y X) ×_T (T ×_Y X) ====> T ×_Y X --π--> T
                         pr₂
```
If every such `π` is an epimorphism along which the points of `V₀` descend (a point of `V₀` over
`T ×_Y X` whose two pullbacks along `pr₁`, `pr₂` agree comes from `T`), and `F` satisfies the
sheaf condition for the covering `π`, then `V₀` represents `F`. -/
theorem exists_representableBy_of_descent
    (hepi : ∀ T : Over Y, Epi (pullback.fst T.hom p))
    (hV₀ : ∀ (T : Over Y) (a : pullback T.hom p ⟶ V₀.left),
      pullback.fst (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a =
        pullback.snd (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a →
      ∃ b : T.left ⟶ V₀.left, pullback.fst T.hom p ≫ b = a)
    (hF : ∀ T : Over Y, Presieve.IsSheafFor F (.singleton (descentCoverπ p T))) :
    ∃ e : F.RepresentableBy V₀, ∀ (T : Over Y) (b : T ⟶ V₀),
      F.map (descentCoverπ p T).op (e.homEquiv b) =
        r.homEquiv (Over.homMk (hq.lift (pullback.fst T.hom p ≫ b.left) (pullback.snd T.hom p)
          (by rw [Category.assoc, Over.w b, pullback.condition])) (hq.lift_snd _ _ _) :
            Over.mk (pullback.snd T.hom p) ⟶ V) := by
  have hFinj (T : Over Y) (x₁ x₂ : F.obj (op T))
      (h : F.map (descentCoverπ p T).op x₁ = F.map (descentCoverπ p T).op x₂) : x₁ = x₂ :=
    (Presieve.isSheafFor_singleton.1 (hF T) _ fun p₁ p₂ hp ↦ by
      simp only [← Functor.map_comp_apply, ← op_comp, hp]).unique rfl h.symm
  have hFglue (T : Over Y) (y : F.obj (op (descentCover p T)))
      (hy : F.map (descentCoverPr₁ p T).op y = F.map (descentCoverPr₂ p T).op y) :
      ∃ x, F.map (descentCoverπ p T).op x = y := by
    refine (Presieve.isSheafFor_singleton.1 (hF T) y fun {Z} p₁ p₂ hp ↦ ?_).exists
    let c : Z ⟶ descentCover₂ p T := Over.homMk (pullback.lift p₁.left p₂.left
      (congrArg CommaMorphism.left hp)) (by
        simp only [Over.mk_hom, pullback.lift_fst_assoc]
        rw [pullback.condition, ← Category.assoc]
        exact (Category.assoc _ _ _).trans (Over.w p₁))
    have h₁ : p₁ = c ≫ descentCoverPr₁ p T := by
      ext
      simp [c]
    have h₂ : p₂ = c ≫ descentCoverPr₂ p T := by
      ext
      simp [c]
    rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      hy]
  -- the point of `V` over `T ×_Y X` attached to a point `b` of `V₀` over `T`
  let lift (T : Over Y) (b : T ⟶ V₀) : Over.mk (pullback.snd T.hom p) ⟶ V :=
    Over.homMk (hq.lift (pullback.fst T.hom p ≫ b.left) (pullback.snd T.hom p) (by
      rw [Category.assoc, Over.w b, pullback.condition])) (hq.lift_snd _ _ _)
  have hlift (T : Over Y) (b : T ⟶ V₀) :
      (lift T b).left ≫ q = pullback.fst T.hom p ≫ b.left := hq.lift_fst _ _ _
  have hdesc (T : Over Y) (b : T ⟶ V₀) :
      F.map (descentCoverPr₁ p T).op (r.homEquiv (lift T b)) =
        F.map (descentCoverPr₂ p T).op (r.homEquiv (lift T b)) := by
    rw [map_descentCoverPr_eq_iff r q hq hinv, hlift, ← Category.assoc, pullback.condition,
      Category.assoc]
  let toPt (T : Over Y) (y : F.obj (op (descentCover p T))) :
      Over.mk (pullback.snd T.hom p) ⟶ V := r.homEquiv.symm y
  -- the point of `V₀` over `T` attached to a section of `F` over `T`
  have hpt (T : Over Y) (x : F.obj (op T)) : ∃ b : T ⟶ V₀,
      (toPt T (F.map (descentCoverπ p T).op x)).left ≫ q =
        pullback.fst T.hom p ≫ b.left := by
    let a := toPt T (F.map (descentCoverπ p T).op x)
    have ha : F.map (descentCoverPr₁ p T).op (r.homEquiv a) =
        F.map (descentCoverPr₂ p T).op (r.homEquiv a) := by
      have hpr : descentCoverPr₁ p T ≫ descentCoverπ p T =
          descentCoverPr₂ p T ≫ descentCoverπ p T := by
        ext
        exact pullback.condition
      simp only [a, toPt, Equiv.apply_symm_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, hpr]
    obtain ⟨b, hb⟩ := hV₀ T (a.left ≫ q) ((map_descentCoverPr_eq_iff r q hq hinv T a).1 ha)
    have := hepi T
    refine ⟨Over.homMk b ?_, hb.symm⟩
    rw [← cancel_epi (pullback.fst T.hom p), ← Category.assoc, hb, Category.assoc, hq.w,
      ← Category.assoc, Over.w a, pullback.condition]
    rfl
  choose Φ hΦ using hpt
  have hlift_eq (T : Over Y) (a : Over.mk (pullback.snd T.hom p) ⟶ V) (b : T ⟶ V₀)
      (hab : a.left ≫ q = pullback.fst T.hom p ≫ b.left) : a = lift T b := by
    refine Over.OverMorphism.ext (hq.hom_ext ?_ ?_)
    · rw [hab, hlift]
    · rw [Over.w a, Over.w (lift T b)]
  have hΦ_eq (T : Over Y) (x : F.obj (op T)) :
      F.map (descentCoverπ p T).op x = r.homEquiv (lift T (Φ T x)) := by
    rw [← hlift_eq T _ _ (hΦ T x)]
    exact (Equiv.apply_symm_apply _ _).symm
  refine ⟨{ homEquiv {T} := { toFun b := (hFglue T _ (hdesc T b)).choose
                              invFun x := Φ T x
                              left_inv b := ?_
                              right_inv x := ?_ }
            homEquiv_comp {T' T} c b := ?_ }, fun T b ↦ (hFglue T _ (hdesc T b)).choose_spec⟩
  · have := hepi T
    have h₁ := (hFglue T _ (hdesc T b)).choose_spec
    refine Over.OverMorphism.ext ((cancel_epi (pullback.fst T.hom p)).1 ?_)
    rw [← hΦ, h₁]
    change (r.homEquiv.symm (r.homEquiv (lift T b))).left ≫ q = _
    rw [Equiv.symm_apply_apply, hlift]
  · apply hFinj
    rw [(hFglue T _ (hdesc T (Φ T x))).choose_spec, hΦ_eq]
  · apply hFinj
    change F.map (descentCoverπ p T').op (hFglue T' _ (hdesc T' (c ≫ b))).choose =
      F.map (descentCoverπ p T').op (F.map c.op (hFglue T _ (hdesc T b)).choose)
    rw [(hFglue T' _ (hdesc T' (c ≫ b))).choose_spec, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp]
    let cc : Over.mk (pullback.snd T'.hom p) ⟶ Over.mk (pullback.snd T.hom p) :=
      Over.homMk (pullback.map _ _ _ _ c.left (𝟙 X) (𝟙 Y) (by simp) (by simp))
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    have hcc : descentCoverπ p T' ≫ c = (Over.map p).map cc ≫ descentCoverπ p T := by
      ext
      simp only [Over.comp_left, Over.homMk_left, Over.map_map_left, cc]
      exact (pullback.lift_fst _ _ _).symm
    rw [hcc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [(hFglue T _ (hdesc T b)).choose_spec]
    change _ = ((Over.map p).op ⋙ F).map cc.op (r.homEquiv (lift T b))
    rw [← r.homEquiv_comp]
    congr 1
    refine (hlift_eq T' _ _ ?_).symm
    simp only [Over.comp_left, Category.assoc, hlift, cc, Over.homMk_left]
    rw [pullback.lift_fst_assoc, Category.assoc]

include hq hinv in
/-- **Descending a representing object**, without the compatibility of
`CategoryTheory.Functor.RepresentableBy.exists_representableBy_of_descent`. -/
theorem nonempty_representableBy_of_descent
    (hepi : ∀ T : Over Y, Epi (pullback.fst T.hom p))
    (hV₀ : ∀ (T : Over Y) (a : pullback T.hom p ⟶ V₀.left),
      pullback.fst (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a =
        pullback.snd (pullback.fst T.hom p) (pullback.fst T.hom p) ≫ a →
      ∃ b : T.left ⟶ V₀.left, pullback.fst T.hom p ≫ b = a)
    (hF : ∀ T : Over Y, Presieve.IsSheafFor F (.singleton (descentCoverπ p T))) :
    Nonempty (F.RepresentableBy V₀) :=
  ⟨(exists_representableBy_of_descent r q hq hinv hepi hV₀ hF).choose⟩


omit [HasPullbacks C] in
/-- **The sheaf condition for a single morphism transfers along `Over.map g`.** If `P` satisfies the
sheaf condition for the image of `π : T' ⟶ T` under `Over.map g`, then `(Over.map g).op ⋙ P`
satisfies it for `π`: an object over `X'` with a morphism to `(Over.map g).obj T'` is an
object over `X`. -/
lemma isSheafFor_singleton_overMap {X' : C} (g : X ⟶ X') {G : (Over X')ᵒᵖ ⥤ Type w}
    {T T' : Over X} (π : T' ⟶ T)
    (h : Presieve.IsSheafFor G (.singleton ((Over.map g).map π))) :
    Presieve.IsSheafFor ((Over.map g).op ⋙ G) (.singleton π) := by
  rw [Presieve.isSheafFor_singleton] at h ⊢
  intro y hy
  -- an object `Z'` over `X'` with a morphism `a` to `T'` is an object over `X`
  let lift {Z' : Over X'} (a : Z' ⟶ (Over.map g).obj T') : Over X := Over.mk (a.left ≫ T'.hom)
  let e {Z' : Over X'} (a : Z' ⟶ (Over.map g).obj T') : Z' ⟶ (Over.map g).obj (lift a) :=
    Over.homMk (𝟙 _) (by simp [lift, ← Over.w a])
  obtain ⟨x, hx, hxu⟩ := h y fun {Z'} p₁ p₂ hp ↦ by
    have hl : p₂.left ≫ T'.hom = p₁.left ≫ T'.hom := by
      rw [← Over.w π]
      simpa using congrArg (fun φ ↦ φ.left ≫ T.hom) hp.symm
    let q₁ : lift p₁ ⟶ T' := Over.homMk p₁.left rfl
    let q₂ : lift p₁ ⟶ T' := Over.homMk p₂.left hl
    have hq : q₁ ≫ π = q₂ ≫ π := by
      ext
      simpa [q₁, q₂] using congrArg CommaMorphism.left hp
    have h₁ : p₁ = e p₁ ≫ (Over.map g).map q₁ := by
      ext
      simp [e, q₁]
    have h₂ : p₂ = e p₁ ≫ (Over.map g).map q₂ := by
      ext
      simp [e, q₂]
    rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (G.map (e p₁).op) (hy q₁ q₂ hq)
  exact ⟨x, hx, fun x' hx' ↦ hxu x' hx'⟩

end CategoryTheory.Functor.RepresentableBy
