import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Finite fibre powers of a scheme chart of a presheaf

For a representable map `a : h_V → X` from a scheme `V` over `S` to a presheaf `X`, and a
finite nonempty index type `ι`, the `ι`-fold fibre power `V ×_X ⋯ ×_X V` is an actual scheme
over `S`. Its points over a test scheme `T` are the `ι`-indexed families of points of `V`
over `T` with equal images in `X`. When `V` is separated over `S` the fibre power is
separated over `S`, and when `a` is étale every projection is étale. A group indexing the
fibre power acts on it by permuting the factors.
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : Presheaf S} {V : Over S}

/-- An `ι`-fold fibre power of the chart `a : h_V → X`: a scheme over `S` with projections to
`V` that have equal images in `X`, universal among such families. -/
structure ChartFibrePower (a : (schemeYoneda S).obj V ⟶ X) (ι : Type v) where
  /-- The fibre power, as a scheme over `S`. -/
  obj : Over S
  /-- The projections. -/
  pr : ι → (obj ⟶ V)
  w : ∀ i j, (schemeYoneda S).map (pr i) ≫ a = (schemeYoneda S).map (pr j) ≫ a
  /-- The point of the fibre power given by a family with equal images. -/
  lift : ∀ {T : Over S} (y : ι → (T ⟶ V)),
    (∀ i j, (schemeYoneda S).map (y i) ≫ a = (schemeYoneda S).map (y j) ≫ a) → (T ⟶ obj)
  lift_pr : ∀ {T : Over S} (y : ι → (T ⟶ V))
    (hy : ∀ i j, (schemeYoneda S).map (y i) ≫ a = (schemeYoneda S).map (y j) ≫ a) (i : ι),
    lift y hy ≫ pr i = y i
  hom_ext : ∀ {T : Over S} (f g : T ⟶ obj), (∀ i, f ≫ pr i = g ≫ pr i) → f = g

namespace ChartFibrePower

variable {a : (schemeYoneda S).obj V ⟶ X}

attribute [reassoc (attr := simp)] lift_pr

/-- The one-fold fibre power is the chart itself. -/
def one (a : (schemeYoneda S).obj V ⟶ X) : ChartFibrePower a (Fin 1) where
  obj := V
  pr _ := 𝟙 V
  w _ _ := rfl
  lift y _ := y 0
  lift_pr y _ i := by
    rw [Category.comp_id, Subsingleton.elim i 0]
  hom_ext f g h := by simpa using h 0

/-- Reindexing a fibre power along an equivalence of index types. -/
def reindex {ι : Type v} {κ : Type*} (P : ChartFibrePower a ι) (e : κ ≃ ι) :
    ChartFibrePower a κ where
  obj := P.obj
  pr k := P.pr (e k)
  w k l := P.w (e k) (e l)
  lift y hy := P.lift (fun i => y (e.symm i)) (fun i j => hy _ _)
  lift_pr y hy k := by
    rw [P.lift_pr, e.symm_apply_apply]
  hom_ext f g h := P.hom_ext f g fun i => by
    simpa using h (e.symm i)

section Succ

variable (ha : (schemeYoneda S).relativelyRepresentable a) {n : ℕ}
  (P : ChartFibrePower a (Fin (n + 1)))

/-- The map from the fibre power to `X`, through the first projection. -/
abbrev toBase : (schemeYoneda S).obj P.obj ⟶ X := (schemeYoneda S).map (P.pr 0) ≫ a

/-- The new fibre power, as the represented pullback of the chart along `P.toBase`. -/
abbrev succObj : Over S := Functor.relativelyRepresentable.pullback ha P.toBase

/-- The projection of the new fibre power to the old one. -/
abbrev succSnd : succObj ha P ⟶ P.obj := Functor.relativelyRepresentable.snd ha P.toBase

/-- The new factor of the new fibre power. -/
abbrev succFst : succObj ha P ⟶ V := Functor.relativelyRepresentable.fst' ha P.toBase

theorem succ_isPullback : IsPullback ((schemeYoneda S).map (succFst ha P))
    ((schemeYoneda S).map (succSnd ha P)) a P.toBase :=
  Functor.relativelyRepresentable.isPullback' ha P.toBase

/-- The projections of the new fibre power. -/
def succPr : Fin (n + 2) → (succObj ha P ⟶ V) :=
  Fin.cases (succFst ha P) fun i => succSnd ha P ≫ P.pr i

@[simp] theorem succPr_zero : succPr ha P 0 = succFst ha P := rfl

@[simp] theorem succPr_succ (i : Fin (n + 1)) :
    succPr ha P i.succ = succSnd ha P ≫ P.pr i := rfl

theorem succPr_image (i : Fin (n + 2)) :
    (schemeYoneda S).map (succPr ha P i) ≫ a =
      (schemeYoneda S).map (succSnd ha P) ≫ P.toBase := by
  induction i using Fin.cases with
  | zero => exact (succ_isPullback ha P).w
  | succ i =>
    rw [succPr_succ, Functor.map_comp, Category.assoc, P.w i 0]

/-- The fibre power with one more factor. -/
def succ : ChartFibrePower a (Fin (n + 2)) where
  obj := succObj ha P
  pr := succPr ha P
  w i j := by rw [succPr_image, succPr_image]
  lift y hy := Functor.relativelyRepresentable.lift' ha (y 0)
    (P.lift (fun i => y i.succ) (fun i j => hy _ _)) (by
      change _ = (schemeYoneda S).map _ ≫ (schemeYoneda S).map (P.pr 0) ≫ a
      rw [← Functor.map_comp_assoc, P.lift_pr]
      exact hy 0 1)
  lift_pr y hy i := by
    induction i using Fin.cases with
    | zero => exact Functor.relativelyRepresentable.lift'_fst _ _ _ _
    | succ i =>
      rw [succPr_succ, Functor.relativelyRepresentable.lift'_snd_assoc, P.lift_pr]
  hom_ext f g h := by
    apply Functor.relativelyRepresentable.hom_ext' ha
    · exact h 0
    · exact P.hom_ext _ _ fun i => by simpa using h i.succ

end Succ

/-- Fibre powers indexed by `Fin (n + 1)` exist. -/
def fin (ha : (schemeYoneda S).relativelyRepresentable a) :
    ∀ n : ℕ, ChartFibrePower a (Fin (n + 1))
  | 0 => one a
  | n + 1 => succ ha (fin ha n)

/-- Separatedness of the new fibre power over `S`. -/
theorem succ_isSeparated (ha : (schemeYoneda S).relativelyRepresentable a) {n : ℕ}
    (P : ChartFibrePower a (Fin (n + 1))) [IsSeparated V.hom] [IsSeparated P.obj.hom] :
    IsSeparated (succ ha P).obj.hom := by
  let m : (succObj ha P).left ⟶ Limits.pullback P.obj.hom V.hom :=
    Limits.pullback.lift (succSnd ha P).left (succFst ha P).left
      ((Over.w (succSnd ha P)).trans (Over.w (succFst ha P)).symm)
  have hsnd : (succSnd ha P).left = m ≫ Limits.pullback.fst P.obj.hom V.hom :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hfst : (succFst ha P).left = m ≫ Limits.pullback.snd P.obj.hom V.hom :=
    (Limits.pullback.lift_snd _ _ _).symm
  have hm : Mono m := by
    constructor
    intro W g₁ g₂ hg
    have h₁ : g₁ ≫ (succSnd ha P).left = g₂ ≫ (succSnd ha P).left := by
      rw [hsnd, reassoc_of% hg]
    have h₂ : g₁ ≫ (succFst ha P).left = g₂ ≫ (succFst ha P).left := by
      rw [hfst, reassoc_of% hg]
    let T : Over S := Over.mk (g₁ ≫ (succObj ha P).hom)
    have hT : g₂ ≫ (succObj ha P).hom = g₁ ≫ (succObj ha P).hom := by
      rw [← Over.w (succSnd ha P), reassoc_of% h₁]
    let f₁ : T ⟶ succObj ha P := Over.homMk g₁
    let f₂ : T ⟶ succObj ha P := Over.homMk g₂ hT
    have : f₁ = f₂ := by
      apply (succ ha P).hom_ext
      intro i
      induction i using Fin.cases with
      | zero => exact Over.OverMorphism.ext h₂
      | succ i =>
        change f₁ ≫ succSnd ha P ≫ P.pr i = f₂ ≫ succSnd ha P ≫ P.pr i
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        exact Over.OverMorphism.ext h₁
    exact congrArg CommaMorphism.left this
  change IsSeparated (succObj ha P).hom
  rw [← Over.w (succSnd ha P), hsnd, Category.assoc]
  infer_instance

/-- Étaleness of the projections of the new fibre power. -/
theorem succ_etale (ha : IsEtale a) {n : ℕ} (P : ChartFibrePower a (Fin (n + 1)))
    (hP : ∀ i, Etale (P.pr i).left) (i : Fin (n + 2)) :
    Etale ((succ ha.1 P).pr i).left := by
  have hsq := succ_isPullback ha.1 P
  have hsnd : Etale (succSnd ha.1 P).left :=
    ha.projection P.toBase _ _ hsq
  induction i using Fin.cases with
  | zero =>
    have hc : IsEtale P.toBase := IsEtale.comp (isEtale_map _ (hP 0)) ha
    exact hc.projection a _ _ hsq.flip
  | succ i =>
    have := hP i
    change Etale ((succSnd ha.1 P).left ≫ (P.pr i).left)
    infer_instance

theorem fin_properties (ha : IsEtale a) [IsSeparated V.hom] :
    ∀ n : ℕ, IsSeparated (fin ha.1 n).obj.hom ∧
      ∀ i, Etale ((fin ha.1 n).pr i).left
  | 0 => ⟨inferInstanceAs (IsSeparated V.hom), fun _ => inferInstanceAs (Etale (𝟙 V.left))⟩
  | n + 1 => by
    obtain ⟨h₁, h₂⟩ := fin_properties ha n
    have := h₁
    exact ⟨succ_isSeparated ha.1 _, succ_etale ha _ h₂⟩

/-- Every finite nonempty index type has a separated fibre power with étale projections. -/
theorem exists_of_finite (ha : IsEtale a) [IsSeparated V.hom] (ι : Type v) [Finite ι]
    [Nonempty ι] : ∃ P : ChartFibrePower a ι, IsSeparated P.obj.hom ∧ ∀ i, Etale (P.pr i).left := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain _ | n := n
  · exact (IsEmpty.false (e (Classical.arbitrary ι))).elim
  obtain ⟨h₁, h₂⟩ := fin_properties ha n
  exact ⟨(fin ha.1 n).reindex e, h₁, fun i => h₂ (e i)⟩

section Action

variable {G : Type v} [Group G] (P : ChartFibrePower a G)

/-- Left multiplication on the factors: `act g ≫ pr e = pr (g * e)`. -/
def act (g : G) : P.obj ⟶ P.obj :=
  P.lift (fun e => P.pr (g * e)) fun _ _ => P.w _ _

@[reassoc (attr := simp)]
theorem act_pr (g e : G) : P.act g ≫ P.pr e = P.pr (g * e) :=
  P.lift_pr _ _ e

theorem act_one : P.act 1 = 𝟙 P.obj :=
  P.hom_ext _ _ fun e => by simp

theorem act_mul (g h : G) : P.act g ≫ P.act h = P.act (g * h) :=
  P.hom_ext _ _ fun e => by simp [mul_assoc]

end Action

end ChartFibrePower

end Langlands.AlgebraicGeometry.AlgebraicSpace
