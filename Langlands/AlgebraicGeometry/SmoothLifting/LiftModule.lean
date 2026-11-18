import Langlands.AlgebraicGeometry.SmoothLifting.GlobalComb

/-! # The module of lifts along a square-zero thickening with a chosen base lift

For a square-zero ideal `I` of `C` and a chosen lift `e : Spec C ⟶ X` of `x₀` over `s`, the set
of all such lifts is a `C`-module with zero `e`: `x + y = e + (x - e) + (y - e)` and
`c • x = e + c (x - e)`, computed by global affine combinations. Morphisms over `S` are
additive and `C`-linear for the induced base lifts.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

variable (f I x₀ s) in
/-- Global lifts of `x₀` over `s`. -/
def GLift : Type u := {y : Spec C ⟶ X // IsGlobalLift f I x₀ s y}

/-- Chart representative of the restriction of a global lift. -/
abbrev Chart.grep (hI : SqZero I) (ch : Chart f I x₀ s) (R : Type u) [CommRing R] [Algebra C R]
    (hg : IsUnit (algebraMap C R ch.g)) {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y)
    (b : Γ(X, ch.U)) : R :=
  (ch.rep R hI hg (restrC R y) (hy.isLift R)).hom b

theorem Chart.grep_gcomb {ι : Type} [Fintype ι] (hI : SqZero I) (ch : Chart f I x₀ s)
    (R : Type u) [CommRing R] [Algebra C R] (hg : IsUnit (algebraMap C R ch.g))
    {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) (b : Γ(X, ch.U)) :
    ch.grep hI R hg (gcomb_isGlobalLift hI hy₀ hy c) b =
      ch.grep hI R hg hy₀ b + ∑ k, algebraMap C R (c k) * (ch.grep hI R hg (hy k) b -
        ch.grep hI R hg hy₀ b) := by
  rw [Chart.grep, ch.rep_congr hI hg _ (ch.comb_isLift R hI hg _ _ _ _ _)
    (gcomb_restr hI hy₀ hy c ch R hg) b, ch.rep_comb_apply hI hg _ _ _ _ _ _ b]

theorem IsGlobalLift.ext_grep (hI : SqZero I) {n : ℕ} (chs : Fin n → Chart f I x₀ s)
    (hspan : Ideal.span (Set.range fun i => (chs i).g) = ⊤) {z z' : Spec C ⟶ X}
    (hz : IsGlobalLift f I x₀ s z) (hz' : IsGlobalLift f I x₀ s z')
    (h : ∀ i b, (chs i).grep hI (Loc (chs i).g) (isUnit_loc _) hz b =
      (chs i).grep hI (Loc (chs i).g) (isUnit_loc _) hz' b) : z = z' :=
  IsGlobalLift.ext_of_charts chs hspan fun i =>
    (chs i).eq_of_rep hI (isUnit_loc _) (hz.isLift _) (hz'.isLift _) (h i)

/-- The type of global lifts with the module structure based at `e`. -/
def LiftModule (_hI : SqZero I) (_e : GLift f I x₀ s) : Type u := GLift f I x₀ s

namespace LiftModule

variable (hI : SqZero I) (e : GLift f I x₀ s)

/-- A global lift as an element of the module based at `e`. -/
def of (x : GLift f I x₀ s) : LiftModule hI e := x

@[simp] theorem of_val (x : GLift f I x₀ s) : (of hI e x : GLift f I x₀ s) = x := rfl

/-- A covering family of charts chosen once for the base point. -/
def charts : Σ n : ℕ, {chs : Fin n → Chart f I x₀ s //
    Ideal.span (Set.range fun i => (chs i).g) = ⊤} :=
  ⟨(exists_charts hI e.2.h₀).choose, (exists_charts hI e.2.h₀).choose_spec.choose,
    (exists_charts hI e.2.h₀).choose_spec.choose_spec⟩

/-- The two-term combination `e + a (x - e) + b (y - e)`. -/
def lin (x y : GLift f I x₀ s) (a b : C) : GLift f I x₀ s :=
  ⟨gcomb hI e.2 (y := ![x.1, y.1]) (fun k => by fin_cases k; exacts [x.2, y.2]) ![a, b],
    gcomb_isGlobalLift _ _ _ _⟩

theorem grep_lin (ch : Chart f I x₀ s) (R : Type u) [CommRing R] [Algebra C R]
    (hg : IsUnit (algebraMap C R ch.g)) (x y : GLift f I x₀ s) (a b : C) (z : Γ(X, ch.U)) :
    ch.grep hI R hg (lin hI e x y a b).2 z = ch.grep hI R hg e.2 z +
      algebraMap C R a * (ch.grep hI R hg x.2 z - ch.grep hI R hg e.2 z) +
      algebraMap C R b * (ch.grep hI R hg y.2 z - ch.grep hI R hg e.2 z) := by
  rw [lin, ch.grep_gcomb hI R hg e.2 _ ![a, b] z, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem lin_self (a b : C) : lin hI e e e a b = e := by
  refine Subtype.ext (IsGlobalLift.ext_grep hI _ (charts hI e).2.2 (lin hI e e e a b).2 e.2
    fun i z => ?_)
  rw [grep_lin]
  ring

/-- The coordinate map: differences of chart representatives from the base point. -/
def coord (x : GLift f I x₀ s) :
    ∀ i : Fin (charts hI e).1, Γ(X, ((charts hI e).2.1 i).U) → Loc ((charts hI e).2.1 i).g :=
  fun i z => ((charts hI e).2.1 i).grep hI _ (isUnit_loc _) x.2 z -
    ((charts hI e).2.1 i).grep hI _ (isUnit_loc _) e.2 z

theorem coord_injective : Function.Injective (coord hI e) := by
  intro x y h
  refine Subtype.ext (IsGlobalLift.ext_grep hI _ (charts hI e).2.2 x.2 y.2 fun i z => ?_)
  have := congrFun (congrFun h i) z
  simp only [coord] at this
  exact sub_left_injective this

theorem coord_lin (x y : GLift f I x₀ s) (a b : C) :
    coord hI e (lin hI e x y a b) = a • coord hI e x + b • coord hI e y := by
  funext i z
  show coord hI e (lin hI e x y a b) i z = a • coord hI e x i z + b • coord hI e y i z
  simp only [coord, grep_lin, Algebra.smul_def]
  ring

instance : Zero (LiftModule hI e) := ⟨e⟩
instance : Add (LiftModule hI e) := ⟨fun x y => lin hI e x y 1 1⟩
instance : Neg (LiftModule hI e) := ⟨fun x => lin hI e x e (-1) 0⟩
instance : Sub (LiftModule hI e) := ⟨fun x y => lin hI e x y 1 (-1)⟩
instance : SMul C (LiftModule hI e) := ⟨fun c x => lin hI e x e c 0⟩
instance : SMul ℕ (LiftModule hI e) := ⟨fun n x => lin hI e x e (n : C) 0⟩
instance : SMul ℤ (LiftModule hI e) := ⟨fun n x => lin hI e x e (n : C) 0⟩

/-- The coordinate map as a function on the module type. -/
def coord' (x : LiftModule hI e) := coord hI e x

theorem coord'_zero : coord' hI e 0 = 0 := by
  funext i z
  simp [coord', coord, show (0 : LiftModule hI e) = e from rfl]

theorem coord'_add (x y : LiftModule hI e) : coord' hI e (x + y) = coord' hI e x + coord' hI e y := by
  refine (coord_lin hI e x y 1 1).trans ?_
  rw [one_smul, one_smul]
  rfl

theorem coord'_smul (c : C) (x : LiftModule hI e) :
    coord' hI e (c • x) = c • coord' hI e x := by
  refine (coord_lin hI e x e c 0).trans ?_
  have : coord hI e e = 0 := coord'_zero hI e
  rw [this, smul_zero, add_zero]
  rfl

theorem coord'_neg (x : LiftModule hI e) : coord' hI e (-x) = -coord' hI e x := by
  refine (coord_lin hI e x e (-1) 0).trans ?_
  rw [show coord hI e e = 0 from coord'_zero hI e]
  simp only [neg_smul, one_smul, smul_zero, add_zero]
  rfl

theorem coord'_sub (x y : LiftModule hI e) :
    coord' hI e (x - y) = coord' hI e x - coord' hI e y := by
  refine (coord_lin hI e x y 1 (-1)).trans ?_
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  rfl

theorem coord'_nsmul (x : LiftModule hI e) (n : ℕ) :
    coord' hI e (n • x) = n • coord' hI e x := by
  refine (coord_lin hI e x e (n : C) 0).trans ?_
  rw [show coord hI e e = 0 from coord'_zero hI e, smul_zero, add_zero, Nat.cast_smul_eq_nsmul]
  rfl

theorem coord'_zsmul (x : LiftModule hI e) (n : ℤ) :
    coord' hI e (n • x) = n • coord' hI e x := by
  refine (coord_lin hI e x e (n : C) 0).trans ?_
  rw [show coord hI e e = 0 from coord'_zero hI e, smul_zero, add_zero, Int.cast_smul_eq_zsmul]
  rfl

instance : AddCommGroup (LiftModule hI e) :=
  Function.Injective.addCommGroup (coord' hI e) (coord_injective hI e) (coord'_zero hI e)
    (coord'_add hI e) (coord'_neg hI e) (coord'_sub hI e) (coord'_nsmul hI e) (coord'_zsmul hI e)

/-- The coordinate map as an additive homomorphism. -/
def coordHom : LiftModule hI e →+ (∀ i : Fin (charts hI e).1,
    Γ(X, ((charts hI e).2.1 i).U) → Loc ((charts hI e).2.1 i).g) where
  toFun := coord' hI e
  map_zero' := coord'_zero hI e
  map_add' := coord'_add hI e

instance instModuleLift : Module C (LiftModule hI e) :=
  Function.Injective.module C (coordHom hI e) (coord_injective hI e) fun c x => by
    change coord' hI e (c • x) = c • coord' hI e x
    exact coord'_smul hI e c x

theorem coord_mem (x : GLift f I x₀ s) (i : Fin (charts hI e).1)
    (z : Γ(X, ((charts hI e).2.1 i).U)) :
    coord hI e x i z ∈ redIdeal I (Loc ((charts hI e).2.1 i).g) :=
  ((charts hI e).2.1 i).rep_sub_mem _ hI (isUnit_loc _) _ _ (e.2.isLift _) (x.2.isLift _) z

/-- Elements of the square-zero ideal act trivially on lifts. -/
theorem smul_eq_zero_of_mem {c : C} (hc : c ∈ I) (x : LiftModule hI e) : c • x = 0 := by
  apply coord_injective hI e
  change coord' hI e (c • x) = coord' hI e 0
  rw [coord'_smul, coord'_zero]
  funext i z
  change c • coord hI e x i z = 0
  rw [Algebra.smul_def]
  exact (hI.map _) _ (Ideal.mem_map_of_mem _ hc) _ (coord_mem hI e x i z)

end LiftModule

theorem gcomb_congr {ι : Type} [Fintype ι] (hI : SqZero I) {y₀ y₀' : Spec C ⟶ X}
    (hy₀ : IsGlobalLift f I x₀ s y₀) (hy₀' : IsGlobalLift f I x₀ s y₀') (e₀ : y₀ = y₀')
    {y y' : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k))
    (hy' : ∀ k, IsGlobalLift f I x₀ s (y' k)) (e : y = y') (c : ι → C) :
    gcomb hI hy₀ hy c = gcomb hI hy₀' hy' c := by
  subst e₀ e
  rfl

section Map

variable {Y : Scheme.{u}} {fY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ fY = f)
  {x₀Y : Spec (CommRingCat.of (C ⧸ I)) ⟶ Y} (hx : x₀ ≫ φ = x₀Y)
include hφ hx

theorem IsGlobalLift.map {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) :
    IsGlobalLift fY I x₀Y s (y ≫ φ) := by
  subst hx; exact hy.comp φ hφ

/-- A morphism over `S` sends global lifts to global lifts. -/
def GLift.map (y : GLift f I x₀ s) : GLift fY I x₀Y s := ⟨y.1 ≫ φ, y.2.map φ hφ hx⟩

theorem gcomb_map {ι : Type} [Fintype ι] (hI : SqZero I) {y₀ : Spec C ⟶ X}
    (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    gcomb hI hy₀ hy c ≫ φ = gcomb hI (hy₀.map φ hφ hx) (fun k => (hy k).map φ hφ hx) c := by
  subst hx
  exact gcomb_comp φ hφ hI hy₀ hy c

theorem LiftModule.lin_map (hI : SqZero I) (e : GLift f I x₀ s) (eY : GLift fY I x₀Y s)
    (he : e.1 ≫ φ = eY.1) (u v : GLift f I x₀ s) (a b : C) :
    (LiftModule.lin hI e u v a b).1 ≫ φ =
      (LiftModule.lin hI eY (u.map φ hφ hx) (v.map φ hφ hx) a b).1 := by
  change gcomb _ _ _ _ ≫ φ = gcomb _ _ _ _
  rw [gcomb_map φ hφ hx]
  refine gcomb_congr hI _ _ he _ _ ?_ _
  funext k
  fin_cases k <;> rfl

end Map

section MapLinear

variable {Y : Scheme.{u}} {fY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ fY = f)
  {x₀Y : Spec (CommRingCat.of (C ⧸ I)) ⟶ Y} (hx : x₀ ≫ φ = x₀Y)

/-- Composition with a morphism over `S` is `C`-linear on modules of lifts. -/
def LiftModule.map (hI : SqZero I) (e : GLift f I x₀ s) (eY : GLift fY I x₀Y s)
    (he : e.1 ≫ φ = eY.1) : LiftModule hI e →ₗ[C] LiftModule hI eY where
  toFun x := LiftModule.of hI eY (GLift.map φ hφ hx x)
  map_add' x y := by
    apply Subtype.ext
    exact LiftModule.lin_map φ hφ hx hI e eY he x y 1 1
  map_smul' c x := by
    apply Subtype.ext
    refine (LiftModule.lin_map φ hφ hx hI e eY he x e c 0).trans ?_
    have : GLift.map φ hφ hx e = eY := Subtype.ext he
    change (LiftModule.lin hI eY _ (GLift.map φ hφ hx e) c 0).1 = (LiftModule.lin hI eY _ eY c 0).1
    rw [this]
    rfl

@[simp] theorem LiftModule.map_val (hI : SqZero I) (e : GLift f I x₀ s) (eY : GLift fY I x₀Y s)
    (he : e.1 ≫ φ = eY.1) (x : LiftModule hI e) :
    (LiftModule.map φ hφ hx hI e eY he x : GLift fY I x₀Y s).1 = (x : GLift f I x₀ s).1 ≫ φ :=
  rfl

end MapLinear

end Langlands.AlgebraicGeometry.SmoothLifting
