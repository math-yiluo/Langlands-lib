import Langlands.AlgebraicGeometry.PolynomialSpecPoints
import Langlands.AlgebraicGeometry.ProductCoefficientInjectivity
import Langlands.AlgebraicGeometry.ClosedLiftingLocus
import Langlands.GroupScheme.AutomorphicAction.Cocycles

/-! # Cocycles whose sections have coordinates linear in a fixed family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction.SectionCoordinateModel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PolynomialSpecPoints

section Sections

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The morphism `(h, t) ↦ (d(t, h), h)` from `H × T` to `G × H`. -/
def secHom {T : Over S} (d : T ⊗ H.X ⟶ G.X) : H.X ⊗ T ⟶ G.X ⊗ H.X :=
  lift (lift (snd H.X T) (fst H.X T) ≫ d) (fst H.X T)

@[simp]
theorem secHom_snd {T : Over S} (d : T ⊗ H.X ⟶ G.X) :
    secHom d ≫ snd G.X H.X = fst H.X T :=
  lift_snd _ _

/-- The morphism `d` is recovered from `secHom d`. -/
theorem secHom_fst {T : Over S} (d : T ⊗ H.X ⟶ G.X) :
    lift (snd T H.X) (fst T H.X) ≫ secHom d ≫ fst G.X H.X = d := by
  simp only [secHom, lift_fst, ← Category.assoc, comp_lift, lift_fst, lift_snd]
  rw [show lift (fst T H.X) (snd T H.X) = 𝟙 _ from lift_fst_snd, Category.id_comp]

theorem secHom_injective {T : Over S} {d d' : T ⊗ H.X ⟶ G.X}
    (h : secHom d = secHom d') : d = d' := by
  rw [← secHom_fst d, h, secHom_fst]

/-- The section of `G × H → H` over `H × T` attached to a cocycle. -/
abbrev sec {a : AutomorphicAction H G} {T : Over S} (c : a.Cocycle T) :
    H.X ⊗ T ⟶ G.X ⊗ H.X :=
  secHom c.hom

/-- If `σ` is a section of `G × H → H` over `H × Z`, then the morphisms `secHom`
of the pulled back cocycle-shaped morphisms are the pullbacks of `σ`. -/
theorem secHom_whiskerRight {Z T : Over S} (σ : H.X ⊗ Z ⟶ G.X ⊗ H.X)
    (hσ : σ ≫ snd G.X H.X = fst H.X Z) (z : T ⟶ Z) :
    secHom ((z ▷ H.X) ≫ lift (snd Z H.X) (fst Z H.X) ≫ σ ≫ fst G.X H.X) =
      (H.X ◁ z) ≫ σ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [secHom, lift_fst, Category.assoc]
    simp only [← Category.assoc]
    congr 2
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · rw [secHom_snd, Category.assoc, hσ, whiskerLeft_fst]

end Sections

section Coordinates

variable {R : CommRingCat.{u}}

/-- The morphism `X × 𝔸^{C × m} → 𝔸^C`, `(x, y) ↦ (∑ₗ e_l(x) y_{κ,l})_κ`. -/
def Φ (X : Over (Spec R)) (C : Type) {m : ℕ} (e : Fin m → Γ(X.left, ⊤)) :
    X ⊗ space R (C × Fin m) ⟶ space R C :=
  PolynomialSpecPoints.mk fun κ => ∑ l, (fst X (space R (C × Fin m))).left.appTop (e l) *
    (snd X (space R (C × Fin m))).left.appTop (globalCoord R (C × Fin m) (κ, l))

theorem appTop_comp {T T' T'' : Over (Spec R)} (f : T ⟶ T') (g : T' ⟶ T'')
    (x : Γ(T''.left, ⊤)) : (f ≫ g).left.appTop x = f.left.appTop (g.left.appTop x) := by
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Coordinates of `Φ` after substituting a test point into the second factor. -/
theorem coord_whiskerLeft_Φ (X : Over (Spec R)) {C : Type} {m : ℕ}
    (e : Fin m → Γ(X.left, ⊤)) {T : Over (Spec R)} (y : T ⟶ space R (C × Fin m)) (κ : C) :
    coord ((X ◁ y) ≫ Φ X C e) κ =
      ∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (coord y (κ, l)) := by
  rw [coord_comp, Φ, coord_mk, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← appTop_comp, ← appTop_comp, whiskerLeft_fst, whiskerLeft_snd, appTop_comp]
  rfl

/-- A scheme with a closed immersion into a finite affine space is affine and of
finite type over the base. -/
theorem isAffineHom_of_isClosedImmersion {K : Type} {Z : Over (Spec R)} (i : Z ⟶ space R K)
    (hi : IsClosedImmersion i.left) : IsAffineHom Z.hom := by
  rw [← Over.w i]
  infer_instance

theorem locallyOfFiniteType_of_isClosedImmersion {K : Type} [Finite K] {Z : Over (Spec R)}
    (i : Z ⟶ space R K) (hi : IsClosedImmersion i.left) : LocallyOfFiniteType Z.hom := by
  rw [← Over.w i]
  infer_instance

end Coordinates

variable {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
  {a : AutomorphicAction H G}

set_option backward.isDefEq.respectTransparency.types false in
theorem isAffineHom_tensor (X Y : Over (Spec (CommRingCat.of k)))
    [IsAffineHom X.hom] [IsAffineHom Y.hom] : IsAffineHom (X ⊗ Y).hom := by
  change IsAffineHom (pullback.fst X.hom Y.hom ≫ X.hom)
  have hfst : IsAffineHom (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  infer_instance

/-- The multiplication law of a cocycle-shaped morphism along a test map. -/
def MulLaw {Z T : Over (Spec (CommRingCat.of k))} (c₀ : Z ⊗ H.X ⟶ G.X) (t : T ⟶ Z) : Prop :=
  ∀ (V : Over (Spec (CommRingCat.of k))) (b : V ⟶ T) (h h' : V ⟶ H.X),
    lift (b ≫ t) (h * h') ≫ c₀ = (lift (b ≫ t) h ≫ c₀) * a.act h (lift (b ≫ t) h' ≫ c₀)

/-- The test maps along which a cocycle-shaped morphism satisfies the
multiplication law are those through one closed subscheme. -/
theorem exists_mulLaw_locus [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    {Z : Over (Spec (CommRingCat.of k))} (c₀ : Z ⊗ H.X ⟶ G.X) :
    ∃ (Z₁ : Over (Spec (CommRingCat.of k))) (i : Z₁ ⟶ Z), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ Z),
        (∃ z : T ⟶ Z₁, z ≫ i = t) ↔ MulLaw (a := a) c₀ t := by
  have : IsAffineHom (H.X ⊗ H.X).hom := isAffineHom_tensor _ _
  have : IsSeparated G.X.hom := IsSeparated.of_isAffineHom G.X.hom
  let p₁ : (H.X ⊗ H.X) ⊗ Z ⟶ H.X := fst (H.X ⊗ H.X) Z ≫ fst H.X H.X
  let p₂ : (H.X ⊗ H.X) ⊗ Z ⟶ H.X := fst (H.X ⊗ H.X) Z ≫ snd H.X H.X
  let f₁ : (H.X ⊗ H.X) ⊗ Z ⟶ G.X := lift (snd (H.X ⊗ H.X) Z) (p₁ * p₂) ≫ c₀
  let f₂ : (H.X ⊗ H.X) ⊗ Z ⟶ G.X :=
    (lift (snd (H.X ⊗ H.X) Z) p₁ ≫ c₀) * a.act p₁ (lift (snd (H.X ⊗ H.X) Z) p₂ ≫ c₀)
  obtain ⟨Z₁, i, hi, hZ₁⟩ := ClosedLiftingLocus.exists_equalizer_locus (H.X ⊗ H.X) Z G.X f₁ f₂
  refine ⟨Z₁, i, hi, fun T t => (hZ₁ T t).trans ?_⟩
  have e₁ : ∀ (V : Over (Spec (CommRingCat.of k))) (b : V ⟶ T) (h h' : V ⟶ H.X),
      lift (lift h h') b ≫ ((H.X ⊗ H.X) ◁ t) ≫ f₁ = lift (b ≫ t) (h * h') ≫ c₀ := by
    intro V b h h'
    simp only [f₁, p₁, p₂, ← Category.assoc, lift_whiskerLeft, comp_lift, MonObj.comp_mul,
      lift_fst, lift_snd]
  have e₂ : ∀ (V : Over (Spec (CommRingCat.of k))) (b : V ⟶ T) (h h' : V ⟶ H.X),
      lift (lift h h') b ≫ ((H.X ⊗ H.X) ◁ t) ≫ f₂ =
        (lift (b ≫ t) h ≫ c₀) * a.act h (lift (b ≫ t) h' ≫ c₀) := by
    intro V b h h'
    simp only [f₂, p₁, p₂, ← Category.assoc, lift_whiskerLeft, MonObj.comp_mul, a.naturality,
      comp_lift, lift_fst, lift_snd]
  constructor
  · intro h V b h₁ h₂
    rw [← e₁, ← e₂, h]
  · intro h
    have hid : lift (lift (fst (H.X ⊗ H.X) T ≫ fst H.X H.X) (fst (H.X ⊗ H.X) T ≫ snd H.X H.X)) (snd (H.X ⊗ H.X) T) =
        𝟙 ((H.X ⊗ H.X) ⊗ T) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, Category.id_comp]
        rw [← comp_lift, lift_fst_snd, Category.comp_id]
      · simp
    calc ((H.X ⊗ H.X) ◁ t) ≫ f₁ = lift (lift (fst (H.X ⊗ H.X) T ≫ fst H.X H.X) (fst (H.X ⊗ H.X) T ≫ snd H.X H.X))
            (snd (H.X ⊗ H.X) T) ≫ ((H.X ⊗ H.X) ◁ t) ≫ f₁ := by rw [hid, Category.id_comp]
      _ = _ := e₁ _ _ _ _
      _ = _ := h _ _ _ _
      _ = lift (lift (fst (H.X ⊗ H.X) T ≫ fst H.X H.X) (fst (H.X ⊗ H.X) T ≫ snd H.X H.X))
            (snd (H.X ⊗ H.X) T) ≫ ((H.X ⊗ H.X) ◁ t) ≫ f₂ := (e₂ _ _ _ _).symm
      _ = ((H.X ⊗ H.X) ◁ t) ≫ f₂ := by rw [hid, Category.id_comp]

/-- Over a field, for a closed immersion `j : G × H ⟶ H × 𝔸^C` over `H` and a family
`e` of global functions on `H`, the cocycles whose sections become, after `j`, linear
in `e` with coefficients from the test scheme are represented by a closed subscheme
`Z` of `𝔸^{C × m}`: a point `y` together with a cocycle `c` comes from `Z` exactly when
the section of `c` is `y` read through `e`. When `e` is linearly independent, a point
of `Z` is determined by its cocycle. -/
theorem exists_model [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] (C : Type) (m : ℕ)
    (j : G.X ⊗ H.X ⟶ H.X ⊗ space (CommRingCat.of k) C) (hj : IsClosedImmersion j.left)
    (hjf : j ≫ fst _ _ = snd G.X H.X) (e : Fin m → Γ(H.X.left, ⊤))
    (he : letI := Scheme.TwoAffineOpenCover.algebraOfHom H.X.hom ⊤; LinearIndependent k e) :
    ∃ (Z : Over (Spec (CommRingCat.of k))) (i : Z ⟶ space (CommRingCat.of k) (C × Fin m))
      (U : a.Cocycle Z), IsClosedImmersion i.left ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ space (CommRingCat.of k) (C × Fin m))
          (c : a.Cocycle T),
        (∃ x : T ⟶ Z, x ≫ i = y ∧ Cocycle.restrict x U = c) ↔
          (H.X ◁ y) ≫ lift (fst _ _) (Φ H.X C e) = sec c ≫ j) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))),
        Function.Injective (fun x : T ⟶ Z => Cocycle.restrict x U) := by
  -- The closed locus where the transported section lifts through `j`.
  obtain ⟨Z₀, i₀, hi₀, hZ₀⟩ :=
    ClosedLiftingLocus.exists_lifting_locus H.X (space (CommRingCat.of k) (C × Fin m))
      (G.X ⊗ H.X) (H.X ⊗ space (CommRingCat.of k) C) j hj (lift (fst _ _) (Φ H.X C e))
  obtain ⟨σ₀, hσ₀⟩ := (hZ₀ Z₀ i₀).mp ⟨𝟙 _, Category.id_comp _⟩
  have hσ₀snd : σ₀ ≫ snd G.X H.X = fst H.X Z₀ := by
    rw [← hjf, ← Category.assoc, hσ₀, Category.assoc, lift_fst, whiskerLeft_fst]
  let c₀ : Z₀ ⊗ H.X ⟶ G.X := lift (snd Z₀ H.X) (fst Z₀ H.X) ≫ σ₀ ≫ fst G.X H.X
  have hsec : ∀ {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ Z₀),
      secHom ((z ▷ H.X) ≫ c₀) = (H.X ◁ z) ≫ σ₀ :=
    fun z => secHom_whiskerRight σ₀ hσ₀snd z
  -- The closed locus where the resulting morphism satisfies the cocycle law.
  obtain ⟨Z, i₁, hi₁, hZ⟩ := exists_mulLaw_locus (a := a) c₀
  have hmul : MulLaw (a := a) c₀ i₁ := (hZ Z i₁).mp ⟨𝟙 _, Category.id_comp _⟩
  let U : a.Cocycle Z :=
    { hom := (i₁ ▷ H.X) ≫ c₀
      one := fun {V} b => by
        rw [lift_whiskerRight_assoc]
        have h1 := hmul V b 1 1
        rw [mul_one, a.act_one_left] at h1
        exact mul_eq_left.mp h1.symm
      mul := fun {V} b h h' => by
        simp only [lift_whiskerRight_assoc]
        exact hmul V b h h' }
  have hj' : Mono j := by
    have := hj
    exact Over.mono_of_mono_left j
  have hi : IsClosedImmersion (i₁ ≫ i₀).left := by
    have := hi₀
    have := hi₁
    change IsClosedImmersion (i₁.left ≫ i₀.left)
    infer_instance
  have hreal : ∀ (T : Over (Spec (CommRingCat.of k)))
      (y : T ⟶ space (CommRingCat.of k) (C × Fin m)) (c : a.Cocycle T),
      (∃ x : T ⟶ Z, x ≫ i₁ ≫ i₀ = y ∧ Cocycle.restrict x U = c) ↔
        (H.X ◁ y) ≫ lift (fst _ _) (Φ H.X C e) = sec c ≫ j := by
    intro T y c
    constructor
    · rintro ⟨x, rfl, rfl⟩
      change (H.X ◁ (x ≫ i₁ ≫ i₀)) ≫ lift (fst _ _) (Φ H.X C e) =
        secHom ((x ▷ H.X) ≫ (i₁ ▷ H.X) ≫ c₀) ≫ j
      rw [← Category.assoc (x ▷ H.X), ← comp_whiskerRight, hsec, Category.assoc, hσ₀]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    · intro h
      obtain ⟨z₀, hz₀⟩ := (hZ₀ T y).mpr ⟨sec c, h.symm⟩
      have hσ : (H.X ◁ z₀) ≫ σ₀ = sec c := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hσ₀, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hz₀, h]
      have hc : (z₀ ▷ H.X) ≫ c₀ = c.hom := secHom_injective ((hsec z₀).trans hσ)
      have hz : MulLaw (a := a) c₀ z₀ := by
        intro V b h₁ h₂
        have := c.mul b h₁ h₂
        rw [← hc] at this
        simpa only [lift_whiskerRight_assoc] using this
      obtain ⟨x, hx⟩ := (hZ T z₀).mpr hz
      refine ⟨x, by rw [← Category.assoc, hx, hz₀], ?_⟩
      apply Cocycle.ext
      change (x ▷ H.X) ≫ (i₁ ▷ H.X) ≫ c₀ = c.hom
      rw [← Category.assoc, ← comp_whiskerRight, hx, hc]
  refine ⟨Z, i₁ ≫ i₀, U, hi, hreal, fun T x x' hxx => ?_⟩
  have h₁ := (hreal T (x ≫ i₁ ≫ i₀) _).mp ⟨x, rfl, rfl⟩
  have h₂ := (hreal T (x' ≫ i₁ ≫ i₀) (Cocycle.restrict x U)).mp ⟨x', rfl, hxx.symm⟩
  have h₃ : (H.X ◁ (x ≫ i₁ ≫ i₀)) ≫ Φ H.X C e = (H.X ◁ (x' ≫ i₁ ≫ i₀)) ≫ Φ H.X C e := by
    have := congrArg (· ≫ snd H.X (space (CommRingCat.of k) C)) (h₁.trans h₂.symm)
    simpa only [Category.assoc, lift_snd] using this
  have hy : x ≫ i₁ ≫ i₀ = x' ≫ i₁ ≫ i₀ := by
    apply PolynomialSpecPoints.ext
    rintro ⟨κ, l⟩
    have hk := congrArg (fun w => coord w κ) h₃
    simp only [coord_whiskerLeft_Φ] at hk
    exact congrFun (ProductCoefficients.coefficients_injective H.X T e he
      (y := fun l => coord (x ≫ i₁ ≫ i₀) (κ, l)) (y' := fun l => coord (x' ≫ i₁ ≫ i₀) (κ, l))
      hk) l
  have : Mono (i₁ ≫ i₀) := by
    have := hi
    exact Over.mono_of_mono_left _
  exact (cancel_mono (i₁ ≫ i₀)).mp hy

end Langlands.GroupScheme.AutomorphicAction.SectionCoordinateModel
