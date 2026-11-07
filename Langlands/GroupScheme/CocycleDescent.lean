import Langlands.GroupScheme.CocycleRefinement

/-! # Descent of fibrewise trivial cocycles along fpqc refinements

A natural cocycle on a cover `V` whose values are trivial on pairs of points with the same
image in a coarser cover `W` is the refinement of a natural cocycle on `W`, provided the
refinement `V ⟶ W` is quasi-compact, flat and surjective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {V W : Over S}

/-- Quasi-compact, flat and surjective morphisms of schemes. -/
private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
/-- Products of fpqc refinements are fpqc. -/
private theorem fpqcProperty_tensorHom {V₁ W₁ V₂ W₂ : Over S} (r₁ : V₁ ⟶ W₁) (r₂ : V₂ ⟶ W₂)
    (h₁ : fpqcProperty r₁.left) (h₂ : fpqcProperty r₂.left) :
    fpqcProperty (r₁ ⊗ₘ r₂).left :=
  MorphismProperty.pullbackMap (P := fpqcProperty) h₁ h₂ (Over.w r₁).symm (Over.w r₂).symm

private theorem fpqcProperty_of_instances (r : V ⟶ W)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left] : fpqcProperty r.left :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem epi_of_fpqcProperty {X Y : Scheme.{u}} (f : X ⟶ Y) (h : fpqcProperty f) :
    Epi f := by
  let : QuasiCompact f := h.1
  let : Flat f := h.2.1
  let : Surjective f := h.2.2
  infer_instance

/-- A cocycle that is trivial on pairs with equal image in `W` depends only on those images. -/
theorem toFun_eq_of_comp_eq (ζ : Cocycle G V) (r : V ⟶ W)
    (hζ : ∀ {Z : Over S} (a b : Z ⟶ V), a ≫ r = b ≫ r → ζ.toFun a b = 1)
    {Z : Over S} {a a' b b' : Z ⟶ V} (ha : a ≫ r = a' ≫ r) (hb : b ≫ r = b' ≫ r) :
    ζ.toFun a b = ζ.toFun a' b' := by
  rw [ζ.cocycle a a' b, ζ.cocycle a' b' b, hζ a a' ha, hζ b' b hb.symm, one_mul, mul_one]

/-- A fibrewise trivial cocycle along an fpqc refinement `r : V ⟶ W` is the refinement of a
cocycle on `W`. -/
theorem exists_refine_eq_of_comp_eq (ζ : Cocycle G V) (r : V ⟶ W)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (hζ : ∀ {Z : Over S} (a b : Z ⟶ V), a ≫ r = b ≫ r → ζ.toFun a b = 1) :
    ∃ ν : Cocycle G W, ∀ {Z : Over S} (a b : Z ⟶ V), ν.toFun (a ≫ r) (b ≫ r) = ζ.toFun a b := by
  have hr := fpqcProperty_of_instances r
  have hrr := fpqcProperty_tensorHom r r hr hr
  have : EffectiveEpi (r ⊗ₘ r).left := by
    let : QuasiCompact (r ⊗ₘ r).left := hrr.1
    let : Flat (r ⊗ₘ r).left := hrr.2.1
    let : Surjective (r ⊗ₘ r).left := hrr.2.2
    infer_instance
  let ζ₀ : V ⊗ V ⟶ G.X := ζ.toFun (fst V V) (snd V V)
  have hval {Z : Over S} (x : Z ⟶ V ⊗ V) : x ≫ ζ₀ = ζ.toFun (x ≫ fst V V) (x ≫ snd V V) :=
    (ζ.naturality x _ _).symm
  let d : (W ⊗ W).left ⟶ G.X.left :=
    EffectiveEpi.desc (r ⊗ₘ r).left ζ₀.left (fun {Z} x y hxy => by
      have hy : y ≫ (V ⊗ V).hom = x ≫ (V ⊗ V).hom := by
        rw [← Over.w (r ⊗ₘ r), ← Category.assoc, ← Category.assoc, hxy]
      let x₀ : Over.mk (x ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk x rfl
      let y₀ : Over.mk (x ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk y hy
      have hxy₀ : x₀ ≫ (r ⊗ₘ r) = y₀ ≫ (r ⊗ₘ r) := Over.OverMorphism.ext hxy
      have h1 : (x₀ ≫ fst V V) ≫ r = (y₀ ≫ fst V V) ≫ r := by
        simpa only [Category.assoc, tensorHom_fst] using congrArg (· ≫ fst W W) hxy₀
      have h2 : (x₀ ≫ snd V V) ≫ r = (y₀ ≫ snd V V) ≫ r := by
        simpa only [Category.assoc, tensorHom_snd] using congrArg (· ≫ snd W W) hxy₀
      have h := toFun_eq_of_comp_eq ζ r hζ h1 h2
      rw [← hval, ← hval] at h
      exact congrArg (fun e => e.left) h)
  have hd : (r ⊗ₘ r).left ≫ d = ζ₀.left := EffectiveEpi.fac _ _ _
  let ν₀ : W ⊗ W ⟶ G.X := Over.homMk d (by
    apply (cancel_epi (r ⊗ₘ r).left).mp
    rw [← Category.assoc, hd, Over.w ζ₀, Over.w (r ⊗ₘ r)])
  have hν₀ : (r ⊗ₘ r) ≫ ν₀ = ζ₀ := Over.OverMorphism.ext hd
  have hcomp {Z : Over S} (a b : Z ⟶ V) :
      CartesianMonoidalCategory.lift (a ≫ r) (b ≫ r) ≫ ν₀ = ζ.toFun a b := by
    have hl : CartesianMonoidalCategory.lift (a ≫ r) (b ≫ r) =
        CartesianMonoidalCategory.lift a b ≫ (r ⊗ₘ r) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hl, Category.assoc, hν₀, hval, lift_fst, lift_snd]
  -- The universal triple of points of `W`.
  let T : Over S := (W ⊗ W) ⊗ W
  let π₁ : T ⟶ W := fst _ _ ≫ fst W W
  let π₂ : T ⟶ W := fst _ _ ≫ snd W W
  let π₃ : T ⟶ W := snd _ _
  have huniv : CartesianMonoidalCategory.lift π₁ π₃ ≫ ν₀ =
      (CartesianMonoidalCategory.lift π₁ π₂ ≫ ν₀) *
        (CartesianMonoidalCategory.lift π₂ π₃ ≫ ν₀) := by
    have hrrr := fpqcProperty_tensorHom (r ⊗ₘ r) r hrr hr
    have := epi_of_fpqcProperty _ hrrr
    apply Over.OverMorphism.ext
    apply (cancel_epi ((r ⊗ₘ r) ⊗ₘ r).left).mp
    refine congrArg (fun e => e.left) (?_ : ((r ⊗ₘ r) ⊗ₘ r) ≫ _ = ((r ⊗ₘ r) ⊗ₘ r) ≫ _)
    let ρ₁ : (V ⊗ V) ⊗ V ⟶ V := fst _ _ ≫ fst V V
    let ρ₂ : (V ⊗ V) ⊗ V ⟶ V := fst _ _ ≫ snd V V
    let ρ₃ : (V ⊗ V) ⊗ V ⟶ V := snd _ _
    have e₁ : ((r ⊗ₘ r) ⊗ₘ r) ≫ π₁ = ρ₁ ≫ r := by
      simp only [π₁, ρ₁, ← Category.assoc, tensorHom_fst]
      simp only [Category.assoc, tensorHom_fst]
    have e₂ : ((r ⊗ₘ r) ⊗ₘ r) ≫ π₂ = ρ₂ ≫ r := by
      simp only [π₂, ρ₂, ← Category.assoc, tensorHom_fst]
      simp only [Category.assoc, tensorHom_snd]
    have e₃ : ((r ⊗ₘ r) ⊗ₘ r) ≫ π₃ = ρ₃ ≫ r := by
      simp only [π₃, ρ₃, tensorHom_snd]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, comp_lift,
      comp_lift, comp_lift, e₁, e₂, e₃, hcomp, hcomp, hcomp]
    exact ζ.cocycle ρ₁ ρ₂ ρ₃
  refine ⟨{
    toFun := fun a b => CartesianMonoidalCategory.lift a b ≫ ν₀
    naturality := fun t a b => by rw [← Category.assoc, comp_lift]
    cocycle := fun {Z} a b c => by
      have h := congrArg
        (fun e => CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift a b) c ≫ e) huniv
      simp only [MonObj.comp_mul, ← Category.assoc, comp_lift, π₁, π₂, π₃,
        lift_fst, lift_snd] at h
      exact h }, ?_⟩
  intro Z a b
  exact hcomp a b

/-- A fibrewise trivial cocycle along an fpqc refinement `r : V ⟶ W` is trivial as soon as
every cocycle on `W` is trivial. -/
theorem isTrivial_of_comp_eq (ζ : Cocycle G V) (r : V ⟶ W)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (hζ : ∀ {Z : Over S} (a b : Z ⟶ V), a ≫ r = b ≫ r → ζ.toFun a b = 1)
    (hW : ∀ ν : Cocycle G W, ν.IsTrivial) : ζ.IsTrivial := by
  obtain ⟨ν, hν⟩ := exists_refine_eq_of_comp_eq ζ r hζ
  obtain ⟨f, hf⟩ := hW ν
  exact ⟨r ≫ f, fun a b => by rw [← hν, hf, Category.assoc, Category.assoc]⟩

end Langlands.GroupScheme.Cocycle
