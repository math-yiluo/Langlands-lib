import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Diagonals of presheaves through represented equalizer loci

The pullback of the diagonal of a presheaf `F` along a pair of points `x y : F(U)` is the
locus of `U` where `x` and `y` agree. This file shows that the diagonal is representable,
with projections in a morphism property `P`, as soon as every such locus is represented
by a monomorphism in `P`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The pullback of the diagonal along `prod.lift f g` is a limit fork of `f` and `g`. -/
theorem isPullback_diag_of_isLimit_fork {C : Type*} [Category C] {X Y : C}
    [HasBinaryProduct Y Y] {f g : X ⟶ Y} {c : Fork f g} (hc : IsLimit c) :
    IsPullback (c.ι ≫ f) c.ι (diag Y) (prod.lift f g) := by
  refine IsPullback.flip ⟨⟨by ext <;> simp [c.condition]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · refine fun s ↦ Fork.IsLimit.lift hc s.fst ?_
    have H₁ : s.fst ≫ f = s.snd := by simpa using congr($s.condition ≫ prod.fst)
    have H₂ : s.fst ≫ g = s.snd := by simpa using congr($s.condition ≫ prod.snd)
    exact H₁.trans H₂.symm
  · exact fun s ↦ by simp
  · exact fun s ↦ by simpa using congr($s.condition ≫ prod.fst)
  · exact fun s m hm _ ↦ Fork.IsLimit.hom_ext hc (by simpa using hm)

variable {S : Scheme.{u}} {F : Presheaf S}

/-- The morphism `ι : Z ⟶ U` cuts out the locus where `x y : F(U)` agree, in the
factorization sense: a morphism `g : T ⟶ U` factors through `ι` exactly when the
restrictions of `x` and `y` along `g` are equal. Lifts need not be unique; `ι` represents
the equalizer subfunctor only when it is moreover a monomorphism. -/
def RepresentsEqualizer {U Z : Over S} (ι : Z ⟶ U) (x y : F.obj (op U)) : Prop :=
  ∀ ⦃T : Over S⦄ (g : T ⟶ U), (∃ z : T ⟶ Z, z ≫ ι = g) ↔ F.map g.op x = F.map g.op y

/-- A natural transformation out of a represented presheaf evaluates through restriction. -/
theorem schemeYoneda_app_up {U T : Over S} (α : (schemeYoneda S).obj U ⟶ F) (g : T ⟶ U) :
    α.app (op T) (ULift.up g) = F.map g.op (uliftYonedaEquiv α) := by
  rw [uliftYonedaEquiv_naturality]
  simp [uliftYonedaEquiv]

/-- A monomorphism representing an equalizer locus gives a limit fork of represented
presheaves. -/
def RepresentsEqualizer.isLimitFork {U Z : Over S} {ι : Z ⟶ U}
    (α β : (schemeYoneda S).obj U ⟶ F) [Mono ι]
    (hι : RepresentsEqualizer ι (uliftYonedaEquiv α) (uliftYonedaEquiv β))
    (w : (schemeYoneda S).map ι ≫ α = (schemeYoneda S).map ι ≫ β) :
    IsLimit (Fork.ofι ((schemeYoneda S).map ι) w) := by
  refine evaluationJointlyReflectsLimits _ fun T ↦ ?_
  refine (isLimitMapConeForkEquiv ((evaluation _ _).obj T) w).symm ?_
  obtain ⟨T⟩ := T
  refine Types.typeEqualizerOfUnique _ _ fun y hy ↦ ?_
  obtain ⟨g⟩ := y
  have hy' : F.map g.op (uliftYonedaEquiv α) = F.map g.op (uliftYonedaEquiv β) := by
    have := hy
    simp only [evaluation_obj_map] at this
    rwa [schemeYoneda_app_up, schemeYoneda_app_up] at this
  obtain ⟨z, hz⟩ := (hι g).2 hy'
  refine ⟨ULift.up z, by simp [hz], ?_⟩
  rintro ⟨z'⟩ hz'
  have : z' ≫ ι = g := congrArg ULift.down hz'
  exact congrArg ULift.up ((cancel_mono ι).1 (this.trans hz.symm))

/-- If every equalizer locus of two points of `F` over a scheme is represented by a
monomorphism whose underlying scheme morphism has `P`, then the diagonal of `F` is
representable with all represented projections in `P`. -/
theorem relative_diag_of_representsEqualizer (P : MorphismProperty Scheme.{u})
    [P.RespectsIso]
    (h : ∀ ⦃U : Over S⦄ (x y : F.obj (op U)), ∃ (Z : Over S) (ι : Z ⟶ U),
      Mono ι.left ∧ RepresentsEqualizer ι x y ∧ P ι.left) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (diag F) := by
  let := MorphismProperty.RespectsIso.inverseImage P (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro U g
  obtain ⟨Z, ι, hmono, hι, hP⟩ :=
    h (uliftYonedaEquiv (g ≫ prod.fst)) (uliftYonedaEquiv (g ≫ prod.snd))
  have : Mono ι := (Over.forget S).mono_of_mono_map hmono
  have w : (schemeYoneda S).map ι ≫ g ≫ prod.fst =
      (schemeYoneda S).map ι ≫ g ≫ prod.snd := by
    apply uliftYonedaEquiv.injective
    have e₁ := uliftYonedaEquiv_naturality (g ≫ prod.fst) ι.op
    have e₂ := uliftYonedaEquiv_naturality (g ≫ prod.snd) ι.op
    simp only [Quiver.Hom.unop_op] at e₁ e₂
    rw [← e₁, ← e₂]
    exact (hι ι).1 ⟨𝟙 _, by simp⟩
  have hc := RepresentsEqualizer.isLimitFork _ _ hι w
  refine ⟨Z, (schemeYoneda S).map ι ≫ g ≫ prod.fst, ι, ?_, hP⟩
  have := isPullback_diag_of_isLimit_fork hc
  have hg : prod.lift (g ≫ prod.fst) (g ≫ prod.snd) = g := by ext <;> simp
  simpa [hg] using this

/-- Conversely, if the diagonal of `F` is representable with projections in `P`, then
every equalizer locus of two points of `F` over a scheme is cut out, in the sense of
`RepresentsEqualizer`, by a morphism in `P`. -/
theorem exists_representsEqualizer_of_relative_diag {P : MorphismProperty Scheme.{u}}
    (hF : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (diag F)) {U : Over S} (x y : F.obj (op U)) :
    ∃ (Z : Over S) (ι : Z ⟶ U), RepresentsEqualizer ι x y ∧ P ι.left := by
  let g : (schemeYoneda S).obj U ⟶ F ⨯ F :=
    prod.lift (uliftYonedaEquiv.symm x) (uliftYonedaEquiv.symm y)
  have hsq := hF.rep.isPullback g
  refine ⟨hF.rep.pullback g, hF.rep.snd g, fun T h ↦ ⟨?_, fun hxy ↦ ?_⟩,
    hF.property_snd g⟩
  · rintro ⟨z, rfl⟩
    have e₁ := congr($(hsq.w) ≫ prod.fst)
    have e₂ := congr($(hsq.w) ≫ prod.snd)
    simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id,
      g] at e₁ e₂
    have e := congrArg (fun α ↦ ((schemeYoneda S).map z ≫ α).app (op T)
      (ULift.up (𝟙 T))) (e₁.symm.trans e₂)
    simpa [schemeYoneda_app_up, uliftYonedaEquiv_apply] using e
  · let a : (schemeYoneda S).obj T ⟶ F := uliftYonedaEquiv.symm (F.map h.op x)
    have w : a ≫ diag F = (schemeYoneda S).map h ≫ g := by
      ext : 1
      · simpa [a, g] using uliftYonedaEquiv_symm_map h.op x
      · simpa [a, g, hxy] using uliftYonedaEquiv_symm_map h.op y
    obtain ⟨z, hz⟩ := (schemeYoneda S).map_surjective (hsq.lift a ((schemeYoneda S).map h) w)
    refine ⟨z, (schemeYoneda S).map_injective ?_⟩
    rw [Functor.map_comp, hz, hsq.lift_snd]

/-- The diagonal is representable once every equalizer locus is represented by a
monomorphism. -/
theorem hasRepresentableDiagonal_of_representsEqualizer
    (h : ∀ ⦃U : Over S⦄ (x y : F.obj (op U)), ∃ (Z : Over S) (ι : Z ⟶ U),
      Mono ι.left ∧ RepresentsEqualizer ι x y) :
    HasRepresentableDiagonal F :=
  (relative_diag_of_representsEqualizer (MorphismProperty.monomorphisms Scheme.{u})
    fun _ x y ↦ (h x y).imp fun _ ⟨ι, hι, hE⟩ ↦ ⟨ι, hι, hE, hι⟩).rep

/-- The diagonal is representable by immersions once every equalizer locus is
represented by an immersion. -/
theorem relative_isImmersion_diag_of_representsEqualizer
    (h : ∀ ⦃U : Over S⦄ (x y : F.obj (op U)), ∃ (Z : Over S) (ι : Z ⟶ U),
      RepresentsEqualizer ι x y ∧ IsImmersion ι.left) :
    (MorphismProperty.inverseImage @IsImmersion.{u} (Over.forget S)).relative
      (schemeYoneda S) (diag F) :=
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    IsImmersion.isStableUnderBaseChange.respectsIso
  relative_diag_of_representsEqualizer @IsImmersion.{u}
    fun _ x y ↦ (h x y).imp fun _ ⟨ι, hE, hι⟩ ↦ ⟨ι, by infer_instance, hE, hι⟩

/-- The diagonal is a closed immersion once every equalizer locus is represented by a
closed immersion. -/
theorem isClosedImmersion_diag_of_representsEqualizer
    (h : ∀ ⦃U : Over S⦄ (x y : F.obj (op U)), ∃ (Z : Over S) (ι : Z ⟶ U),
      RepresentsEqualizer ι x y ∧ AlgebraicGeometry.IsClosedImmersion ι.left) :
    IsClosedImmersion (diag F) :=
  relative_diag_of_representsEqualizer @AlgebraicGeometry.IsClosedImmersion.{u}
    fun _ x y ↦ (h x y).imp fun _ ⟨ι, hE, hι⟩ ↦ ⟨ι, by infer_instance, hE, hι⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
