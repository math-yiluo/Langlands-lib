import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Adjunctions from a counit on a copresenting subcategory

Let `L : D ⥤ C` and `R : C ⥤ D` preserve zero morphisms, and let `S` be a property of
objects of `C`. Suppose that every object `X` of `C` is the kernel of a morphism
`k : X₀ ⟶ X₁` between `S`-objects, that every morphism from `X` to an `S`-object extends
along `X ⟶ X₀`, and that `R` sends these kernel diagrams to kernel diagrams. Then a
family `ε_Z : L (R Z) ⟶ Z`, natural in all morphisms between `S`-objects and such that
`g ↦ L g ≫ ε_Z` is bijective for every `S`-object `Z`, extends uniquely to the counit of
an adjunction `L ⊣ R`.

This is the formal step of Renard 2026, VI.9.6 (printed pp.201–202), where `S` is the
class of smooth contragredients and every smooth representation `π` is the kernel of
`π~~ ⟶ (π~~/π)~~`.

The counit on `S`-objects may be given as a factorisation: if `ε' : E ⟶ F` factors on
every `S`-object through a natural transformation `ι : 𝟭 ⟶ F` that is a monomorphism
there, the factorisations form a natural transformation `E ⟶ 𝟭` on `S`-objects
(`liftOfMonoFactorisation`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

section MonoFactorisation

variable {E F : C ⥤ C} {S : ObjectProperty C} (ε' : E ⟶ F) (ι : 𝟭 C ⟶ F)
  (hmono : ∀ X, S X → Mono (ι.app X))
  (hfac : ∀ X, S X → ∃ e : E.obj X ⟶ X, e ≫ ι.app X = ε'.app X)

/-- A natural transformation `ε' : E ⟶ F` that factors through a natural transformation
`ι : 𝟭 ⟶ F` on every `S`-object, where `ι` is a monomorphism, gives a natural
transformation `E ⟶ 𝟭` on `S`-objects: the factorisation. -/
def liftOfMonoFactorisation : S.ι ⋙ E ⟶ S.ι where
  app X := Classical.choose (hfac X.1 X.2)
  naturality X Y f := by
    have := hmono Y.1 Y.2
    rw [← cancel_mono (ι.app Y.1)]
    change (E.map f.hom ≫ Classical.choose (hfac Y.1 Y.2)) ≫ ι.app Y.1 =
      (Classical.choose (hfac X.1 X.2) ≫ f.hom) ≫ ι.app Y.1
    have hι : f.hom ≫ ι.app Y.1 = ι.app X.1 ≫ F.map f.hom := ι.naturality f.hom
    rw [Category.assoc, Classical.choose_spec (hfac Y.1 Y.2), ε'.naturality, Category.assoc, hι,
      ← Category.assoc, Classical.choose_spec (hfac X.1 X.2)]

/-- The defining property of `liftOfMonoFactorisation`. -/
@[reassoc]
theorem liftOfMonoFactorisation_app_comp (X : S.FullSubcategory) :
    (liftOfMonoFactorisation ε' ι hmono hfac).app X ≫ ι.app X.1 = ε'.app X.1 :=
  Classical.choose_spec (hfac X.1 X.2)

/-- `liftOfMonoFactorisation` is the unique factorisation. -/
theorem eq_liftOfMonoFactorisation_app (X : S.FullSubcategory) (e : E.obj X.1 ⟶ X.1)
    (he : e ≫ ι.app X.1 = ε'.app X.1) :
    e = (liftOfMonoFactorisation ε' ι hmono hfac).app X := by
  have := hmono X.1 X.2
  rw [← cancel_mono (ι.app X.1), he, liftOfMonoFactorisation_app_comp]

end MonoFactorisation

variable [HasZeroMorphisms C]

/-- A copresentation of `X` by `S`-objects: `X` is the kernel of a morphism
`k : obj₀ ⟶ obj₁` between `S`-objects, and every morphism from `X` to an `S`-object
extends along the kernel inclusion `ι : X ⟶ obj₀`. -/
structure KernelCopresentation (S : ObjectProperty C) (X : C) where
  /-- The object receiving the kernel inclusion. -/
  obj₀ : C
  /-- The target of the morphism whose kernel is `X`. -/
  obj₁ : C
  /-- The kernel inclusion. -/
  ι : X ⟶ obj₀
  /-- The morphism whose kernel is `X`. -/
  k : obj₀ ⟶ obj₁
  w : ι ≫ k = 0
  /-- `X` is a kernel of `k`. -/
  isLimit : IsLimit (KernelFork.ofι ι w)
  mem₀ : S obj₀
  mem₁ : S obj₁
  /-- Every morphism to an `S`-object extends along `ι`. -/
  extend : ∀ {Z : C}, S Z → ∀ h : X ⟶ Z, ∃ h₀ : obj₀ ⟶ Z, ι ≫ h₀ = h

namespace KernelCopresentation

variable {S : ObjectProperty C} {X : C} (c : KernelCopresentation S X)

instance mono_ι : Mono c.ι :=
  mono_of_isLimit_fork c.isLimit

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- The image under `R` of the kernel diagram of a copresentation is again a fork. -/
theorem map_w (R : C ⥤ D) [R.PreservesZeroMorphisms] : R.map c.ι ≫ R.map c.k = 0 := by
  rw [← R.map_comp, c.w, R.map_zero]

end KernelCopresentation

section Extension

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  (L : D ⥤ C) (R : C ⥤ D) [L.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
  {S : ObjectProperty C} (ε : S.ι ⋙ R ⋙ L ⟶ S.ι)

omit [HasZeroMorphisms C] [HasZeroMorphisms D] [L.PreservesZeroMorphisms]
  [R.PreservesZeroMorphisms] in
/-- Naturality of `ε`, stated for morphisms between underlying objects. -/
theorem counit_naturality_of_mem {X Y : C} (hX : S X) (hY : S Y) (f : X ⟶ Y) :
    L.map (R.map f) ≫ ε.app ⟨Y, hY⟩ = ε.app ⟨X, hX⟩ ≫ f :=
  ε.naturality (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (ObjectProperty.homMk f)

theorem counit_comp_k_eq_zero {X : C} (c : KernelCopresentation S X) :
    (L.map (R.map c.ι) ≫ ε.app ⟨c.obj₀, c.mem₀⟩) ≫ c.k = 0 := by
  rw [Category.assoc, ← counit_naturality_of_mem L R ε c.mem₀ c.mem₁ c.k, ← Category.assoc,
    ← L.map_comp, c.map_w R, L.map_zero, zero_comp]

/-- The extension of `ε` to an object with a copresentation by `S`-objects: the
factorisation of `L (R X) ⟶ L (R X₀) ⟶ X₀` through the kernel `X`. -/
def extendedCounit {X : C} (c : KernelCopresentation S X) : L.obj (R.obj X) ⟶ X :=
  (KernelFork.IsLimit.lift' c.isLimit _ (counit_comp_k_eq_zero L R ε c)).1

@[reassoc]
theorem extendedCounit_ι {X : C} (c : KernelCopresentation S X) :
    extendedCounit L R ε c ≫ c.ι = L.map (R.map c.ι) ≫ ε.app ⟨c.obj₀, c.mem₀⟩ :=
  (KernelFork.IsLimit.lift' c.isLimit _ (counit_comp_k_eq_zero L R ε c)).2

/-- The extended counit is natural with respect to morphisms into `S`-objects. -/
theorem extendedCounit_naturality_of_mem {X Z : C} (c : KernelCopresentation S X) (hZ : S Z)
    (h : X ⟶ Z) : L.map (R.map h) ≫ ε.app ⟨Z, hZ⟩ = extendedCounit L R ε c ≫ h := by
  obtain ⟨h₀, rfl⟩ := c.extend hZ h
  rw [R.map_comp, L.map_comp, Category.assoc, counit_naturality_of_mem L R ε c.mem₀ hZ h₀,
    extendedCounit_ι_assoc]

/-- The extended counit is natural. -/
@[reassoc]
theorem extendedCounit_naturality {X Y : C} (cX : KernelCopresentation S X)
    (cY : KernelCopresentation S Y) (f : X ⟶ Y) :
    L.map (R.map f) ≫ extendedCounit L R ε cY = extendedCounit L R ε cX ≫ f := by
  rw [← cancel_mono cY.ι, Category.assoc, extendedCounit_ι, ← Category.assoc, ← L.map_comp,
    ← R.map_comp, extendedCounit_naturality_of_mem L R ε cX cY.mem₀, Category.assoc]

/-- On an `S`-object the extended counit is `ε` itself. -/
theorem extendedCounit_eq_of_mem {X : C} (c : KernelCopresentation S X) (hX : S X) :
    extendedCounit L R ε c = ε.app ⟨X, hX⟩ := by
  rw [← cancel_mono c.ι, extendedCounit_ι, counit_naturality_of_mem L R ε hX c.mem₀]

/-- If `g ↦ L g ≫ ε_Z` is bijective for every `S`-object `Z` and `R` preserves the
kernel diagram of a copresentation of `X`, then `g ↦ L g ≫ ε_X` is bijective for the
extended counit. -/
theorem bijective_extendedCounit
    (hbij : ∀ (Z : C) (hZ : S Z) (τ : D),
      Function.Bijective (fun g : τ ⟶ R.obj Z => L.map g ≫ ε.app ⟨Z, hZ⟩))
    {X : C} (c : KernelCopresentation S X)
    (hc : IsLimit (KernelFork.ofι (R.map c.ι) (c.map_w R))) (τ : D) :
    Function.Bijective (fun g : τ ⟶ R.obj X => L.map g ≫ extendedCounit L R ε c) := by
  have : Mono (R.map c.ι) := mono_of_isLimit_fork hc
  refine ⟨fun g g' hgg' => ?_, fun h => ?_⟩
  · have hgg'' : L.map (g ≫ R.map c.ι) ≫ ε.app ⟨c.obj₀, c.mem₀⟩ =
        L.map (g' ≫ R.map c.ι) ≫ ε.app ⟨c.obj₀, c.mem₀⟩ := by
      simp only [L.map_comp, Category.assoc, ← extendedCounit_ι L R ε c]
      simp only [← Category.assoc]
      exact congrArg (· ≫ c.ι) hgg'
    exact (cancel_mono (R.map c.ι)).1 ((hbij _ c.mem₀ τ).1 hgg'')
  · obtain ⟨g₀, hg₀⟩ := (hbij _ c.mem₀ τ).2 (h ≫ c.ι)
    replace hg₀ : L.map g₀ ≫ ε.app ⟨c.obj₀, c.mem₀⟩ = h ≫ c.ι := hg₀
    have hk : g₀ ≫ R.map c.k = 0 := by
      apply (hbij _ c.mem₁ τ).1
      change L.map (g₀ ≫ R.map c.k) ≫ ε.app ⟨c.obj₁, c.mem₁⟩ =
        L.map 0 ≫ ε.app ⟨c.obj₁, c.mem₁⟩
      rw [L.map_comp, Category.assoc, counit_naturality_of_mem L R ε c.mem₀ c.mem₁,
        ← Category.assoc]
      change (L.map g₀ ≫ ε.app ⟨c.obj₀, c.mem₀⟩) ≫ c.k = _
      rw [hg₀, Category.assoc, c.w, comp_zero, L.map_zero, zero_comp]
    obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hc g₀ hk
    replace hg : g ≫ R.map c.ι = g₀ := hg
    refine ⟨g, ?_⟩
    change L.map g ≫ extendedCounit L R ε c = h
    rw [← cancel_mono c.ι, Category.assoc, extendedCounit_ι, ← Category.assoc, ← L.map_comp,
      hg]
    exact hg₀

/-- The adjunction `L ⊣ R` whose counit extends `ε`. -/
def adjunctionOfCopresentedCounit
    (hbij : ∀ (Z : C) (hZ : S Z) (τ : D),
      Function.Bijective (fun g : τ ⟶ R.obj Z => L.map g ≫ ε.app ⟨Z, hZ⟩))
    (c : ∀ X : C, KernelCopresentation S X)
    (hc : ∀ X : C, IsLimit (KernelFork.ofι (R.map (c X).ι) ((c X).map_w R))) : L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun τ X =>
        (Equiv.ofBijective _ (bijective_extendedCounit L R ε hbij (c X) (hc X) τ)).symm
      homEquiv_naturality_left_symm := fun {τ' τ X} f g => by
        simp only [Equiv.symm_symm, Equiv.ofBijective_apply, L.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {τ X Y} f g => by
        rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, L.map_comp, Category.assoc,
          extendedCounit_naturality L R ε (c X) (c Y), ← Category.assoc]
        congr 1
        exact ((Equiv.ofBijective _
          (bijective_extendedCounit L R ε hbij (c X) (hc X) τ)).apply_symm_apply f).symm }

/-- The counit of `adjunctionOfCopresentedCounit` is the extended counit. -/
theorem adjunctionOfCopresentedCounit_counit_app
    (hbij : ∀ (Z : C) (hZ : S Z) (τ : D),
      Function.Bijective (fun g : τ ⟶ R.obj Z => L.map g ≫ ε.app ⟨Z, hZ⟩))
    (c : ∀ X : C, KernelCopresentation S X)
    (hc : ∀ X : C, IsLimit (KernelFork.ofι (R.map (c X).ι) ((c X).map_w R))) (X : C) :
    (adjunctionOfCopresentedCounit L R ε hbij c hc).counit.app X =
      extendedCounit L R ε (c X) := by
  simp [adjunctionOfCopresentedCounit]

/-- On an `S`-object, the counit of `adjunctionOfCopresentedCounit` is `ε`. -/
theorem adjunctionOfCopresentedCounit_counit_app_of_mem
    (hbij : ∀ (Z : C) (hZ : S Z) (τ : D),
      Function.Bijective (fun g : τ ⟶ R.obj Z => L.map g ≫ ε.app ⟨Z, hZ⟩))
    (c : ∀ X : C, KernelCopresentation S X)
    (hc : ∀ X : C, IsLimit (KernelFork.ofι (R.map (c X).ι) ((c X).map_w R))) {X : C}
    (hX : S X) :
    (adjunctionOfCopresentedCounit L R ε hbij c hc).counit.app X = ε.app ⟨X, hX⟩ := by
  rw [adjunctionOfCopresentedCounit_counit_app, extendedCounit_eq_of_mem L R ε (c X) hX]

end Extension

end Langlands
