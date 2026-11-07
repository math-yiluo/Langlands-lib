import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Kernels and exact functors of smooth representations

An injective intertwiner `ι : X ⟶ Y` whose range is the kernel of `k : Y ⟶ Z` is a
categorical kernel of `k` in the category of smooth representations.

A functor between categories of smooth representations *preserves short exact
sequences* if it sends every actual short exact sequence (`SmoothRep.IsShortExact`)
to one; this is the form of exactness in the Library's statement of Renard 2026,
VI.1.2. Such a functor preserves zero morphisms and injective intertwiners, and it
sends a kernel diagram `X ⟶ Y ⟶ Y/X ↪ Z` (cokernel projection followed by an
injection) to a kernel diagram.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uR uG uH uV uW

section Kernel

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

/-- Morphisms of smooth representations are determined by their intertwiners. -/
theorem hom_ext' {A B : SmoothRep.{uR, uG, uV} R G} {f g : A ⟶ B} (h : hom f = hom g) :
    f = g := by
  rw [← ofHom_hom f, ← ofHom_hom g, h]

/-- An injective intertwiner `ι` whose range is the kernel of `k` is a kernel of `k`. -/
def isLimitKernelForkOfRangeEq {X Y Z : SmoothRep.{uR, uG, uV} R G} (ι : X ⟶ Y)
    (k : Y ⟶ Z) (w : ι ≫ k = 0) (hι : Function.Injective (hom ι))
    (hr : LinearMap.range (hom ι).toLinearMap = LinearMap.ker (hom k).toLinearMap) :
    IsLimit (KernelFork.ofι ι w) :=
  haveI : Mono ι := (mono_iff_injective ι).2 hι
  KernelFork.IsLimit.ofι' ι w fun {W} g hg => by
    have hmem : ∀ x, (hom g).toLinearMap x ∈ LinearMap.range (hom ι).toLinearMap := by
      intro x
      rw [hr, LinearMap.mem_ker]
      exact congrArg (fun φ : W ⟶ Z => hom φ x) hg
    let e := LinearEquiv.ofInjective (hom ι).toLinearMap hι
    let l : W →ₗ[R] X := e.symm.toLinearMap ∘ₗ (hom g).toLinearMap.codRestrict _ hmem
    have hl : ∀ x, hom ι (l x) = hom g x := fun x =>
      LinearEquiv.ofInjective_symm_apply (hom ι).toLinearMap (h := hι)
        (⟨(hom g).toLinearMap x, hmem x⟩ : LinearMap.range (hom ι).toLinearMap)
    refine ⟨ofHom ⟨l, fun s => LinearMap.ext fun x => hι ?_⟩, hom_ext' ?_⟩
    · change hom ι (l (W.representation s x)) = hom ι (X.representation s (l x))
      rw [hl, (hom ι).isIntertwining, hl, (hom g).isIntertwining]
    · exact Representation.IntertwiningMap.ext (LinearMap.ext hl)

/-- An intertwiner followed by the projection onto its cokernel is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokernelπ {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    f ≫ cokernelπ f = 0 :=
  hom_ext' (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ x)))

/-- The range of an intertwiner is the kernel of its cokernel projection followed by
an injective intertwiner. -/
theorem range_eq_ker_cokernelπ_comp {A B C : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (b : cokernel f ⟶ C) (hb : Function.Injective (hom b)) :
    LinearMap.range (hom f).toLinearMap =
      LinearMap.ker (hom (cokernelπ f ≫ b)).toLinearMap := by
  rw [hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hb)]
  exact (Submodule.ker_mkQ _).symm

/-- An injective intertwiner is a kernel of its cokernel projection followed by an
injective intertwiner. -/
def isLimitCokernelπComp {A B C : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (hf : Function.Injective (hom f)) (b : cokernel f ⟶ C) (hb : Function.Injective (hom b)) :
    IsLimit (KernelFork.ofι (f := cokernelπ f ≫ b) f
      (by rw [comp_cokernelπ_assoc, zero_comp])) :=
  isLimitKernelForkOfRangeEq f _ _ hf (range_eq_ker_cokernelπ_comp f b hb)

end Kernel

section Exact

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

/-- A functor between categories of smooth representations preserves short exact
sequences if it sends every actual short exact sequence to a short exact sequence. -/
def PreservesShortExact (F : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uH, uW} R H) :
    Prop :=
  ∀ {A B C : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) (g : B ⟶ C),
    IsShortExact (hom f) (hom g) → IsShortExact (hom (F.map f)) (hom (F.map g))

/-- The cokernel projection of an injective intertwiner completes it to a short exact
sequence. -/
theorem isShortExact_cokernelπ {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (hf : Function.Injective (hom f)) : IsShortExact (hom f) (hom (cokernelπ f)) :=
  ⟨hf, mkQ_surjective B _, (Submodule.ker_mkQ _).symm⟩

namespace PreservesShortExact

variable {F : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uH, uW} R H}
  (hF : PreservesShortExact F)
include hF

/-- An exact functor sends the cokernel projection of an identity to zero. -/
theorem hom_map_cokernelπ_id (A : SmoothRep.{uR, uG, uV} R G) :
    hom (F.map (cokernelπ (𝟙 A))) = 0 := by
  obtain ⟨-, -, h⟩ := hF _ _ (isShortExact_cokernelπ (𝟙 A) Function.injective_id)
  rw [F.map_id, hom_id] at h
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_)
  have hx : x ∈ LinearMap.ker (hom (F.map (cokernelπ (𝟙 A)))).toLinearMap := by
    rw [← h]
    exact ⟨x, rfl⟩
  exact hx

/-- An exact functor preserves zero morphisms. -/
theorem preservesZeroMorphisms : F.PreservesZeroMorphisms where
  map_zero A B := by
    have h0 : (0 : A ⟶ B) = cokernelπ (𝟙 A) ≫ 0 := (comp_zero).symm
    apply hom_ext'
    rw [h0, F.map_comp, hom_comp, hF.hom_map_cokernelπ_id]
    exact Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
      map_zero (hom (F.map (0 : cokernel (𝟙 A) ⟶ B))))

/-- An exact functor preserves injectivity of intertwiners. -/
theorem injective_map {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (hf : Function.Injective (hom f)) : Function.Injective (hom (F.map f)) :=
  (hF _ _ (isShortExact_cokernelπ f hf)).1

/-- An exact functor sends the kernel diagram `X ⟶ Y ⟶ Y/X ↪ Z` of an injective
intertwiner `ι`, followed by the cokernel projection and an injection `b`, to an
injective intertwiner whose range is the kernel of the image of the composite. -/
theorem range_map_eq_ker_map_comp {X Y Z : SmoothRep.{uR, uG, uV} R G} (ι : X ⟶ Y)
    (hι : Function.Injective (hom ι)) (b : cokernel ι ⟶ Z)
    (hb : Function.Injective (hom b)) :
    LinearMap.range (hom (F.map ι)).toLinearMap =
      LinearMap.ker (hom (F.map (cokernelπ ι ≫ b))).toLinearMap := by
  rw [F.map_comp, hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 (hF.injective_map b hb))]
  exact (hF _ _ (isShortExact_cokernelπ ι hι)).2.2

/-- An exact functor sends the kernel diagram of an injective intertwiner `ι`,
followed by its cokernel projection and an injective intertwiner `b`, to a kernel
diagram. -/
def isLimitMapCokernelπComp {X Y Z : SmoothRep.{uR, uG, uV} R G} (ι : X ⟶ Y)
    (hι : Function.Injective (hom ι)) (b : cokernel ι ⟶ Z) (hb : Function.Injective (hom b))
    (w : F.map ι ≫ F.map (cokernelπ ι ≫ b) = 0) :
    IsLimit (KernelFork.ofι (F.map ι) w) :=
  isLimitKernelForkOfRangeEq _ _ w (hF.injective_map ι hι)
    (hF.range_map_eq_ker_map_comp ι hι b hb)

end PreservesShortExact

end Exact

end Langlands.SmoothRep
