import Langlands.GroupScheme.HomScheme.Universal
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Full universal families of closed group-scheme embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- An actual scheme representing closed group-scheme embeddings on every test. -/
structure ClosedEmbeddingModel {S : Scheme.{u}} (H G : GroupScheme S) where
  scheme : Over S
  family : RelativeHom H G scheme
  closed : IsClosedSubgroup family
  universal : ∀ T : Over S, Function.Bijective
    (fun a : T ⟶ scheme =>
      (⟨evaluate a family, isClosedImmersion_evaluate a family closed⟩ :
        {f : RelativeHom H G T // IsClosedSubgroup f}))

namespace ClosedEmbeddingModel

variable {S : Scheme.{u}} {H G : GroupScheme S} (M : ClosedEmbeddingModel H G)

/-- Classify an actual closed embedding by its unique parameter. -/
def parameter {T : Over S} (f : RelativeHom H G T) (hf : IsClosedSubgroup f) :
    T ⟶ M.scheme :=
  Classical.choose ((M.universal T).surjective ⟨f, hf⟩)

@[simp]
theorem evaluate_parameter {T : Over S} (f : RelativeHom H G T)
    (hf : IsClosedSubgroup f) : evaluate (M.parameter f hf) M.family = f :=
  congrArg Subtype.val (Classical.choose_spec ((M.universal T).surjective ⟨f, hf⟩))

/-- Equality of closed-family parameters is detected by their evaluations. -/
theorem parameter_ext {T : Over S} {a b : T ⟶ M.scheme}
    (h : evaluate a M.family = evaluate b M.family) : a = b :=
  (M.universal T).injective (Subtype.ext h)

/-- The classifying map commutes with every test-scheme restriction. -/
theorem parameter_comp {T T' : Over S} (a : T' ⟶ T)
    (f : RelativeHom H G T) (hf : IsClosedSubgroup f) :
    a ≫ M.parameter f hf =
      M.parameter (evaluate a f) (isClosedImmersion_evaluate a f hf) := by
  apply M.parameter_ext
  rw [evaluate_comp, evaluate_parameter, evaluate_parameter]

/-- Restrict an actual universal Hom family to an open representing exactly
the closed-immersion condition on every test scheme. -/
def ofOpen {Y : Over S} (j : RelativeHom H G Y) (hj : IsUniversal j)
    (U : Y.left.Opens)
    (hU : ∀ (T : Over S) (a : T ⟶ Y), Set.range a.left ⊆ U ↔
      IsClosedSubgroup (evaluate a j)) : ClosedEmbeddingModel H G := by
  let V : Over S := Over.mk (U.ι ≫ Y.hom)
  let aU : V ⟶ Y := Over.homMk U.ι rfl
  let : Mono aU := Over.mono_of_mono_left aU
  have hclosed : IsClosedSubgroup (evaluate aU j) :=
    (hU V aU).mp (by rintro _ ⟨x, rfl⟩; exact x.property)
  refine ⟨V, evaluate aU j, hclosed, fun T => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply (cancel_mono aU).mp
    apply (hj T).injective
    change evaluate (a ≫ aU) j = evaluate (b ≫ aU) j
    simpa only [evaluate_comp] using congrArg Subtype.val hab
  · rintro ⟨f, hf⟩
    obtain ⟨a, ha⟩ := (hj T).surjective f
    change evaluate a j = f at ha
    have hrange : Set.range a.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact (hU T a).mpr (by rw [ha]; exact hf)
    let l := IsOpenImmersion.lift U.ι a.left hrange
    have hl : l ≫ U.ι = a.left := IsOpenImmersion.lift_fac _ _ _
    let a' : T ⟶ V := Over.homMk l (by
      change l ≫ U.ι ≫ Y.hom = T.hom
      rw [← Category.assoc, hl]
      exact Over.w a)
    have hfac : a' ≫ aU = a := Over.OverMorphism.ext hl
    refine ⟨a', Subtype.ext ?_⟩
    change evaluate a' (evaluate aU j) = f
    rw [← evaluate_comp, hfac, ha]

end ClosedEmbeddingModel

end Langlands.GroupScheme.HomScheme
