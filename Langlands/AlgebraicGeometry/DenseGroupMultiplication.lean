import Langlands.AlgebraicGeometry.FibreDenseOpen
import Langlands.GroupScheme.DominantHomFlat

/-! # Multiplication of a fibrewise dense open in a smooth group scheme -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.DenseGroupMultiplication

variable {S : Scheme.{u}}

/-- A product of two open immersions over a base is an open immersion. -/
theorem isOpenImmersion_tensorHom {U V A B : Over S} (a : U ⟶ A) (b : V ⟶ B)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] : IsOpenImmersion (a ⊗ₘ b).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (Over.w _).symm (Over.w _).symm

/-- The image of the product is the intersection of the inverse images under the projections. -/
theorem opensRange_tensorHom {U V A B : Over S} (a : U ⟶ A) (b : V ⟶ B)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left]
    [IsOpenImmersion (a ⊗ₘ b).left] :
    (a ⊗ₘ b).left.opensRange =
      ((fst A B).left ⁻¹ᵁ a.left.opensRange) ⊓ ((snd A B).left ⁻¹ᵁ b.left.opensRange) := by
  apply SetLike.coe_injective
  change Set.range (a ⊗ₘ b).left = _
  rw [Over.tensorHom_left]
  exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _

/-- Products of fibrewise dense opens in flat schemes are fibrewise dense. -/
theorem fibreDense_tensorHom {U V A B : Over S} (a : U ⟶ A) (b : V ⟶ B)
    [Flat A.hom] [Flat B.hom] [IsOpenImmersion a.left] [IsOpenImmersion b.left]
    [IsOpenImmersion (a ⊗ₘ b).left] (ha : FibreGenerizationDense A.hom a.left.opensRange)
    (hb : FibreGenerizationDense B.hom b.left.opensRange) :
    FibreGenerizationDense (A ⊗ B).hom (a ⊗ₘ b).left.opensRange := by
  have : Flat (fst A B).left := inferInstanceAs (Flat (pullback.fst A.hom B.hom))
  have : Flat (snd A B).left := inferInstanceAs (Flat (pullback.snd A.hom B.hom))
  rw [opensRange_tensorHom a b]
  exact (Over.w (fst A B) ▸ ha.preimage_flat (fst A B).left).inf
    (Over.w (snd A B) ▸ hb.preimage_flat (snd A B).left)

open Langlands.GroupScheme.DominantHomFlat

variable (G : Langlands.GroupScheme S)

private lemma fst_mul_eq : fst G.X G.X * snd G.X G.X = μ[G.X] := by
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp]

/-- The first projection and multiplication form a product over the structural map. -/
theorem isPullback_fst_mul :
    IsPullback (fst G.X G.X).left μ[G.X].left G.X.hom G.X.hom := by
  let e := shearLeft (𝟙 G.X)
  refine IsPullback.of_iso_pullback ⟨(Over.w (fst G.X G.X)).trans (Over.w μ[G.X]).symm⟩
    ((Over.forget S).mapIso e) ?_ ?_
  · change (e.hom ≫ fst G.X G.X).left = _
    simp [e, shearLeft]
  · change (e.hom ≫ snd G.X G.X).left = _
    rw [shearLeft_hom_snd, Category.comp_id, fst_mul_eq]

/-- The second projection and multiplication form a product over the structural map. -/
theorem isPullback_snd_mul :
    IsPullback (snd G.X G.X).left μ[G.X].left G.X.hom G.X.hom := by
  apply IsPullback.flip
  let e := shearRight (𝟙 G.X)
  refine IsPullback.of_iso_pullback ⟨(Over.w μ[G.X]).trans (Over.w (snd G.X G.X)).symm⟩
    ((Over.forget S).mapIso e) ?_ ?_
  · change (e.hom ≫ fst G.X G.X).left = _
    rw [shearRight_hom_fst, Category.comp_id, fst_mul_eq]
  · change (e.hom ≫ snd G.X G.X).left = _
    simp [e, shearRight]

/-- Multiplication on a smooth group is smooth by either product description. -/
theorem smooth_mul [Smooth G.X.hom] : Smooth μ[G.X].left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth)
    (isPullback_fst_mul G) inferInstance

/-- Multiplying the two images of points of an open subscheme. -/
abbrev openProduct {U : Over S} (a : U ⟶ G.X) : U ⊗ U ⟶ G.X :=
  (a ⊗ₘ a) ≫ μ[G.X]

/-- The multiplication map restricted to a fibrewise dense open times itself is surjective. -/
theorem surjective_openProduct {U : Over S} (a : U ⟶ G.X) [IsOpenImmersion a.left]
    (ha : FibreGenerizationDense G.X.hom a.left.opensRange) : Surjective (openProduct G a).left := by
  have : IsOpenImmersion (a ⊗ₘ a).left := isOpenImmersion_tensorHom a a
  have h₁ := FibreGenerizationDense.preimage_isPullback (isPullback_fst_mul G) ha
  have h₂ := FibreGenerizationDense.preimage_isPullback (isPullback_snd_mul G) ha
  have hd := h₁.inf h₂
  rw [← opensRange_tensorHom a a] at hd
  let s := lift (𝟙 G.X) (1 : G.X ⟶ G.X)
  have hs : s ≫ μ[G.X] = 𝟙 G.X := by rw [← Hom.mul_def, mul_one]
  constructor
  intro x
  obtain ⟨_, ⟨y, rfl⟩, hy, -⟩ := hd (s.left x)
  exact ⟨y, hy.trans (congrArg (fun k : G.X ⟶ G.X => k.left x) hs)⟩

end Langlands.AlgebraicGeometry.DenseGroupMultiplication
