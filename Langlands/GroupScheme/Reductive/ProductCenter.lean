import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.ImageGenerationSubgroup

/-! # Full scheme-theoretic centres of binary products -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H Z W : GroupScheme S}

/-- A point of a product is central exactly when each coordinate is central,
after every restriction of the test scheme. -/
theorem mem_center_tensor_iff {T : Over S} (x : T ⟶ (G ⊗ H).X) :
    x ∈ (center (G ⊗ H)).carrier T ↔
      x ≫ fst G.X H.X ∈ (center G).carrier T ∧
      x ≫ snd G.X H.X ∈ (center H).carrier T := by
  constructor
  · intro hx
    constructor
    · intro T' a y
      apply (commute_iff_eq _ _).mpr
      have h := congrArg (· ≫ fst G.X H.X)
        (hx T' a (lift y (1 : T' ⟶ H.X))).eq
      simpa only [MonObj.mul_comp, lift_fst, Category.assoc] using h
    · intro T' a y
      apply (commute_iff_eq _ _).mpr
      have h := congrArg (· ≫ snd G.X H.X)
        (hx T' a (lift (1 : T' ⟶ G.X) y)).eq
      simpa only [MonObj.mul_comp, lift_snd, Category.assoc] using h
  · rintro ⟨hG, hH⟩ T' a y
    change (a ≫ x) * y = y * (a ≫ x)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [MonObj.mul_comp, Category.assoc]
      exact (hG T' a (y ≫ fst G.X H.X)).eq
    · simp only [MonObj.mul_comp, Category.assoc]
      exact (hH T' a (y ≫ snd G.X H.X)).eq

/-- The tensor of actual full-centre inclusions represents the full centre
of the actual product, including its infinitesimal structure. -/
theorem IsSchemeTheoreticCenter.tensor {z : Z ⟶ G} {w : W ⟶ H}
    (hz : IsSchemeTheoreticCenter z) (hw : IsSchemeTheoreticCenter w) :
    IsSchemeTheoreticCenter (z ⊗ₘ w) := by
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsClosedImmersion w.hom.hom.left := hw.1
  refine ⟨?_, ?_⟩
  · change IsClosedImmersion (z.hom.hom ⊗ₘ w.hom.hom).left
    exact ImageGeneration.isClosedImmersion_tensorHom_left _ _
  · apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      apply (mem_center_tensor_iff _).mpr
      constructor
      · change (y ≫ (z.hom.hom ⊗ₘ w.hom.hom)) ≫ fst G.X H.X ∈ _
        rw [Category.assoc, tensorHom_fst, ← Category.assoc]
        exact hz.isCentral T (y ≫ fst Z.X W.X)
      · change (y ≫ (z.hom.hom ⊗ₘ w.hom.hom)) ≫ snd G.X H.X ∈ _
        rw [Category.assoc, tensorHom_snd, ← Category.assoc]
        exact hw.isCentral T (y ≫ snd Z.X W.X)
    · intro hx
      obtain ⟨hxG, hxH⟩ := (mem_center_tensor_iff x).mp hx
      rw [← hz.2] at hxG
      rw [← hw.2] at hxH
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxG
      obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hxH
      refine SubgroupFunctor.mem_range.mpr ⟨lift y v, ?_⟩
      change lift y v ≫ (z.hom.hom ⊗ₘ w.hom.hom) = x
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
        exact hy
      · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
        exact hv

/-- The actual product of supplied full centres, with its representing inclusion. -/
def productCenterInclusion (z : Z ⟶ G) (w : W ⟶ H)
    (hz : IsSchemeTheoreticCenter z) (hw : IsSchemeTheoreticCenter w) :
    { c : Z ⊗ W ⟶ G ⊗ H // IsSchemeTheoreticCenter c } :=
  ⟨z ⊗ₘ w, hz.tensor hw⟩

@[simp]
theorem productCenterInclusion_val (z : Z ⟶ G) (w : W ⟶ H)
    (hz : IsSchemeTheoreticCenter z) (hw : IsSchemeTheoreticCenter w) :
    (productCenterInclusion z w hz hw).val = z ⊗ₘ w := rfl

/-- Finite full centres are preserved by actual binary products over every base. -/
theorem HasFiniteCenter.tensor (hG : HasFiniteCenter G) (hH : HasFiniteCenter H) :
    HasFiniteCenter (G ⊗ H) := by
  obtain ⟨Z, z, hz, hZ⟩ := hG
  obtain ⟨W, w, hw, hW⟩ := hH
  refine ⟨Z ⊗ W, z ⊗ₘ w, hz.tensor hw, ?_⟩
  exact prop_tensor_hom (@IsFinite : MorphismProperty Scheme.{u}) Z.X W.X hZ hW

end Langlands.GroupScheme
