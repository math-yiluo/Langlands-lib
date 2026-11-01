import Langlands.Geometry.Analytic.AtlasDisjointUnion
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Complete bounded maps from disjoint unions of supplied atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasDisjointUnion

open CategoryTheory CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I : Type z} (A : I → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hA : ∀ i, (A i).atlas.HasNonemptyCharts)

/-- The actual component injection, retaining every original chart and algebra. -/
def inclusion (i : I) : A i ⟶ presentation A hA where
  baseMap :=
    { toFun := fun x => ⟨i, x⟩
      continuous_toFun := continuous_sigmaMk (σ := fun i => (A i).space) }
  indexMap c := ⟨i, c⟩
  index_mono c d h := (chart_subset_iff (fun i => (A i).atlas) i c d).mpr h
  pullback c := BoundedAlgHom.id K ((A i).atlas.algebra c)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := BoundedAlgHom.ext fun _ => rfl

@[simp]
theorem inclusion_baseMap (i : I) (x : (A i).space) :
    (inclusion A hA i).baseMap x = Sigma.mk i x := rfl

@[simp]
theorem inclusion_indexMap (i : I) (c : (A i).atlas.Index) :
    (inclusion A hA i).indexMap c = ⟨i, c⟩ := rfl

@[simp]
theorem inclusion_pullback (i : I) (c : (A i).atlas.Index) :
    (inclusion A hA i).pullback c = BoundedAlgHom.id K ((A i).atlas.algebra c) := rfl

variable {B C : AffinoidAtlasPresentation.{u, max z v, max z w} K}

/-- Assemble complete component arrows into an arbitrary atlas target.
Containment identifies component tags, leaving original chart containments intact. -/
def desc (f : ∀ i, A i ⟶ B) : presentation A hA ⟶ B where
  baseMap :=
    { toFun := fun x => (f x.fst).baseMap x.snd
      continuous_toFun := continuous_sigma fun i => (f i).baseMap.continuous }
  indexMap c := (f c.fst).indexMap c.snd
  index_mono c d h := by
    rcases c with ⟨i, c⟩
    rcases d with ⟨j, d⟩
    have hij := tag_eq_of_subset (fun i => (A i).atlas) hA ⟨i, c⟩ ⟨j, d⟩ h
    dsimp at hij
    subst j
    exact (f i).index_mono c d ((chart_subset_iff (fun i => (A i).atlas) i c d).mp h)
  pullback c := (f c.fst).pullback c.snd
  chart_comm c x := (f c.fst).chart_comm c.snd x
  restriction_comm c d h := by
    rcases c with ⟨i, c⟩
    rcases d with ⟨j, d⟩
    have hij := tag_eq_of_subset (fun i => (A i).atlas) hA ⟨i, c⟩ ⟨j, d⟩ h
    dsimp at hij
    subst j
    exact (f i).restriction_comm c d
      ((chart_subset_iff (fun i => (A i).atlas) i c d).mp h)

@[simp]
theorem desc_baseMap (f : ∀ i, A i ⟶ B) (i : I) (x : (A i).space) :
    (desc A hA f).baseMap ⟨i, x⟩ = (f i).baseMap x := rfl

@[simp]
theorem desc_indexMap (f : ∀ i, A i ⟶ B) (i : I) (c : (A i).atlas.Index) :
    (desc A hA f).indexMap ⟨i, c⟩ = (f i).indexMap c := rfl

@[simp]
theorem desc_pullback (f : ∀ i, A i ⟶ B) (i : I) (c : (A i).atlas.Index) :
    (desc A hA f).pullback ⟨i, c⟩ = (f i).pullback c := rfl

/-- Restriction recovers the entire component arrow, including bounded maps. -/
@[simp]
theorem inclusion_desc (f : ∀ i, A i ⟶ B) (i : I) :
    inclusion A hA i ≫ desc A hA f = f i := by
  apply AffinoidAtlasPresentation.Hom.ext
  · rfl
  · rfl
  · apply heq_of_eq
    funext c
    exact BoundedAlgHom.ext fun _ => rfl

/-- Descending all component restrictions recovers all original arrow data. -/
@[simp]
theorem desc_inclusion (p : presentation A hA ⟶ B) :
    desc A hA (fun i => inclusion A hA i ≫ p) = p := by
  apply AffinoidAtlasPresentation.Hom.ext
  · apply ContinuousMap.ext
    rintro ⟨i, x⟩
    rfl
  · funext c
    rcases c with ⟨i, c⟩
    rfl
  · apply heq_of_eq
    funext c
    rcases c with ⟨i, c⟩
    exact BoundedAlgHom.ext fun _ => rfl

/-- A constructed Hom correspondence for arbitrary chosen-atlas targets. -/
def homEquiv : (presentation A hA ⟶ B) ≃ (∀ i, A i ⟶ B) where
  toFun p i := inclusion A hA i ≫ p
  invFun := desc A hA
  left_inv := desc_inclusion A hA
  right_inv f := funext (inclusion_desc A hA f)

/-- Complete component restrictions determine the full chosen atlas arrow. -/
theorem hom_ext {f g : presentation A hA ⟶ B}
    (h : ∀ i, inclusion A hA i ≫ f = inclusion A hA i ≫ g) : f = g :=
  (homEquiv A hA).injective (funext h)

theorem desc_unique (f : ∀ i, A i ⟶ B) (p : presentation A hA ⟶ B)
    (hp : ∀ i, inclusion A hA i ≫ p = f i) : p = desc A hA f := by
  apply hom_ext A hA
  intro i
  rw [inclusion_desc, hp]

/-- Descent commutes with every complete target arrow. -/
theorem desc_comp (f : ∀ i, A i ⟶ B) (g : B ⟶ C) :
    desc A hA f ≫ g = desc A hA (fun i => f i ≫ g) := by
  apply hom_ext A hA
  intro i
  rw [← Category.assoc, inclusion_desc, inclusion_desc]

/-- The constructed cofan has the actual sigma-space presentation as vertex. -/
def cofan : Cofan A := Cofan.mk (presentation A hA) (inclusion A hA)

/-- This is a categorical coproduct in the complete chosen-map category. -/
def cofanIsColimit : IsColimit (cofan A hA) :=
  Cofan.IsColimit.mk _
    (fun s => desc A hA s.inj)
    (fun s i => inclusion_desc A hA s.inj i)
    (fun s p hp => desc_unique A hA s.inj p hp)

end Langlands.Analytic.AtlasDisjointUnion
