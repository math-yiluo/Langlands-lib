import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Ground-field rational points after extension of the base field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The actual `K`-point obtained from a `k`-point by extension of scalars. -/
def geometricRationalPoint (X : Over (Spec (CommRingCat.of k)))
    (p : RationalPoint k X) :
    RationalPoint K
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj X) :=
  Over.homMk
    (pullback.lift
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.left) (𝟙 _)
      (by
        have hp : p.left ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := Over.w p
        dsimp at hp ⊢
        rw [Category.assoc, hp, Category.comp_id, Category.id_comp]))
    (by exact pullback.lift_snd _ _ _)

@[reassoc]
theorem geometricRationalPoint_fst (X : Over (Spec (CommRingCat.of k)))
    (p : RationalPoint k X) :
    (geometricRationalPoint (K := K) X p).left ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.left := by
  exact pullback.lift_fst _ _ _

/-- Extension of ground-field sections commutes with maps of schemes. -/
@[reassoc]
theorem geometricRationalPoint_natural
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) (p : RationalPoint k X) :
    geometricRationalPoint (K := K) X p ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f =
      geometricRationalPoint (K := K) Y (p ≫ f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [geometricRationalPoint, Over.pullback_map_left, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- Ground-field rational points are dense in the actual scalar extension to `K`. -/
def HasDenseGeometricRationalPoints (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) : Prop :=
  Dense (⋃ p : RationalPoint k X, Set.range (geometricRationalPoint (K := K) X p).left)

/-- Density of ground-field sections descends along a map dominant after scalar extension. -/
theorem hasDenseGeometricRationalPoints_of_denseRange
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (hf : DenseRange
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left)
    (hX : HasDenseGeometricRationalPoints k K X) :
    HasDenseGeometricRationalPoints k K Y := by
  apply hf.dense_of_mapsTo
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left.continuous hX
  rintro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢
  obtain ⟨p, a, rfl⟩ := hx
  refine ⟨p ≫ f, a, ?_⟩
  have h := congrArg (fun q => q.left a) (geometricRationalPoint_natural (K := K) f p)
  exact h.symm

end Langlands.AlgebraicGeometry.PointTopology
