import Langlands.GroupScheme.Rational.PointedFamilyFieldExtension
import Langlands.GroupScheme.Rational.CommutativePTorsionVectorFactorStatement
import Langlands.GroupScheme.Rational.VectorCoordinateRealization
import Langlands.GroupScheme.Rational.VectorGroupDimension

/-! # Detecting a positive vector factor with a pointed family -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorFactorPointedFamilies

variable {B : Scheme.{u}}

/-- Include the first group factor with the second coordinate at its unit. -/
def leftInclusion (V W : GroupScheme B) : V ⟶ V ⊗ W :=
  lift (𝟙 V) (0 : V ⟶ W)

/-- The inclusion is closed if the second factor is separated over the base. -/
theorem isClosedSubgroup_leftInclusion (V W : GroupScheme B)
    [IsSeparated W.X.hom] : IsClosedSubgroup (leftInclusion V W) := by
  have h : (leftInclusion V W).hom.hom.left ≫ (fst V.X W.X).left = 𝟙 _ :=
    congrArg (fun f => f.left) (lift_fst (𝟙 V.X) (1 : V.X ⟶ W.X))
  have : IsSeparated (fst V.X W.X).left := by
    change IsSeparated (pullback.fst V.X.hom W.X.hom)
    infer_instance
  have : IsClosedImmersion
      ((leftInclusion V W).hom.hom.left ≫ (fst V.X W.X).left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (fst V.X W.X).left

section Field

variable {k : Type u} [Field k]
    {G U V W : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}

/-- Every positive-dimensional vector group contains an actual closed vector line. -/
theorem exists_closed_vectorLine (hV : RelativeRoot.IsVectorGroupOfDimension V d)
    (hd : 0 < d) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ V),
      IsClosedSubgroup j ∧ RelativeRoot.IsVectorGroupOfDimension L 1 := by
  let : IsAffineHom V.X.hom := hV.isAffineHom
  obtain ⟨e, he⟩ := hV
  let a : Fin d := ⟨0, hd⟩
  let I : Set (Fin d) := {a}
  let σ : Fin 1 ≃ I := {
    toFun := fun _ => ⟨a, Set.mem_singleton a⟩
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun x => by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp x.property).symm }
  exact ⟨VectorGroup.groupScheme (CommRingCat.of k) 1,
    RelativeRoot.vectorCoordinateBlockInclusion e I σ he,
    RelativeRoot.isClosedSubgroup_vectorCoordinateBlockInclusion e I σ he,
    VectorGroup.coordinates (CommRingCat.of k) 1,
    VectorGroup.isNaturalVectorCoordinates⟩

/-- A nontrivial pointed family detects positive dimension of a vector factor
when its other projection becomes affine-line rigid over the separable closure. -/
theorem vector_dimension_pos
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    [Smooth G.X.hom] [IsSeparated W.X.hom]
    (e : U ≅ V ⊗ W) (hV : RelativeRoot.IsVectorGroupOfDimension V d)
    (hW : HasConstantAffineLineMaps
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj W))
    (n : ℕ) (f : PointedCommutatorFamily.source G
      (AffineLine.scheme (Spec (CommRingCat.of k))) n ⟶ U.X)
    (hf : f ≠ 1)
    (h₀ : PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫ f = 1) : 0 < d := by
  have hs : PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫
        (f ≫ e.hom.hom.hom ≫ snd V.X W.X) = 1 := by
    change PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫ f ≫ (e.hom ≫ snd V W).hom.hom = 1
    rw [← Category.assoc, h₀, MonObj.one_comp]
  have hw : f ≫ e.hom.hom.hom ≫ snd V.X W.X = 1 :=
    PointedCommutatorFamily.family_eq_one_of_sepClosed_extension_of_rationalPointStatement
      (K := SeparableClosure k) hP hW n _ hs
  by_contra hd
  have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
  subst d
  have hv : f ≫ e.hom.hom.hom ≫ fst V.X W.X = 1 :=
    hV.eq_one_of_dim_zero _
  apply hf
  apply (cancel_mono e.hom.hom.hom).mp
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, MonObj.one_comp] using hv
  · simpa only [Category.assoc, MonObj.one_comp] using hw

end Field

end VectorFactorPointedFamilies

end Langlands.GroupScheme
