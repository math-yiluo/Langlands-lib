import Langlands.GroupScheme.Rational.SubgroupProductOrbit
import Langlands.GroupScheme.Torus.SplitSolvableProof
import Langlands.GroupScheme.MatrixRepresentation.CommonFixedVector
import Langlands.GroupScheme.UnipotentAffineOrbitClosedProof
import Langlands.GroupScheme.HomogeneousQuotientDimension

/-! # Geometry and dimensions of actual subgroup-product orbits -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SubgroupProductOrbit

variable {k : Type u} [Field k]

/-- Products of affine unipotent groups are unipotent on all scheme tests. -/
theorem isUnipotent_tensor
    (V C : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom V.X.hom] [IsAffineHom C.X.hom]
    (hV : IsUnipotent V) (hC : IsUnipotent C) : IsUnipotent (V ⊗ C) := by
  let i : V ⟶ V ⊗ C := lift (𝟙 V) (0 : V ⟶ C)
  let r : C ⟶ V ⊗ C := lift (0 : C ⟶ V) (𝟙 C)
  have hAffV : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have hAffC : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  intro n _ _ _ ρ
  obtain ⟨v, hv, hi, hr⟩ := ρ.exists_common_fixedVector i r
    (splitSeries_product_inclusion_normal V C) hAffV hAffC hV hC
  refine ⟨v, hv, ?_⟩
  intro T x
  let a : T ⟶ (V ⊗ C).X := (x ≫ fst V.X C.X) ≫ i.hom.hom
  let b : T ⟶ (V ⊗ C).X := (x ≫ snd V.X C.X) ≫ r.hom.hom
  have hx : x =
      a * b := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [a, b, i, r, MonObj.mul_comp, Grp.lift_hom, Mon.lift_hom,
        Category.assoc, lift_fst, lift_snd, Grp.id_hom_hom,
        Category.comp_id, Grp.zero_hom, Mon.zero_hom, ← Hom.one_def,
        MonObj.comp_one, mul_one, one_mul]
  rw [hx, map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    ← MatrixRepresentation.pointMatrix_restrict ρ r, hr T (x ≫ snd V.X C.X)]
  exact hi T (x ≫ fst V.X C.X)

/-- For a smooth connected affine group the actual Lie dimension is its
constant smooth relative dimension. -/
theorem smoothOfRelativeDimension_lie_dimension
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    SmoothOfRelativeDimension (Lie.dimension G) G.X.hom := by
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom inferInstance inferInstance
  rwa [Lie.dimension_eq_of_smoothOfRelativeDimension G hd]

/-- The dimension of the actual binary product is the sum of the dimensions. -/
theorem lie_dimension_tensor
    (V C : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth V.X.hom] [IsAffineHom V.X.hom] [ConnectedSpace V.X.left]
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    [IsAffineHom (V ⊗ C).X.hom] :
    Lie.dimension (V ⊗ C) = Lie.dimension V + Lie.dimension C := by
  let : SmoothOfRelativeDimension (Lie.dimension V) V.X.hom :=
    smoothOfRelativeDimension_lie_dimension V
  let : SmoothOfRelativeDimension (Lie.dimension C) C.X.hom :=
    smoothOfRelativeDimension_lie_dimension C
  let : SmoothOfRelativeDimension (Lie.dimension C)
      (pullback.fst V.X.hom C.X.hom) :=
    MorphismProperty.pullback_fst V.X.hom C.X.hom inferInstance
  have hd : SmoothOfRelativeDimension (Lie.dimension C + Lie.dimension V)
      (V ⊗ C).X.hom := by
    change SmoothOfRelativeDimension _ (pullback.fst V.X.hom C.X.hom ≫ V.X.hom)
    infer_instance
  rw [Lie.dimension_eq_of_smoothOfRelativeDimension (V ⊗ C) hd, Nat.add_comm]

/-- The actual Lie dimension is unchanged by any extension of the ground field. -/
theorem lie_dimension_baseChange
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom] :
    Lie.dimension ((GroupScheme.baseChange b).obj G) = Lie.dimension G := by
  let : SmoothOfRelativeDimension (Lie.dimension G) G.X.hom :=
    smoothOfRelativeDimension_lie_dimension G
  apply Lie.dimension_eq_of_smoothOfRelativeDimension
  change SmoothOfRelativeDimension _ (pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd G.X.hom b inferInstance

section ClosedOrbit

variable [IsAlgClosed k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]

/-- The orbit of the actual product of two affine unipotent groups is closed. -/
theorem isClosed_range_orbitMap (j : V ⟶ U) (c : C ⟶ U)
    (hV : IsUnipotent V) (hC : IsUnipotent C) :
    IsClosed (Set.range ((action j c).orbitMap 1).left) := by
  let : Smooth (V ⊗ C).X.hom :=
    prop_tensor_hom (@Smooth) V.X C.X inferInstance inferInstance
  let : IsAffineHom (V ⊗ C).X.hom :=
    prop_tensor_hom (@IsAffineHom) V.X C.X inferInstance inferInstance
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  exact unipotentAffineOrbitClosed k (V ⊗ C) (isUnipotent_tensor V C hV hC)
    U.X (action j c) 1

/-- Unipotence discharges the closed-orbit premise of the actual product
homogeneous quotient. -/
def unipotentClosedOrbitQuotient (j : V ⟶ U) (c : C ⟶ U)
    (hc : IsClosedSubgroup c) (hV : IsUnipotent V) (hC : IsUnipotent C)
    (hE : Smooth (subgroupIntersection j c).X.hom) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient
      (intersectionDiagonal j c) :=
  closedOrbitQuotient j c hc hE (isClosed_range_orbitMap j c hV hC)

end ClosedOrbit

end Langlands.GroupScheme.SubgroupProductOrbit
