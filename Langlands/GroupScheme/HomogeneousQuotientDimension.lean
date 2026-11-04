import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof

/-! # Dimensions of actual smooth homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open scoped CategoryTheory.MonObj

namespace Langlands

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The underlying point of a rational section over a field is closed. -/
theorem isClosed_singleton_section_point
    (X : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    IsClosed ({e.left (IsLocalRing.closedPoint k)} : Set X.left) := by
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : IsClosedImmersion e.left :=
    isClosedImmersion_of_comp_eq_id X.hom e.left (Over.w e)
  have hrange : Set.range e.left = {e.left (IsLocalRing.closedPoint k)} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg e.left (Subsingleton.elim y (IsLocalRing.closedPoint k))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint k, rfl⟩
  rw [← hrange]
  exact e.left.isClosedEmbedding.isClosed_range

/-- A rational point bounds the constant smooth relative dimension by the
topological dimension of the scheme. -/
theorem relativeDimension_cast_le_topologicalKrullDim_of_section
    (X : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    {d : ℕ} (hd : SmoothOfRelativeDimension d X.hom) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim X.left := by
  have heq := fieldSmoothClosedPointStalkDimension k X.left X.hom d hd
    (e.left (IsLocalRing.closedPoint k)) (isClosed_singleton_section_point X e)
  rw [← heq, ringKrullDim_stalk_eq_coheight, topologicalKrullDim]
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X.left)).symm]
  exact coheight_le_krullDim _

end AlgebraicGeometry

namespace GroupScheme

namespace Lie

variable {k : Type u} [Field k]

/-- The actual Lie dimension equals every supplied constant smooth relative
dimension of an affine group over a field. -/
theorem dimension_eq_of_smoothOfRelativeDimension
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    {d : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom) :
    dimension G = d := by
  have : SmoothOfRelativeDimension d G.X.hom := hd
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  have heq := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
    k G.X.left G.X.hom d hd (e.left (IsLocalRing.closedPoint k))
    (Langlands.AlgebraicGeometry.isClosed_singleton_section_point G.X e)
  have h := (finrank_kernel_cast_eq_ringKrullDim G).trans heq
  exact_mod_cast h

end Lie

namespace HomogeneousQuotient

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)

/-- Constant smooth dimensions of a supplied actual homogeneous quotient,
including their composition on the ambient group. -/
structure DimensionData (i : P ⟶ G) (q : G.X ⟶ Q) where
  fiberDimension : ℕ
  quotientDimension : ℕ
  subgroup : SmoothOfRelativeDimension fiberDimension P.X.hom
  projection : SmoothOfRelativeDimension fiberDimension q.left
  quotient : SmoothOfRelativeDimension quotientDimension Q.hom
  ambient : SmoothOfRelativeDimension (fiberDimension + quotientDimension) G.X.hom

/-- Constant dimensions for every smooth surjective exact homogeneous quotient
of a smooth connected group over an arbitrary field. -/
def dimensionData
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [Mono i.hom.hom] [Smooth q.left] [Surjective q.left] :
    DimensionData i q := Classical.choice (by
  have : Smooth (q.left ≫ Q.hom) := by
    rw [Over.w q]
    infer_instance
  have : Smooth Q.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.left Q.hom
  have : ConnectedSpace Q.left :=
    q.left.surjective.connectedSpace q.left.continuous
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left Q.left q.left inferInstance inferInstance
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    Q.left (Spec (CommRingCat.of k)) Q.hom inferInstance inferInstance
  have : SmoothOfRelativeDimension n q.left := hn
  have : SmoothOfRelativeDimension d Q.hom := hd
  let F := Dynamic.flagQuotientFiber G q (identityCoset G q)
  have : SmoothOfRelativeDimension n F.hom := by
    change SmoothOfRelativeDimension n (pullback.snd q.left (identityCoset G q).left)
    set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.pullback_snd q.left (identityCoset G q).left hn
  let e := subgroupIdentityFiberIso G P i q hfib
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hP : SmoothOfRelativeDimension n P.X.hom := by
    rw [← Over.w e.hom]
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (e.hom.left ≫ F.hom))
  have hG : SmoothOfRelativeDimension (n + d) G.X.hom := by
    rw [← Over.w q]
    infer_instance
  exact ⟨⟨n, d, hP, hn, hd, hG⟩⟩)

variable {i q}

/-- The exact Lie-dimension formula for a supplied constant-dimension datum. -/
theorem DimensionData.lie_dimension_eq
    [IsAffineHom G.X.hom] [IsAffineHom P.X.hom] (D : DimensionData i q) :
    Lie.dimension G = Lie.dimension P + D.quotientDimension := by
  rw [Lie.dimension_eq_of_smoothOfRelativeDimension G D.ambient,
    Lie.dimension_eq_of_smoothOfRelativeDimension P D.subgroup]

/-- The quotient dimension in the datum is bounded by the actual target
scheme's topological Krull dimension. -/
theorem DimensionData.quotientDimension_cast_le
    (D : DimensionData i q) :
    (D.quotientDimension : WithBot ℕ∞) ≤ topologicalKrullDim Q.left :=
  Langlands.AlgebraicGeometry.relativeDimension_cast_le_topologicalKrullDim_of_section
    Q (identityCoset G q) D.quotient

variable (i q)

/-- An actual smooth exact homogeneous quotient of dimension at most one
gives an ambient Lie-dimension gap of at most one. -/
theorem lie_dimension_le_add_one_of_dimension_le_one
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom G.X.hom] [IsAffineHom P.X.hom]
    [Mono i.hom.hom] [Smooth q.left] [Surjective q.left]
    (hQ : topologicalKrullDim Q.left ≤ 1) :
    Lie.dimension G ≤ Lie.dimension P + 1 := by
  let D := dimensionData i q hfib
  have hd : D.quotientDimension ≤ 1 := by
    have h := D.quotientDimension_cast_le.trans hQ
    exact_mod_cast h
  rw [D.lie_dimension_eq]
  omega

end HomogeneousQuotient

end GroupScheme

end Langlands
