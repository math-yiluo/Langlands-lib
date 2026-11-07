import Langlands.AlgebraicGeometry.SmoothPureDimensionStatement
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension

/-! # From smooth chart dimension to actual pure fibre dimension -/

noncomputable section

universe u

open Set Order Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open SchemeFiberGeometry

private theorem stalk_dimension_le (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  change (coheight x : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds X)
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]
  exact coheight_le_krullDim _

private theorem fieldSmooth_dimension_eq
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [CompactSpace X] [Nonempty X] :
    topologicalKrullDim X = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · exact fieldSmoothTopologicalKrullDim k X f n inferInstance inferInstance
  · obtain ⟨x, _, hx⟩ := isClosed_univ.exists_closed_singleton
      (show (univ : Set X).Nonempty from Set.univ_nonempty)
    rw [← fieldSmoothClosedPointStalkDimension k X f n inferInstance x hx]
    exact stalk_dimension_le X x

private theorem smooth_dimension_sourceOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] (U : X.Opens) :
    SmoothOfRelativeDimension n (U.ι ≫ f) := by
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))

/-- Fixed smooth chart dimension is the actual local topological dimension
at every point, with no compactness assumption on the scheme. -/
theorem fieldSmooth_topologicalKrullDimAt
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    topologicalKrullDimAt x = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let : IsAffine V.toScheme := hV
    let := smooth_dimension_sourceOpen f n V
    exact (topologicalKrullDimAt_le_open x V hxV).trans
      (fieldSmoothTopologicalKrullDim k V.toScheme (V.ι ≫ f) n
        inferInstance inferInstance)
  · obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_at x
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    let : IsAffine V.toScheme := hV
    let : Nonempty V.toScheme := ⟨⟨x, hxV⟩⟩
    let := smooth_dimension_sourceOpen f n V
    calc
      (n : WithBot ℕ∞) = topologicalKrullDim V :=
        (fieldSmooth_dimension_eq k V.toScheme (V.ι ≫ f) n).symm
      _ ≤ topologicalKrullDim U :=
        (Topology.IsEmbedding.inclusion hVU).isInducing.topologicalKrullDim_le
      _ = topologicalKrullDimAt x := hU

/-- The field and actual residue-fibre comparisons, exactly as stated. -/
theorem smoothPureDimension : SmoothPureDimensionStatement.{u} := by
  have hfield : FieldSmoothPureDimensionStatement.{u} := by
    intro k _ X f n hf
    let := hf
    let : Smooth f := SmoothOfRelativeDimension.smooth n f
    exact (hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType
      k X f n).mpr (fieldSmooth_topologicalKrullDimAt k X f n)
  refine ⟨hfield, ?_⟩
  intro X Y f n hf y
  let := hf
  let : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hdim : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) hf
  exact hfield (Y.residueField y) (f.fiber y) (f.fiberToSpecResidueField y) n hdim

end Langlands.AlgebraicGeometry
