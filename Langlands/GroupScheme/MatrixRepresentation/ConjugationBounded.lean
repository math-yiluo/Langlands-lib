import Langlands.GroupScheme.MatrixRepresentation.ConjugationSpan
import Langlands.GroupScheme.Rational.SpectralFamilyBound
import Langlands.GroupScheme.BoundedSubgroupStableLatticeStatement
import Langlands.LinearAlgebra.BoundedSpanningAction

/-! # Bounded normalizer action on the subgroup coordinate span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {H : Subgroup (rationalPoints G)}

namespace ConjugationSubrepresentation

/-- The original subgroup coordinate vectors expressed in the split coordinates. -/
def subgroupVectors (S : ConjugationSubrepresentation ρ H) :
    Set (Fin S.dimension → F) :=
  Set.range fun h : H => S.retraction *ᵥ GeneralLinear.values (ρ.rationalMatrix h.val)

/-- Retraction of the original generators spans the entire restricted coordinate space. -/
theorem subgroupVectors_span (S : ConjugationSubrepresentation ρ H) :
    Submodule.span F S.subgroupVectors = ⊤ := by
  classical
  have hmap : Submodule.span F S.subgroupVectors =
      (ρ.subgroupCoordinateSpan H).map S.retraction.mulVecLin := by
    rw [subgroupCoordinateSpan, Submodule.map_span]
    congr 1
    exact Set.range_comp S.retraction.mulVecLin
      (fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val))
  rw [hmap]
  apply top_unique
  rw [← (Pi.basisFun F (Fin S.dimension)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨(fun r => S.inclusion r j), S.columns_mem j, ?_⟩
  simp only [Pi.basisFun_apply, Matrix.mulVecLin_apply]
  change S.retraction *ᵥ S.inclusion.col j = Pi.single j 1
  rw [← Matrix.mulVec_single_one S.inclusion j, Matrix.mulVec_mulVec,
    S.left_inverse, Matrix.one_mulVec]

/-- Every normalizer element preserves the retracted subgroup generators. -/
theorem mapsTo_subgroupVectors (S : ConjugationSubrepresentation ρ H)
    {g : rationalPoints G} (hg : g ∈ Subgroup.normalizer (H : Set _)) :
    Set.MapsTo (S.representation.rationalMatrix g :
      Matrix (Fin S.dimension) (Fin S.dimension) F).mulVec
      S.subgroupVectors S.subgroupVectors := by
  rintro _ ⟨h, rfl⟩
  refine ⟨⟨g * h.val * g⁻¹,
    (Subgroup.mem_normalizer_iff.mp hg h.val).mp h.property⟩, ?_⟩
  symm
  rw [S.rationalMatrix_eq]
  calc
    (S.retraction * (ρ.coordinateConjugation.rationalMatrix g :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) F) *
          S.inclusion) *ᵥ
        (S.retraction *ᵥ GeneralLinear.values (ρ.rationalMatrix h.val)) =
      S.retraction *ᵥ ((ρ.coordinateConjugation.rationalMatrix g :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) F) *ᵥ
          ((S.inclusion * S.retraction) *ᵥ
            GeneralLinear.values (ρ.rationalMatrix h.val))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = S.retraction *ᵥ
        GeneralLinear.values (ρ.rationalMatrix (g * h.val * g⁻¹)) := by
      rw [S.projection _ (Submodule.subset_span ⟨h, rfl⟩),
        coordinateConjugation_rationalMatrix_mulVec_values]

variable [ValuativeRel F] [IsAffine G.X.left]

/-- Algebraic boundedness of the subgroup bounds each retracted coordinate. -/
theorem subgroupVectors_bounded (S : ConjugationSubrepresentation ρ H)
    (hH : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))) :
    ∀ i, ∃ b : F, b ≠ 0 ∧ ∀ x ∈ S.subgroupVectors, x i ≤ᵥ b := by
  classical
  have he := ρ.hasBoundedRationalEntries_of_isAlgebraicallyBounded
    (H : Set (rationalPoints G)) hH
  let e : H → (H → F) →ₐ[F] F := fun h => Pi.evalAlgHom F (fun _ => F) h
  have hvalues : ∀ κ : GeneralLinear.Coordinate n,
      (fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val) κ) ∈
        boundedEvaluationSubalgebra e := by
    intro κ
    cases κ with
    | entry i j =>
      obtain ⟨b, hb, h⟩ := he i j
      exact ⟨b, hb, fun h' => h h'.val h'.property⟩
    | inverseEntry i j =>
      obtain ⟨b, hb, h⟩ := he i j
      refine ⟨b, hb, fun h' => ?_⟩
      change (ρ.rationalMatrix h'.val)⁻¹ i j ≤ᵥ b
      simpa only [map_inv] using h h'.val⁻¹ (H.inv_mem h'.property)
  intro i
  have hlin :
      (fun h : H => (S.retraction *ᵥ GeneralLinear.values (ρ.rationalMatrix h.val)) i) ∈
        boundedEvaluationSubalgebra e := by
    have heq :
        (fun h : H => (S.retraction *ᵥ GeneralLinear.values (ρ.rationalMatrix h.val)) i) =
          ∑ κ : GeneralLinear.Coordinate n,
            S.retraction i κ • (fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val) κ) := by
      ext h
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Subalgebra.sum_mem _ fun κ _ =>
      (boundedEvaluationSubalgebra e).smul_mem (hvalues κ) _
  obtain ⟨b, hb, h⟩ := hlin
  refine ⟨b, hb, ?_⟩
  rintro _ ⟨h', rfl⟩
  exact h h'

/-- The whole normalizer family has uniformly bounded restricted matrix entries. -/
theorem hasBoundedRationalEntries_normalizer (S : ConjugationSubrepresentation ρ H)
    (hH : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))) :
    S.representation.HasBoundedRationalEntries
      (↑(Subgroup.normalizer (H : Set (rationalPoints G))) : Set (rationalPoints G)) := by
  obtain ⟨b, hb, h⟩ := Langlands.LinearAlgebra.exists_valuative_bound_entries_of_mapsTo_spanning
    S.subgroupVectors S.subgroupVectors_span (S.subgroupVectors_bounded hH)
    (fun g : Subgroup.normalizer (H : Set _) =>
      (S.representation.rationalMatrix g.val :
        Matrix (Fin S.dimension) (Fin S.dimension) F))
    (fun g => S.mapsTo_subgroupVectors g.property)
  exact fun i j => ⟨b, hb, fun g hg => h ⟨g, hg⟩ i j⟩

local instance conjugationBoundedAffineGL (S : ConjugationSubrepresentation ρ H) :
    IsAffine (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin S.dimension) (CommRingCat.of F)

/-- The actual restricted conjugation image of the normalizer is algebraically bounded. -/
theorem isAlgebraicallyBounded_normalizer_image (S : ConjugationSubrepresentation ρ H)
    (hH : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))) :
    IsAlgebraicallyBounded F
      (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X
      ((fun g : rationalPoints G => g ≫ S.representation.hom.hom) ''
        (↑(Subgroup.normalizer (H : Set (rationalPoints G))) : Set (rationalPoints G))) :=
  S.representation.isAlgebraicallyBounded_image_of_entries _
    (fun _ hg => (Subgroup.normalizer (H : Set (rationalPoints G))).inv_mem hg)
    (S.hasBoundedRationalEntries_normalizer hH)

end ConjugationSubrepresentation

/-- A bounded subgroup has bounded normalizer image in its actual split-span action. -/
def ConjugationBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (n : Type) [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (H : Subgroup (rationalPoints G))
    (S : ConjugationSubrepresentation ρ H),
    IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)) →
      @IsAlgebraicallyBounded F _
        (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X
        (GeneralLinear.isAffine_groupScheme (Fin S.dimension) (CommRingCat.of F)) _
        ((fun g : rationalPoints G => g ≫ S.representation.hom.hom) ''
          (↑(Subgroup.normalizer (H : Set (rationalPoints G))) : Set (rationalPoints G)))

/-- Boundedness of the normalizer's restricted conjugation image. -/
theorem conjugationBounded : ConjugationBoundedStatement.{u} := by
  intro F _ _ G _ n _ _ ρ H S hH
  exact S.isAlgebraicallyBounded_normalizer_image hH

end Langlands.GroupScheme.MatrixRepresentation
