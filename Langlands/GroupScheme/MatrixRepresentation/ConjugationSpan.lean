import Langlands.GroupScheme.GeneralLinearCoordinateConjugation
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability

/-! # The conjugation representation on a dense subgroup's coordinate span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Ambient

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual conjugation representation on matrix and inverse-matrix coordinates. -/
def coordinateConjugation (ρ : MatrixRepresentation G n) :
    MatrixRepresentation G (GeneralLinear.Coordinate n) :=
  ρ ≫ GeneralLinear.coordinateConjugationHom n R

@[simp] theorem coordinateConjugation_pointMatrix (ρ : MatrixRepresentation G n)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    ρ.coordinateConjugation.pointMatrix T x =
      GeneralLinear.conjCoordsHom n Γ(T.left, ⊤) (ρ.pointMatrix T x) := by
  simpa only [pointMatrix_apply, coordinateConjugation, Grp.comp_hom_hom,
    Category.assoc] using
    GeneralLinear.pointsEquiv_coordinateConjugationHom n R T (x ≫ ρ.hom.hom)

@[simp] theorem coordinateConjugation_rationalMatrix (ρ : MatrixRepresentation G n)
    (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    ρ.coordinateConjugation.rationalMatrix x =
      GeneralLinear.conjCoordsHom n R (ρ.rationalMatrix x) := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom
    (ρ.coordinateConjugation.pointMatrix _ x) = _
  rw [coordinateConjugation_pointMatrix]
  exact (GeneralLinear.conjCoordsHom_map n
    (Scheme.ΓSpecIso R).hom.hom (ρ.pointMatrix _ x)).symm

/-- On coordinate values, the rational action is conjugation in the original group. -/
theorem coordinateConjugation_rationalMatrix_mulVec_values
    (ρ : MatrixRepresentation G n)
    (x y : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    (ρ.coordinateConjugation.rationalMatrix x :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) R) *ᵥ
        GeneralLinear.values (ρ.rationalMatrix y) =
      GeneralLinear.values (ρ.rationalMatrix (x * y * x⁻¹)) := by
  rw [coordinateConjugation_rationalMatrix,
    GeneralLinear.conjCoordsHom_mulVec_values, map_mul, map_mul, map_inv]

end Ambient

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The span of the faithful matrix and inverse-matrix values of a rational subgroup.
No faithfulness assumption is needed to define this space. -/
def subgroupCoordinateSpan (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) :
    Submodule k (GeneralLinear.Coordinate n → k) :=
  Submodule.span k (Set.range fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val))

/-- A normalizer element preserves the set of coordinate values of the subgroup. -/
theorem coordinateConjugation_mapsTo_subgroupValues (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hg : g ∈ Subgroup.normalizer (H : Set _)) :
    Set.MapsTo
      (ρ.coordinateConjugation.rationalMatrix g :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k).mulVec
      (Set.range fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val))
      (Set.range fun h : H => GeneralLinear.values (ρ.rationalMatrix h.val)) := by
  rintro v ⟨h, rfl⟩
  rw [coordinateConjugation_rationalMatrix_mulVec_values]
  exact ⟨⟨g * h.val * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h.val).mp h.property⟩, rfl⟩

/-- A normalizer element preserves the entire coordinate span. -/
theorem coordinateConjugation_mem_subgroupCoordinateSpan
    (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hg : g ∈ Subgroup.normalizer (H : Set _))
    {v : GeneralLinear.Coordinate n → k} (hv : v ∈ ρ.subgroupCoordinateSpan H) :
    (ρ.coordinateConjugation.rationalMatrix g :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) *ᵥ v ∈
      ρ.subgroupCoordinateSpan H := by
  let L := (ρ.coordinateConjugation.rationalMatrix g :
    Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k).mulVecLin
  change L v ∈ ρ.subgroupCoordinateSpan H
  induction hv using Submodule.span_induction with
  | mem v hv =>
    exact Submodule.subset_span (coordinateConjugation_mapsTo_subgroupValues ρ H hg hv)
  | zero => simpa only [map_zero] using (ρ.subgroupCoordinateSpan H).zero_mem
  | add v w _ _ hv hw =>
    simpa only [map_add] using (ρ.subgroupCoordinateSpan H).add_mem hv hw
  | smul a v _ hv =>
    simpa only [map_smul] using (ρ.subgroupCoordinateSpan H).smul_mem a hv

/-- An actual representation on the subgroup coordinate span, with split coordinates. -/
structure ConjugationSubrepresentation (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  inclusion : Matrix (GeneralLinear.Coordinate n) (Fin dimension) k
  retraction : Matrix (Fin dimension) (GeneralLinear.Coordinate n) k
  left_inverse : retraction * inclusion = 1
  columns_mem : ∀ j, (fun r => inclusion r j) ∈ ρ.subgroupCoordinateSpan H
  projection : ∀ v, v ∈ ρ.subgroupCoordinateSpan H →
    (inclusion * retraction) *ᵥ v = v
  intertwines : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    (ρ.coordinateConjugation.pointMatrix T x :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) Γ(T.left, ⊤)) *
        inclusion.map (scalarMap T) =
      inclusion.map (scalarMap T) *
        (representation.pointMatrix T x : Matrix (Fin dimension) (Fin dimension) Γ(T.left, ⊤))
  rationalMatrix_eq : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
    (representation.rationalMatrix x : Matrix (Fin dimension) (Fin dimension) k) =
      retraction * (ρ.coordinateConjugation.rationalMatrix x :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) * inclusion

/-- Density of the subgroup extends its invariant coordinate span to an actual
representation on every scheme test. -/
theorem nonempty_conjugationSubrepresentation [IsReduced G.X.left]
    (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype) :
    Nonempty (ConjugationSubrepresentation ρ H) := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    exists_subspace_split_coordinates (ρ.subgroupCoordinateSpan H)
  have hstable : ρ.coordinateConjugation.IsStableCoordinates B C := by
    apply isStableCoordinates_of_denseRationalMatrix ρ.coordinateConjugation B C H.subtype hH
    intro h
    change (ρ.coordinateConjugation.rationalMatrix h.val :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) * B =
      B * (C * (ρ.coordinateConjugation.rationalMatrix h.val :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) * B)
    have hmat : (B * C) *
        ((ρ.coordinateConjugation.rationalMatrix h.val :
          Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) * B) =
        (ρ.coordinateConjugation.rationalMatrix h.val :
          Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k) * B := by
      ext r s
      exact congrFun (hproj _ (coordinateConjugation_mem_subgroupCoordinateSpan ρ H
        (Subgroup.le_normalizer h.property) (hcols s))) r
    simpa only [Matrix.mul_assoc] using hmat.symm
  let σ := restrictCoordinates ρ.coordinateConjugation B C hCB hstable
  refine ⟨⟨d, σ, B, C, hCB, hcols, hproj,
    restrictCoordinates_intertwines ρ.coordinateConjugation B C hCB hstable, ?_⟩⟩
  intro x
  change (σ.pointMatrix _ x :
    Matrix (Fin d) (Fin d) Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = _
  rw [restrictCoordinates_pointMatrix]
  change (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))) *
    (ρ.coordinateConjugation.pointMatrix _ x :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n)
        Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) * B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = _
  rw [Matrix.map_mul, Matrix.map_mul]
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = B := by
    ext r s
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = C := by
    ext r s
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.apply_symm_apply _
  rw [hB, hC]
  rfl

/-- A chosen actual representation on the coordinate span of a dense rational subgroup. -/
def conjugationSubrepresentation [IsReduced G.X.left]
    (ρ : MatrixRepresentation G n)
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype) :
    ConjugationSubrepresentation ρ H :=
  Classical.choice (nonempty_conjugationSubrepresentation ρ H hH)

end Langlands.GroupScheme.MatrixRepresentation
