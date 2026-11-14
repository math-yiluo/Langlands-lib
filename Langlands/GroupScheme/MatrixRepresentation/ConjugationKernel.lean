import Langlands.GroupScheme.MatrixRepresentation.ConjugationSpan
import Langlands.GroupScheme.Rational.Characters

/-! # The full scheme kernel of the dense-span conjugation representation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A projected vector of matrix and inverse-matrix values commutes with pullback. -/
theorem coordinateValuesProjection_naturality (ρ : MatrixRepresentation G n)
    (M : Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ G.X) :
    M.map (scalarMap T') *ᵥ GeneralLinear.values (ρ.pointMatrix T' (a ≫ x)) =
      fun r => a.left.appTop
        ((M.map (scalarMap T) *ᵥ GeneralLinear.values (ρ.pointMatrix T x)) r) := by
  have hM : M.map (scalarMap T') =
      (M.map (scalarMap T)).map a.left.appTop.hom := by
    ext r s
    exact (scalarMap_comp a _).symm
  rw [hM, pointMatrix_naturality, GeneralLinear.values_map]
  funext r
  exact (a.left.appTop.hom.map_mulVec _ _ r).symm

/-- A projection identity on a dense rational family holds on every scheme test. -/
theorem values_projection_of_denseRationalFamily [IsReduced G.X.left]
    (ρ : MatrixRepresentation G n)
    (M : Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) k)
    {I : Type v}
    (p : I → Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)
    (hp : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily p)
    (h : ∀ i, M *ᵥ GeneralLinear.values (ρ.rationalMatrix (p i)) =
      GeneralLinear.values (ρ.rationalMatrix (p i)))
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    M.map (scalarMap T) *ᵥ GeneralLinear.values (ρ.pointMatrix T x) =
      GeneralLinear.values (ρ.pointMatrix T x) := by
  have hbase (i : I) :
      M.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))) *ᵥ
          GeneralLinear.values (ρ.pointMatrix _ (p i)) =
        GeneralLinear.values (ρ.pointMatrix _ (p i)) := by
    rw [← map_rationalMatrix, GeneralLinear.values_map]
    funext r
    exact ((scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))).map_mulVec _ _ r).symm.trans
      (congrArg (fun z => scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (z r)) (h i))
  let f : G.X ⟶ coefficientSpace (GeneralLinear.Coordinate n) (CommRingCat.of k) :=
    coefficientPoint G.X
      (M.map (scalarMap G.X) *ᵥ GeneralLinear.values (ρ.pointMatrix G.X (𝟙 _)))
  let g : G.X ⟶ coefficientSpace (GeneralLinear.Coordinate n) (CommRingCat.of k) :=
    coefficientPoint G.X (GeneralLinear.values (ρ.pointMatrix G.X (𝟙 _)))
  have hsep : IsSeparated
      (coefficientSpace (GeneralLinear.Coordinate n) (CommRingCat.of k)).hom := by
    dsimp [coefficientSpace]
    infer_instance
  have he : f = g := by
    apply Langlands.AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPointFamily p hp
    intro i
    apply coefficientCoordinates_injective
    simp only [f, g, coefficientCoordinates_comp, coefficientCoordinates_coefficientPoint]
    have hf := ρ.coordinateValuesProjection_naturality M (p i) (𝟙 G.X)
    have hg := congrArg GeneralLinear.values (ρ.pointMatrix_naturality (p i) (𝟙 G.X))
    simp only [Category.comp_id, GeneralLinear.values_map] at hf hg
    exact hf.symm.trans ((hbase i).trans hg)
  have huniv := congrArg coefficientCoordinates he
  simp only [f, g, coefficientCoordinates_coefficientPoint] at huniv
  have hx := ρ.coordinateValuesProjection_naturality M x (𝟙 G.X)
  have hv := congrArg GeneralLinear.values (ρ.pointMatrix_naturality x (𝟙 G.X))
  simp only [Category.comp_id, GeneralLinear.values_map] at hx hv
  exact hx.trans ((congrArg (fun z => fun r => x.left.appTop (z r)) huniv).trans hv.symm)

variable {H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)}
  {ρ : MatrixRepresentation G n}

namespace ConjugationSubrepresentation

/-- Every point's coordinate values lie in the scalar-extended split span. -/
theorem values_projection [IsReduced G.X.left]
    (S : ConjugationSubrepresentation ρ H)
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (S.inclusion * S.retraction).map (scalarMap T) *ᵥ
        GeneralLinear.values (ρ.pointMatrix T x) =
      GeneralLinear.values (ρ.pointMatrix T x) := by
  apply values_projection_of_denseRationalFamily ρ _ H.subtype hH
  intro h
  exact S.projection _ (Submodule.subset_span (Set.mem_range_self h))

/-- A point acting trivially on the restricted span commutes with every point. -/
theorem commute_of_pointMatrix_eq_one [IsReduced G.X.left] [Mono ρ.hom.hom]
    (S : ConjugationSubrepresentation ρ H)
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X)
    (hx : S.representation.pointMatrix T x = 1) : Commute x y := by
  have hfix := S.intertwines T x
  rw [hx, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] at hfix
  have hproj := S.values_projection hH T y
  rw [Matrix.map_mul] at hproj
  have ha :
      (ρ.coordinateConjugation.pointMatrix T x :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) Γ(T.left, ⊤)) *ᵥ
          GeneralLinear.values (ρ.pointMatrix T y) =
        GeneralLinear.values (ρ.pointMatrix T y) := by
    calc
      _ = (ρ.coordinateConjugation.pointMatrix T x :
            Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) Γ(T.left, ⊤)) *ᵥ
          ((S.inclusion.map (scalarMap T) * S.retraction.map (scalarMap T)) *ᵥ
            GeneralLinear.values (ρ.pointMatrix T y)) := congrArg _ hproj.symm
      _ = _ := by
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hfix]
        exact hproj
  have he : x * y * x⁻¹ = y := by
    apply ρ.pointMatrix_injective T
    apply GeneralLinear.values_injective
    simpa only [coordinateConjugation_pointMatrix,
      GeneralLinear.conjCoordsHom_mulVec_values, map_mul, map_inv] using ha
  change x * y = y * x
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun z => z * x) he

/-- The point kernel is contained in the full scheme center, including all pullbacks. -/
theorem mem_center_of_pointMatrix_eq_one [IsReduced G.X.left] [Mono ρ.hom.hom]
    (S : ConjugationSubrepresentation ρ H)
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype)
    {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ G.X}
    (hx : S.representation.pointMatrix T x = 1) :
    x ∈ (center G).carrier T := by
  intro T' a y
  apply S.commute_of_pointMatrix_eq_one hH T' (a ≫ x) y
  rw [pointMatrix_naturality, hx, map_one]

/-- Central points fix the scalar extension of the whole subgroup coordinate span. -/
theorem fixes_span_of_mem_center (_S : ConjugationSubrepresentation ρ H)
    {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ G.X}
    (hx : x ∈ (center G).carrier T)
    {v : GeneralLinear.Coordinate n → k} (hv : v ∈ ρ.subgroupCoordinateSpan H) :
    (ρ.coordinateConjugation.pointMatrix T x :
      Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) Γ(T.left, ⊤)) *ᵥ
        (fun r => scalarMap T (v r)) = fun r => scalarMap T (v r) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, rfl⟩ := hv
    have hc := commute_of_mem_center hx
      (CategoryTheory.CartesianMonoidalCategory.toUnit T ≫ h.val)
    have he : x * (CategoryTheory.CartesianMonoidalCategory.toUnit T ≫ h.val) * x⁻¹ =
        CategoryTheory.CartesianMonoidalCategory.toUnit T ≫ h.val := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hm := congrArg (fun z => GeneralLinear.values (ρ.pointMatrix T z)) he
    change _ *ᵥ ((scalarMap T) ∘ GeneralLinear.values (ρ.rationalMatrix h.val)) =
      (scalarMap T) ∘ GeneralLinear.values (ρ.rationalMatrix h.val)
    rw [← GeneralLinear.values_map, ← pointMatrix_constant,
      coordinateConjugation_pointMatrix, GeneralLinear.conjCoordsHom_mulVec_values]
    simpa only [map_mul, map_inv] using hm
  | zero =>
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero _
  | add v w _ _ hv hw =>
    have he : (fun r => scalarMap T ((v + w) r)) =
        (fun r => scalarMap T (v r)) + (fun r => scalarMap T (w r)) := by
      funext r
      exact map_add _ _ _
    rw [he, Matrix.mulVec_add, hv, hw]
  | smul a v _ hv =>
    have he : (fun r => scalarMap T ((a • v) r)) =
        scalarMap T a • (fun r => scalarMap T (v r)) := by
      funext r
      exact map_mul _ _ _
    rw [he, Matrix.mulVec_smul, hv]

/-- The full scheme center acts trivially on the restricted representation. -/
theorem pointMatrix_eq_one_of_mem_center (S : ConjugationSubrepresentation ρ H)
    {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ G.X}
    (hx : x ∈ (center G).carrier T) : S.representation.pointMatrix T x = 1 := by
  have hfix :
      (ρ.coordinateConjugation.pointMatrix T x :
        Matrix (GeneralLinear.Coordinate n) (GeneralLinear.Coordinate n) Γ(T.left, ⊤)) *
          S.inclusion.map (scalarMap T) = S.inclusion.map (scalarMap T) := by
    ext r s
    exact congrFun (S.fixes_span_of_mem_center hx (S.columns_mem s)) r
  have he := (S.intertwines T x).symm.trans hfix
  have hcb : S.retraction.map (scalarMap T) * S.inclusion.map (scalarMap T) = 1 := by
    rw [← Matrix.map_mul, S.left_inverse]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hh := congrArg (fun M => S.retraction.map (scalarMap T) * M) he
  rw [← Matrix.mul_assoc, hcb, Matrix.one_mul] at hh
  apply Units.ext
  exact hh

/-- The point kernel is exactly the full scheme center, on every scheme test. -/
theorem pointMatrix_eq_one_iff_mem_center [IsReduced G.X.left] [Mono ρ.hom.hom]
    (S : ConjugationSubrepresentation ρ H)
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype)
    {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ G.X} :
    S.representation.pointMatrix T x = 1 ↔ x ∈ (center G).carrier T :=
  ⟨S.mem_center_of_pointMatrix_eq_one hH, S.pointMatrix_eq_one_of_mem_center⟩

/-- The represented full scheme kernel has exactly the center range functor. -/
theorem range_kernel_eq_center [IsReduced G.X.left] [Mono ρ.hom.hom]
    (S : ConjugationSubrepresentation ρ H)
    (hH : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype) :
    SubgroupFunctor.range (kernelι S.representation) = center G := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, ← S.pointMatrix_eq_one_iff_mem_center hH]
  change x ≫ S.representation.hom.hom = 1 ↔
    GeneralLinear.pointsEquiv _ _ T (x ≫ S.representation.hom.hom) = 1
  rw [← map_one (GeneralLinear.pointsEquiv _ _ T), EmbeddingLike.apply_eq_iff_eq]

end ConjugationSubrepresentation

/-- The dense-span conjugation representation has the full scheme center as kernel. -/
def ConjugationKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsReduced G.X.left] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) [Mono ρ.hom.hom]
    (H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)),
    Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily H.subtype →
    ∀ S : ConjugationSubrepresentation ρ H,
      SubgroupFunctor.range (kernelι S.representation) = center G

/-- Proof of the full scheme-kernel identification. -/
theorem conjugationKernel : ConjugationKernelStatement.{u} := by
  intro k _ G _ n _ _ ρ _ H hH S
  exact S.range_kernel_eq_center hH

end Langlands.GroupScheme.MatrixRepresentation
