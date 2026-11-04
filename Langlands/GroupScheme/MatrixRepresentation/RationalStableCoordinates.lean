import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Langlands.GroupScheme.MatrixRepresentation.InvariantCoordinates
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.SchemeActionRationalPoints

/-! # Detecting invariant coordinates on rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]

/-- The difference between the ambient action and its projected coordinates. -/
def coordinateStabilityDefect (ρ : MatrixRepresentation G n)
    (B : Matrix n m R) (C : Matrix m n R)
    (T : Over (Spec R)) (x : T ⟶ G.X) : Matrix n m Γ(T.left, ⊤) :=
  (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) -
    B.map (scalarMap T) *
      (C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        B.map (scalarMap T))

/-- The defect is natural on all relative scheme tests. -/
theorem coordinateStabilityDefect_naturality (ρ : MatrixRepresentation G n)
    (B : Matrix n m R) (C : Matrix m n R)
    {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ G.X) :
    ρ.coordinateStabilityDefect B C T' (a ≫ x) =
      (ρ.coordinateStabilityDefect B C T x).map a.left.appTop.hom := by
  have hB : B.map (scalarMap T') = (B.map (scalarMap T)).map a.left.appTop.hom := by
    ext r s
    exact (scalarMap_naturality a _).symm
  have hC : C.map (scalarMap T') = (C.map (scalarMap T)).map a.left.appTop.hom := by
    ext r s
    exact (scalarMap_naturality a _).symm
  simp only [coordinateStabilityDefect, pointMatrix_naturality,
    hB, hC, Matrix.map_sub _ (map_sub _), Matrix.map_mul (f := a.left.appTop.hom)]
  rfl

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {J : GroupScheme (Spec (CommRingCat.of k))}
  [IsReduced J.X.left] [LocallyOfFiniteType J.X.hom]

/-- For a reduced group locally of finite type over an algebraically closed
field, split-coordinate invariance is detected on base points. -/
theorem isStableCoordinates_of_basePoints (ρ : MatrixRepresentation J n)
    (B : Matrix n m k) (C : Matrix m n k)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X,
      ρ.coordinateStabilityDefect B C _ x = 0) :
    ρ.IsStableCoordinates B C := by
  have hsep : IsSeparated (coefficientSpace n (CommRingCat.of k)).hom := by
    dsimp [coefficientSpace]
    infer_instance
  have huniv : ρ.coordinateStabilityDefect B C J.X (𝟙 _) = 0 := by
    ext r s
    let f : J.X ⟶ coefficientSpace n (CommRingCat.of k) :=
      coefficientPoint J.X (fun r => ρ.coordinateStabilityDefect B C J.X (𝟙 _) r s)
    let z : J.X ⟶ coefficientSpace n (CommRingCat.of k) :=
      coefficientPoint J.X 0
    have he : f = z := by
      apply hom_ext_rationalPoints
      intro x
      apply coefficientCoordinates_injective
      simp only [f, z, coefficientCoordinates_comp,
        coefficientCoordinates_coefficientPoint]
      funext r
      have hx := congrArg (fun M => M r s)
        (ρ.coordinateStabilityDefect_naturality B C x (𝟙 J.X))
      simp only [Category.comp_id, h x, Matrix.zero_apply, Matrix.map_apply] at hx
      exact hx.symm.trans (map_zero _).symm
    have hec := congrArg (fun q => coefficientCoordinates q r) he
    simpa only [f, z, coefficientCoordinates_coefficientPoint, Pi.zero_apply,
      Matrix.zero_apply] using hec
  intro T x
  apply sub_eq_zero.mp
  change ρ.coordinateStabilityDefect B C T x = 0
  have hx := ρ.coordinateStabilityDefect_naturality B C x (𝟙 J.X)
  simpa only [Category.comp_id, huniv, Matrix.map_zero _ (map_zero _)] using hx

/-- The same criterion expressed by matrices with entries in the ground field. -/
theorem isStableCoordinates_of_rationalMatrix (ρ : MatrixRepresentation J n)
    (B : Matrix n m k) (C : Matrix m n k)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X,
      (ρ.rationalMatrix x : Matrix n n k) * B =
        B * (C * (ρ.rationalMatrix x : Matrix n n k) * B)) :
    ρ.IsStableCoordinates B C := by
  apply isStableCoordinates_of_basePoints ρ B C
  intro x
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  apply Matrix.map_injective e.injective
  change (ρ.coordinateStabilityDefect B C _ x).map e.toRingHom =
    (0 : Matrix n m Γ(Spec (CommRingCat.of k), ⊤)).map e.toRingHom
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = B := by
    ext r s
    exact e.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = C := by
    ext r s
    exact e.apply_symm_apply _
  have hM : ((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k))))) x).val.map
      e.toRingHom = (ρ.rationalMatrix x : Matrix n n k) := rfl
  simpa only [coordinateStabilityDefect, Matrix.map_sub _ (map_sub _),
    Matrix.map_mul (f := e.toRingHom), hB, hC, hM,
    Matrix.map_zero _ (map_zero _)] using sub_eq_zero.mpr (h x)

end AlgebraicallyClosed

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The base-field matrix recovers the original matrix of sections. -/
theorem map_rationalMatrix (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    Matrix.GeneralLinearGroup.map
        (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (ρ.rationalMatrix g) =
      ρ.pointMatrix _ g := by
  apply Units.ext
  ext r s
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _).appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom (ρ.pointMatrix _ g r s)) = _
  simp

/-- Constant rational points have matrices obtained by scalar extension. -/
theorem pointMatrix_constant (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (T : Over (Spec (CommRingCat.of k))) :
    ρ.pointMatrix T (CartesianMonoidalCategory.toUnit T ≫ g) =
      Matrix.GeneralLinearGroup.map (scalarMap T) (ρ.rationalMatrix g) := by
  rw [pointMatrix_naturality]
  change Matrix.GeneralLinearGroup.map
      (CartesianMonoidalCategory.toUnit T).left.appTop.hom
      (ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) g) = _
  rw [← map_rationalMatrix]
  apply Units.ext
  ext r s
  exact scalarMap_comp _ _

omit [DecidableEq m] in
/-- A matrix coordinate identity can be checked at the universal point. -/
theorem stableCoordinates_iff_universal (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k) :
    ρ.IsStableCoordinates B C ↔
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) *
          B.map (scalarMap G.X) =
        B.map (scalarMap G.X) *
          (C.map (scalarMap G.X) *
            (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) *
            B.map (scalarMap G.X)) := by
  constructor
  · exact fun h => h _ _
  · intro h T x
    have hx := congrArg (fun M : Matrix n m Γ(G.X.left, ⊤) =>
      M.map x.left.appTop.hom) h
    have hB : (B.map (scalarMap G.X)).map x.left.appTop.hom =
        B.map (scalarMap T) := by
      ext r s
      exact scalarMap_comp _ _
    have hC : (C.map (scalarMap G.X)).map x.left.appTop.hom =
        C.map (scalarMap T) := by
      ext r s
      exact scalarMap_comp _ _
    have hM := ρ.pointMatrix_naturality x (𝟙 G.X)
    simp only [Category.comp_id] at hM
    have hM' := congrArg (fun U : GL n Γ(T.left, ⊤) =>
      (U : Matrix n n Γ(T.left, ⊤))) hM
    change (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)).map
        x.left.appTop.hom at hM'
    simp only [Matrix.map_mul] at hx
    rw [hB, hC, ← hM'] at hx
    exact hx

end Langlands.GroupScheme.MatrixRepresentation
