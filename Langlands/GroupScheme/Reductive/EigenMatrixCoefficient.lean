import Langlands.GroupScheme.HomogeneousCharacterCoordinates

/-! # Matrix coefficients of eigen-covectors against eigenvectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

section Value

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The value `ξ(ρ(g) v)` of the matrix coefficient of `ξ` and `v` at a test point `g`. -/
def coefficientValue (ρ : MatrixRepresentation G n) (ξ v : n → k)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) : Γ(T.left, ⊤) :=
  (fun a => scalarMap T (ξ a)) ⬝ᵥ
    ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ fun b => scalarMap T (v b))

/-- Pulling back the test scheme pulls back the coefficient value. -/
theorem coefficientValue_naturality (ρ : MatrixRepresentation G n) (ξ v : n → k)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (g : T ⟶ G.X) :
    coefficientValue ρ ξ v T' (a ≫ g) = a.left.appTop (coefficientValue ρ ξ v T g) := by
  have hs : ∀ c : k, a.left.appTop (scalarMap T c) = scalarMap T' c := fun c => by
    change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop) ≫ a.left.appTop) c = _
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w a]
    rfl
  have hM : ((ρ.pointMatrix T' (a ≫ g) : GL n Γ(T'.left, ⊤)) : Matrix n n Γ(T'.left, ⊤)) =
      (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)).map a.left.appTop.hom := by
    rw [MatrixRepresentation.pointMatrix_naturality]
    ext i j
    rfl
  change _ = a.left.appTop.hom _
  rw [coefficientValue, coefficientValue, RingHom.map_dotProduct, hM]
  congr 1
  · funext b
    exact (hs (ξ b)).symm
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext b
    exact (hs (v b)).symm

/-- At the identity point the coefficient value is the pairing `ξ(v)`. -/
theorem coefficientValue_one (ρ : MatrixRepresentation G n) (ξ v : n → k)
    (T : Over (Spec (CommRingCat.of k))) :
    coefficientValue ρ ξ v T 1 = scalarMap T (ξ ⬝ᵥ v) := by
  rw [coefficientValue, map_one, Units.val_one, Matrix.one_mulVec, RingHom.map_dotProduct]
  rfl

/-- Left multiplication by a point on which `ξ` is an eigen-covector scales the value. -/
theorem coefficientValue_mul_left (ρ : MatrixRepresentation G n) (ξ v : n → k)
    {T : Over (Spec (CommRingCat.of k))} (h g : T ⟶ G.X) (c : Γ(T.left, ⊤))
    (hξ : (fun a => scalarMap T (ξ a)) ᵥ* (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤)) =
      c • fun a => scalarMap T (ξ a)) :
    coefficientValue ρ ξ v T (h * g) = c * coefficientValue ρ ξ v T g := by
  rw [coefficientValue, coefficientValue, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, hξ, smul_dotProduct, smul_eq_mul]

/-- Right multiplication by a point on which `v` is an eigenvector scales the value. -/
theorem coefficientValue_mul_right (ρ : MatrixRepresentation G n) (ξ v : n → k)
    {T : Over (Spec (CommRingCat.of k))} (g h : T ⟶ G.X) (c : Γ(T.left, ⊤))
    (hv : (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun b => scalarMap T (v b)) =
      c • fun b => scalarMap T (v b)) :
    coefficientValue ρ ξ v T (g * h) = c * coefficientValue ρ ξ v T g := by
  rw [coefficientValue, coefficientValue, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

end Value

section Coordinate

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The value of a coordinate at a test point, regarded as a global section of the test
scheme. -/
abbrev pointValue (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (b : algebra G) :
    Γ(T.left, ⊤) :=
  pointAlgebraHom G T g b

/-- The coordinate `g ↦ ξ(ρ(g) v)` of `G`: the coordinate whose global function is the
coefficient value at the universal point. -/
def matrixCoefficient (ρ : MatrixRepresentation G n) (ξ v : n → k) : algebra G :=
  (globalAlgEquiv G).symm (coefficientValue ρ ξ v G.X (𝟙 G.X))

/-- The matrix coefficient evaluates to `ξ(ρ(g) v)` at every test point. -/
theorem pointAlgebraHom_matrixCoefficient (ρ : MatrixRepresentation G n) (ξ v : n → k)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointAlgebraHom G T g (matrixCoefficient G ρ ξ v) = coefficientValue ρ ξ v T g := by
  rw [pointAlgebraHom_apply_eq, matrixCoefficient, ← globalAlgEquiv_apply,
    AlgEquiv.apply_symm_apply]
  have h := coefficientValue_naturality ρ ξ v g (𝟙 G.X)
  rw [Category.comp_id] at h
  exact h.symm

/-- If `ξ(v) = 1`, the matrix coefficient takes the value `1` at the identity point of every
test scheme. -/
theorem pointAlgebraHom_one_matrixCoefficient (ρ : MatrixRepresentation G n) {ξ v : n → k}
    (hξv : ξ ⬝ᵥ v = 1) (T : Over (Spec (CommRingCat.of k))) :
    pointAlgebraHom G T 1 (matrixCoefficient G ρ ξ v) = 1 := by
  rw [pointAlgebraHom_matrixCoefficient, coefficientValue_one, hξv, map_one]

end Coordinate

section Subgroups

variable {G H H' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom H'.X.hom]

local instance eigenMatrixCoefficientInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance eigenMatrixCoefficientInst2 : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance eigenMatrixCoefficientInst3 : IsAffine H'.X.left :=
  isAffine_of_isAffineHom H'.X.hom

/-- If `ξ` is an eigen-covector of `ρ ∘ i` with eigenvalue `χ` on every test scheme, the matrix
coefficient of `ξ` and `v` is left `i`-covariant of weight `χ`. -/
theorem matrixCoefficient_mem_leftCovariantSubspace (ρ : MatrixRepresentation G n)
    (ξ v : n → k) (i : H ⟶ G) (χ : algebra H)
    (hξ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
      (fun a => scalarMap T (ξ a)) ᵥ*
          (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
        pointValue H T h χ • fun a => scalarMap T (ξ a)) :
    matrixCoefficient G ρ ξ v ∈ leftCovariantSubspace i χ := by
  rw [mem_leftCovariantSubspace_iff_points]
  intro T h g
  rw [pointAlgebraHom_matrixCoefficient, pointAlgebraHom_matrixCoefficient]
  exact coefficientValue_mul_left ρ ξ v _ g _ (hξ T h)

/-- If `ρ(i'(h)⁻¹) v = ψ(h) v` on every test scheme, the matrix coefficient of `ξ` and `v`
satisfies `d(g i'(h)⁻¹) = ψ(h) d(g)` on every test scheme. -/
theorem pointAlgebraHom_mul_inv_matrixCoefficient (ρ : MatrixRepresentation G n)
    (ξ v : n → k) (i' : H' ⟶ G) (ψ : algebra H')
    (hv : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H'.X),
      (ρ.pointMatrix T (h ≫ i'.hom.hom)⁻¹ : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun b => scalarMap T (v b)) =
        pointValue H' T h ψ • fun b => scalarMap T (v b))
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H'.X) (g : T ⟶ G.X) :
    pointAlgebraHom G T (g * (h ≫ i'.hom.hom)⁻¹) (matrixCoefficient G ρ ξ v) =
      pointAlgebraHom H' T h ψ * pointAlgebraHom G T g (matrixCoefficient G ρ ξ v) := by
  rw [pointAlgebraHom_matrixCoefficient, pointAlgebraHom_matrixCoefficient]
  exact coefficientValue_mul_right ρ ξ v g _ _ (hv T h)

end Subgroups

end AffineCoordinates

end Langlands.GroupScheme
