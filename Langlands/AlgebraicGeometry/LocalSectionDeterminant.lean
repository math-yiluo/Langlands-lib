import Langlands.AlgebraicGeometry.LocalSectionBasis
import Langlands.Shimura.PEL.HodgeDeterminantBaseChange

/-! # Determinant polynomials on actual local module sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    {I : Type u} [Fintype I] {M : X.Modules}
    {ι : Type v} [Fintype ι]

local instance : DecidableEq I := Classical.decEq I

/-- The determinant of an actual finite family acting on sections of a free chart. -/
def localSectionDeterminant
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) (V : Over U) : MvPolynomial ι Γ(X, V.left) :=
  Langlands.Shimura.HodgeDeterminant.polynomial (localSectionBasis e V)
    (fun i => localSectionEndomorphism M V (f i))

/-- Any finite basis of the same section module gives the constructed polynomial. -/
theorem localSectionDeterminant_eq_basis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) (V : Over U)
    {J : Type u} [Fintype J] [DecidableEq J]
    (b : Module.Basis J Γ(X, V.left) Γ(M, V.left)) :
    localSectionDeterminant e f V =
      Langlands.Shimura.HodgeDeterminant.polynomial b
        (fun i => localSectionEndomorphism M V (f i)) :=
  Langlands.Shimura.HodgeDeterminant.polynomial_basis_independent_commRing _ _ _

/-- Trivializations with arbitrary finite index types give the same polynomial. -/
theorem localSectionDeterminant_trivialization_independent
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U)
    (f : ι → End (M.over U)) (V : Over U) :
    localSectionDeterminant e f V = localSectionDeterminant e' f V := by
  let : DecidableEq J := Classical.decEq J
  exact localSectionDeterminant_eq_basis e f V (localSectionBasis e' V)

/-- The universal matrix itself commutes with the actual restriction ring map. -/
theorem localSectionDeterminant_matrix_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) {V W : Over U} (j : V ⟶ W) :
    (Langlands.Shimura.HodgeDeterminant.matrix (localSectionBasis e W)
        (fun i => localSectionEndomorphism M W (f i))).map
          (MvPolynomial.map (X.presheaf.map j.left.op).hom) =
      Langlands.Shimura.HodgeDeterminant.matrix (localSectionBasis e V)
        (fun i => localSectionEndomorphism M V (f i)) := by
  ext k l
  simp only [Matrix.map_apply, Langlands.Shimura.HodgeDeterminant.matrix,
    map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    localSectionEndomorphism_toMatrix_restrict e j]

/-- The polynomial on the smaller open is the coefficient restriction of the first. -/
theorem localSectionDeterminant_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) {V W : Over U} (j : V ⟶ W) :
    MvPolynomial.map (X.presheaf.map j.left.op).hom
        (localSectionDeterminant e f W) = localSectionDeterminant e f V := by
  unfold localSectionDeterminant Langlands.Shimura.HodgeDeterminant.polynomial
  rw [RingHom.map_det]
  exact congrArg Matrix.det (localSectionDeterminant_matrix_restrict e f j)

/-- Every coefficient is a restriction-compatible structure-sheaf section. -/
theorem coeff_localSectionDeterminant_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) {V W : Over U} (j : V ⟶ W) (d : ι →₀ ℕ) :
    X.presheaf.map j.left.op ((localSectionDeterminant e f W).coeff d) =
      (localSectionDeterminant e f V).coeff d := by
  rw [← localSectionDeterminant_restrict e f j, MvPolynomial.coeff_map]

/-- Evaluation is the intrinsic determinant of the actual section endomorphism. -/
theorem eval_localSectionDeterminant
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) (V : Over U) (x : ι → Γ(X, V.left)) :
    eval x (localSectionDeterminant e f V) =
      LinearMap.det (∑ i, x i • localSectionEndomorphism M V (f i)) :=
  Langlands.Shimura.HodgeDeterminant.eval_polynomial _ _ _

/-- Homogeneous support has degree the rank of the actual free chart. -/
theorem localSectionDeterminant_isHomogeneous
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : ι → End (M.over U)) (V : Over U) :
    (localSectionDeterminant e f V).IsHomogeneous (Fintype.card I) :=
  Langlands.Shimura.HodgeDeterminant.polynomial_isHomogeneous _ _

end Langlands.Scheme.Modules
