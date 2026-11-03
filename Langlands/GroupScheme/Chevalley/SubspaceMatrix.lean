import Langlands.GroupScheme.Chevalley.RegularSubspace
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.MatrixRepresentation

/-! # Matrix coefficients for a chosen basis of a regular subspace -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B]
  [Coalgebra K B] (V : Submodule K B)

/-- A linear retraction onto the chosen subspace. -/
def subspaceRetraction : B →ₗ[K] V :=
  Classical.choose (V.subtype.exists_leftInverse_of_injective V.ker_subtype)

omit [Coalgebra K B] in
theorem subspaceRetraction_comp_subtype :
    subspaceRetraction V ∘ₗ V.subtype = LinearMap.id :=
  Classical.choose_spec (V.subtype.exists_leftInverse_of_injective V.ker_subtype)

variable {N : ℕ} (b : Basis (Fin N) K V)

/-- The coordinate functionals of the subspace basis, extended to the ambient coalgebra. -/
def extendedCoord (i : Fin N) : Module.Dual K B :=
  b.coord i ∘ₗ subspaceRetraction V

omit [Coalgebra K B] in
@[simp] theorem extendedCoord_basis (i j : Fin N) :
    extendedCoord V b i (b j : B) = (1 : Matrix (Fin N) (Fin N) K) i j := by
  have hp := LinearMap.congr_fun (subspaceRetraction_comp_subtype V) (b j)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hp
  change b.coord i (subspaceRetraction V (V.subtype (b j))) = _
  rw [hp]
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

/-- The matrix coefficients of right translation on the chosen basis. -/
def subspaceMatrix : Matrix (Fin N) (Fin N) B :=
  Matrix.of fun i j => leftAct (extendedCoord V b i) (b j : B)

omit [Coalgebra K B] in
theorem basis_expand {v : B} (hv : v ∈ V) :
    ∑ i, extendedCoord V b i v • (b i : B) = v := by
  have hp := LinearMap.congr_fun (subspaceRetraction_comp_subtype V) (⟨v, hv⟩ : V)
  have he := congrArg Subtype.val (b.sum_repr (⟨v, hv⟩ : V))
  simpa only [extendedCoord, LinearMap.comp_apply, Basis.coord_apply,
    Submodule.coe_sum, Submodule.coe_smul,
    show subspaceRetraction V v = ⟨v, hv⟩ from hp] using he

variable (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V → rightAct f v ∈ V)

include hV in
/-- The actual comultiplication formula in the chosen basis. -/
theorem comul_basis (j : Fin N) :
    comul (R := K) (b j : B) = ∑ i, (b i : B) ⊗ₜ[K] subspaceMatrix V b i j := by
  apply tensor_ext
  intro f
  rw [← rightAct_apply, ← basis_expand V b (hV f _ (b j).2), map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rw [subspaceMatrix, Matrix.of_apply, apply_leftAct]

include hV in
/-- Coassociativity gives the multiplicative matrix coefficient law. -/
theorem comul_subspaceMatrix (i j : Fin N) :
    comul (R := K) (subspaceMatrix V b i j) =
      ∑ l, subspaceMatrix V b i l ⊗ₜ[K] subspaceMatrix V b l j := by
  apply tensor_ext
  intro f
  change rightAct f (leftAct (extendedCoord V b i) (b j : B)) = _
  rw [rightAct_leftAct, ← basis_expand V b (hV f _ (b j).2), map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, ← apply_leftAct]
  rfl

/-- The counit gives the identity matrix. -/
theorem counit_subspaceMatrix (i j : Fin N) :
    counit (R := K) (subspaceMatrix V b i j) =
      (1 : Matrix (Fin N) (Fin N) K) i j := by
  change counit (leftAct (extendedCoord V b i) (b j : B)) = _
  rw [apply_leftAct, rightAct_counit, extendedCoord_basis]

include hV in
/-- The coefficient-valued translation formula for each basis vector. -/
theorem translate_basis {A : Type*} [AddCommGroup A] [Module K A] (f : B →ₗ[K] A)
    (j : Fin N) :
    translate f (b j : B) = ∑ i, (b i : B) ⊗ₜ[K] f (subspaceMatrix V b i j) := by
  rw [translate, LinearMap.comp_apply, comul_basis V b hV, map_sum]
  simp

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.Chevalley

open CategoryTheory Opposite AlgebraicGeometry AffineLinearEmbedding

universe u

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (hR : IsField R) (V : Submodule R B) {N : ℕ} (b : Basis (Fin N) R V)
  (hV : letI := hR.toField
    letI := (bialgebra e).toCoalgebra
    ∀ (f : Module.Dual R B) (v : B), v ∈ V → rightAct f v ∈ V)

/-- The actual group-scheme representation on the chosen finite regular subspace. -/
def regularRepresentation :
    MatrixRepresentation (Corepresented.groupScheme F e) (Fin N) := by
  letI := hR.toField
  letI := (bialgebra e).toCoalgebra
  exact toGLHom e (subspaceMatrix V b) (comul_subspaceMatrix V b hV)
    (counit_subspaceMatrix V b)

/-- On every scheme test, the representation matrix is evaluation of the constructed
coefficients in relative global sections. -/
theorem regularRepresentation_pointMatrix
    (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X) (i j : Fin N) :
    letI := hR.toField
    letI := (bialgebra e).toCoalgebra
    (regularRepresentation e hR V b hV).pointMatrix T x i j =
      (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom
        (subspaceMatrix V b i j) := by
  let := hR.toField
  let := (bialgebra e).toCoalgebra
  have hh :
      (regularRepresentation e hR V b hV).pointMatrix T x =
        (toGL e (subspaceMatrix V b) (comul_subspaceMatrix V b hV)
          (counit_subspaceMatrix V b)).app ((algΓ R).obj T).unop
            (Corepresented.pointsEquiv F e T x) :=
    Corepresented.groupSchemeMap_points e
      (GeneralLinear.corepresentableBy (Fin N) R) _ x
  exact congrArg (fun g : GL (Fin N) Γ(T.left, ⊤) => g i j) hh

end Langlands.GroupScheme.Chevalley
