import Langlands.GroupScheme.Examples.HermitianMatrixPresentation
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Hermitian matrix points over the original affine coefficient algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix.SchemeModel

open SU3Root

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {n : ℕ}

local notation "S" => CommRingCat.of F
set_option quotPrecheck false in
local notation "T[" R "]" => (algSpec S).obj (op R)
local notation "Γ[" R "]" => SpecialLinear.WeilRoot.sectionAlgebra F (T[R])
local notation "C[" R "]" => SpecialLinear.WeilRoot.tensorAlgebra F E (T[R])
local notation "bar[" R "]" => SU3Root.SchemeModel.coefficientInvolution F E (T[R])
local notation "c[" R "]" => tensorInvolution F E R

/-- Evaluation of sections and exchange of tensor factors on an affine test. -/
def affineCoefficientEquiv (R : CommAlgCat.{u} S) : C[R] ≃+* (R ⊗[F] E) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
    (Corepresented.affineSectionsAlgEquiv R)).toRingEquiv.trans
      (Algebra.TensorProduct.comm F E R).toRingEquiv

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
@[simp] theorem affineCoefficientEquiv_tmul (R : CommAlgCat.{u} S) (x : E) (a : Γ[R]) :
    affineCoefficientEquiv F E R (x ⊗ₜ[F] a) =
      Corepresented.affineSectionsAlgEquiv R a ⊗ₜ[F] x := rfl

/-- The two actual coefficient involutions coincide in affine coordinates. -/
theorem affineCoefficientEquiv_bar (R : CommAlgCat.{u} S) (x : C[R]) :
    affineCoefficientEquiv F E R (bar[R].bar x) = c[R].bar (affineCoefficientEquiv F E R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The original Gram matrix extended to the affine tensor algebra. -/
def coefficientForm (H : Form (fieldInvolution F E) (Fin n))
    (R : CommAlgCat.{u} S) : Form c[R] (Fin n) :=
  H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
    (fun _ => rfl)

private theorem map_tensorForm_gram (H : Form (fieldInvolution F E) (Fin n)) (R : CommAlgCat.{u} S) :
    ((tensorForm F E H (T[R])).gram : Matrix (Fin n) (Fin n) C[R]).map
        (affineCoefficientEquiv F E R) = (coefficientForm F E H R).gram := by
  ext i j
  change affineCoefficientEquiv F E R (H.gram i j ⊗ₜ[F] (1 : Γ[R])) =
    (1 : R) ⊗ₜ[F] H.gram i j
  rw [affineCoefficientEquiv_tmul, map_one]

private theorem isometry_mem_map_affineCoefficientEquiv_iff (H : Form (fieldInvolution F E) (Fin n))
    (R : CommAlgCat.{u} S) (g : GL (Fin n) C[R]) :
    g ∈ specialUnitarySubgroup (tensorForm F E H (T[R])) ↔
      GeneralLinearGroup.map (affineCoefficientEquiv F E R).toRingHom g ∈
        specialUnitarySubgroup (coefficientForm F E H R) := by
  let e := affineCoefficientEquiv F E R
  let J := tensorForm F E H (T[R])
  let J' := coefficientForm F E H R
  have hJ : (J.gram : Matrix (Fin n) (Fin n) C[R]).map e = J'.gram := map_tensorForm_gram F E H R
  rw [mem_specialUnitarySubgroup, mem_specialUnitarySubgroup]
  change adjoint bar[R] (g : Matrix (Fin n) (Fin n) C[R]) * (J.gram : Matrix (Fin n) (Fin n) C[R]) *
      (g : Matrix (Fin n) (Fin n) C[R]) = J.gram ∧ GeneralLinearGroup.det g = 1 ↔
    adjoint c[R] ((g : Matrix (Fin n) (Fin n) C[R]).map e) * (J'.gram : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
      (g : Matrix (Fin n) (Fin n) C[R]).map e = J'.gram ∧
      GeneralLinearGroup.det (GeneralLinearGroup.map e.toRingHom g) = 1
  have hm : adjoint c[R] ((g : Matrix (Fin n) (Fin n) C[R]).map e) =
      (adjoint bar[R] (g : Matrix (Fin n) (Fin n) C[R])).map e :=
    adjoint_map e.toRingHom (affineCoefficientEquiv_bar F E R) _
  rw [hm, ← hJ]
  change _ ∧ _ ↔
    (adjoint bar[R] (g : Matrix (Fin n) (Fin n) C[R])).map e.toRingHom *
      (J.gram : Matrix (Fin n) (Fin n) C[R]).map e.toRingHom *
      (g : Matrix (Fin n) (Fin n) C[R]).map e.toRingHom = (J.gram : Matrix (Fin n) (Fin n) C[R]).map e.toRingHom ∧ _
  rw [← Matrix.map_mul, ← Matrix.map_mul, GeneralLinearGroup.map_det, ← map_one (Units.map e.toMonoidHom)]
  exact and_congr (e.mapMatrix.injective.eq_iff).symm
    ((Units.mapEquiv e.toMulEquiv).injective.eq_iff).symm

private def equivSubgroups {A B : Type u} [Group A] [Group B] (e : A ≃* B)
    (P : Subgroup A) (Q : Subgroup B) (h : ∀ a, a ∈ P ↔ e a ∈ Q) : P ≃* Q where
  toEquiv := Equiv.subtypeEquiv e.toEquiv h
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

private def affineUnitEquiv (R : CommAlgCat.{u} S) : GL (Fin n) C[R] ≃* GL (Fin n) (R ⊗[F] E) :=
  Units.mapEquiv ((affineCoefficientEquiv F E R).mapMatrix (m := Fin n)).toMulEquiv

private def coefficientUnitaryEquiv (H : Form (fieldInvolution F E) (Fin n)) (R : CommAlgCat.{u} S) :
    tensorPoints F E H (T[R]) ≃* specialUnitarySubgroup (coefficientForm F E H R) :=
  equivSubgroups (affineUnitEquiv F E (n := n) R)
    (specialUnitarySubgroup (tensorForm F E H (T[R])))
    (specialUnitarySubgroup (coefficientForm F E H R))
    (isometry_mem_map_affineCoefficientEquiv_iff F E H R)

/-- The actual affine points of the supplied presentation are the special unitary matrices
on the original tensor algebra of coefficients. -/
def Presentation.affineMatrixEquiv
    {G : GroupScheme (Spec (CommRingCat.of F))} {H : Form (fieldInvolution F E) (Fin n)}
    (p : Presentation F E H G) (R : CommAlgCat.{u} S) :
    ((T[R]) ⟶ G.X) ≃* specialUnitarySubgroup (coefficientForm F E H R) :=
  (p.pointsEquiv (T[R])).trans (coefficientUnitaryEquiv F E H R)

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
private theorem affineCoefficientEquiv_tensorMap {R R' : CommAlgCat.{u} S} (f : R ⟶ R') (x : C[R]) :
    affineCoefficientEquiv F E R' (SpecialLinear.WeilRoot.tensorMap F E ((algSpec S).map f.op) x) =
      Algebra.TensorProduct.map f.hom (AlgHom.id F E) (affineCoefficientEquiv F E R x) := by
  have hnat := Corepresented.affineSectionsIso_inv_naturality f
  have hcomp : ((algΓ S).map ((algSpec S).map f.op)).unop ≫
      (Corepresented.affineSectionsIso R').hom = (Corepresented.affineSectionsIso R).hom ≫ f := by
    rw [← cancel_epi (Corepresented.affineSectionsIso R).inv, ← Category.assoc, hnat,
      Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  induction x using TensorProduct.inductionOn with
  | tmul e a =>
    change affineCoefficientEquiv F E R' (e ⊗ₜ[F] (((algΓ S).map ((algSpec S).map f.op)).unop.hom a)) = _
    rw [affineCoefficientEquiv_tmul, affineCoefficientEquiv_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun g : Γ[R] ⟶ R' => g.hom a ⊗ₜ[F] e) hcomp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The affine matrix presentation respects every map of coefficient algebras. -/
theorem Presentation.affineMatrixEquiv_naturality
    {G : GroupScheme (Spec (CommRingCat.of F))} {H : Form (fieldInvolution F E) (Fin n)}
    (p : Presentation F E H G)
    {R R' : CommAlgCat.{u} S} (f : R ⟶ R') (x : G.affinePoints R) :
    (p.affineMatrixEquiv F E R' (G.affinePointMap f x)).val =
      GeneralLinearGroup.map (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom
        (p.affineMatrixEquiv F E R x).val := by
  apply Units.ext
  change ((p.pointsEquiv (T[R']) (((algSpec S).map f.op) ≫ x)).val : Matrix (Fin n) (Fin n) C[R']).map
      (affineCoefficientEquiv F E R') =
    (((p.pointsEquiv (T[R]) x).val : Matrix (Fin n) (Fin n) C[R]).map (affineCoefficientEquiv F E R)).map
      (Algebra.TensorProduct.map f.hom (AlgHom.id F E))
  rw [p.matrix_naturality ((algSpec S).map f.op) x]
  ext i j
  exact affineCoefficientEquiv_tensorMap F E f _

end Langlands.GroupScheme.HermitianMatrix.SchemeModel
