import Langlands.GroupScheme.CliffordSpin.AffineEquations
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.FiniteAlgebraUnits

/-! # The affine scheme of scalar Clifford spin lifts -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 100000

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
  [Invertible (2 : F)] {n : ℕ} (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V)

local notation "S" => CommRingCat.of F
local notation "C" => CliffordAlgebra Q

/-- Use the exterior basis transported to the Clifford algebra as affine coordinates. -/
abbrev algebraBasis : Module.Basis (Finset (Fin n)) F C := cliffordOrthogonalBasis Q b

private abbrev unitBasis : Module.Basis (Fin (Fintype.card (Finset (Fin n)))) F C :=
  (algebraBasis Q b).reindex (Fintype.equivFin _)

private abbrev unitAlgebra : CommAlgCat.{u} S := FiniteAlgebraUnits.coordinateAlgebra (unitBasis Q b)
private abbrev matrixAlgebra : CommAlgCat.{u} S := CommAlgCat.of S (GeneralLinear.CoordinateRing (Fin n) S)

/-- The ambient algebra of coordinates for a Clifford unit and an invertible matrix. -/
abbrev ambientAlgebra : CommAlgCat.{u} S :=
  Corepresented.tensorObj (unitAlgebra Q b) (matrixAlgebra (F := F) (n := n))

private abbrev unitFunctor := FiniteAlgebraUnits.functor F C
private abbrev matrixFunctor := GeneralLinear.functor (Fin n) S

/-- The point functor of pairs of tensor units and invertible matrices. -/
def ambientFunctor : CommAlgCat.{u} S ⥤ GrpCat.{u} where
  obj A := GrpCat.of ((A ⊗[F] C)ˣ × GL (Fin n) A)
  map f := GrpCat.ofHom (((unitFunctor Q).map f).hom.prodMap ((matrixFunctor (n := n)).map f).hom)
  map_id A := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Prod.ext
    · change (unitFunctor Q).map (𝟙 A) x.1 = x.1
      rw [CategoryTheory.Functor.map_id]
      rfl
    · change (matrixFunctor (n := n)).map (𝟙 A) x.2 = x.2
      rw [CategoryTheory.Functor.map_id]
      rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Prod.ext
    · change (unitFunctor Q).map (f ≫ g) x.1 =
        (unitFunctor Q).map g ((unitFunctor Q).map f x.1)
      rw [Functor.map_comp]
      rfl
    · change (matrixFunctor (n := n)).map (f ≫ g) x.2 =
        (matrixFunctor (n := n)).map g ((matrixFunctor (n := n)).map f x.2)
      rw [Functor.map_comp]
      rfl

/-- The tensor product corepresents the pair functor. -/
def ambientCorepresentation : (ambientFunctor (n := n) Q ⋙ forget GrpCat).CorepresentableBy
    (ambientAlgebra Q b) := by
  let e := FiniteAlgebraUnits.corepresentableBy (unitBasis Q b)
  let d := GeneralLinear.corepresentableBy (Fin n) S
  refine ⟨fun {A} => ?_, ?_⟩
  · exact
      { toFun := fun f => ⟨e.homEquiv (Corepresented.inl _ _ ≫ f), d.homEquiv (Corepresented.inr _ _ ≫ f)⟩
        invFun := fun x => Corepresented.tensorLift (e.homEquiv.symm x.1) (d.homEquiv.symm x.2)
        left_inv := fun f => by
          simp only [Equiv.symm_apply_apply]
          apply CommAlgCat.hom_ext
          apply Algebra.TensorProduct.ext'
          intro a m
          change f.hom (a ⊗ₜ[F] 1) * f.hom (1 ⊗ₜ[F] m) = f.hom (a ⊗ₜ[F] m)
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        right_inv := fun x => by
          apply Prod.ext
          · change e.homEquiv (Corepresented.inl _ _ ≫ Corepresented.tensorLift
                (e.homEquiv.symm x.1) (d.homEquiv.symm x.2)) = x.1
            rw [Corepresented.inl_tensorLift, Equiv.apply_symm_apply]
          · change d.homEquiv (Corepresented.inr _ _ ≫ Corepresented.tensorLift
                (e.homEquiv.symm x.1) (d.homEquiv.symm x.2)) = x.2
            rw [Corepresented.inr_tensorLift, Equiv.apply_symm_apply] }
  · intro A B g f
    apply Prod.ext
    · change e.homEquiv (Corepresented.inl _ _ ≫ f ≫ g) =
        (unitFunctor Q).map g (e.homEquiv (Corepresented.inl _ _ ≫ f))
      rw [← Category.assoc, e.homEquiv_comp]
      rfl
    · change d.homEquiv (Corepresented.inr _ _ ≫ f ≫ g) =
        (matrixFunctor (n := n)).map g (d.homEquiv (Corepresented.inr _ _ ≫ f))
      rw [← Category.assoc, d.homEquiv_comp]
      rfl

private inductive Equation (n : ℕ) where
  | grade (j : Finset (Fin n))
  | norm (j : Finset (Fin n))
  | action (i : Fin n) (j : Finset (Fin n))
  | determinant

private def coefficient {A : CommAlgCat.{u} S} (x : A ⊗[F] C) (j : Finset (Fin n)) : A :=
  ((algebraBasis Q b).baseChange A).repr x j

private theorem coefficient_map {A B : CommAlgCat.{u} S} (f : A ⟶ B)
    (x : A ⊗[F] C) (j : Finset (Fin n)) :
    f.hom (coefficient Q b x j) = coefficient Q b (tensorMap Q f.hom x) j := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [coefficient, map_add, Finsupp.add_apply] at hx hy ⊢
    rw [hx, hy]
  | tmul a c =>
    simp [coefficient, Algebra.smul_def, AlgHom.commutes]

private def evaluate (A : CommAlgCat.{u} S) (x : (ambientFunctor (n := n) Q).obj A) :
    Equation n → A
  | .grade j => coefficient Q b (gradeDefect Q A x.1) j
  | .norm j => coefficient Q b (normDefect Q A x.1) j
  | .action i j => coefficient Q b (actionDefect Q b A x.1 x.2 i) j
  | .determinant => (x.2 : Matrix (Fin n) (Fin n) A).det - 1

private theorem evaluate_map {A B : CommAlgCat.{u} S} (f : A ⟶ B)
    (x : (ambientFunctor (n := n) Q).obj A) (i : Equation n) :
    f.hom (evaluate Q b A x i) = evaluate Q b B ((ambientFunctor (n := n) Q).map f x) i := by
  have hu : (((ambientFunctor (n := n) Q).map f x).1 : B ⊗[F] C) = tensorMap Q f.hom x.1 := rfl
  have hg : ((ambientFunctor (n := n) Q).map f x).2 = Matrix.GeneralLinearGroup.map f.hom.toRingHom x.2 := rfl
  cases i with
  | grade j => simp only [evaluate, coefficient_map Q b f, hu, tensorMap_gradeDefect]
  | norm j => simp only [evaluate, coefficient_map Q b f, hu, tensorMap_normDefect]
  | action i j => simp only [evaluate, coefficient_map Q b f, hu, hg, tensorMap_actionDefect]
  | determinant =>
    change f.hom ((x.2 : Matrix (Fin n) (Fin n) A).det - 1) = _
    rw [map_sub, map_one]
    change f.hom ((x.2 : Matrix (Fin n) (Fin n) A).det) - 1 =
      (((Matrix.GeneralLinearGroup.map f.hom.toRingHom x.2 : GL (Fin n) B) :
        Matrix (Fin n) (Fin n) B)).det - 1
    exact congrArg (· - 1) (RingHom.map_det f.hom.toRingHom _)

private theorem coefficient_zero_iff {A : CommAlgCat.{u} S} (x : A ⊗[F] C) :
    (∀ j, coefficient Q b x j = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply ((algebraBasis Q b).baseChange A).repr.injective
    ext j
    exact (h j).trans (by simp)
  · rintro rfl j
    simp [coefficient]

private theorem mem_iff_evaluate_zero (A : CommAlgCat.{u} S)
    (x : (ambientFunctor (n := n) Q).obj A) :
    x ∈ coefficientSubgroup Q b A ↔ ∀ i, evaluate Q b A x i = 0 := by
  obtain ⟨a, g⟩ := x
  rw [mem_coefficientSubgroup_iff]
  constructor
  · rintro ⟨hg, hn, hd, ha⟩ i
    cases i with
    | grade j => simp [evaluate, hg, coefficient]
    | norm j => simp [evaluate, hn, coefficient]
    | action i j => simp [evaluate, ha i, coefficient]
    | determinant =>
      change (g : Matrix (Fin n) (Fin n) A).det - 1 = 0
      exact sub_eq_zero.mpr (congrArg Units.val hd)
  · intro h
    refine ⟨(coefficient_zero_iff Q b _).mp (fun j => h (.grade j)),
      (coefficient_zero_iff Q b _).mp (fun j => h (.norm j)), ?_,
      fun i => (coefficient_zero_iff Q b _).mp (fun j => h (.action i j))⟩
    exact Units.ext (sub_eq_zero.mp (h .determinant))

/-- The ideal generated by the coefficient equations of the universal pair. -/
def ideal : Ideal (ambientAlgebra Q b) :=
  Ideal.span (Set.range (evaluate Q b (ambientAlgebra Q b)
    ((ambientCorepresentation Q b).homEquiv (𝟙 _))))

/-- The universal coordinates give exactly the intended subgroup on every affine test. -/
theorem isCutOutBy : Corepresented.IsCutOutBy (ambientCorepresentation Q b)
    (fun A => coefficientSubgroup Q b A) (ideal Q b) := by
  intro A x
  let e := ambientCorepresentation Q b
  let f := e.homEquiv.symm x
  have h (i : Equation n) : f.hom (evaluate Q b (ambientAlgebra Q b) (e.homEquiv (𝟙 _)) i) =
      evaluate Q b A x i := by
    rw [evaluate_map, ← Corepresented.homEquiv_comp' e, Category.id_comp, Equiv.apply_symm_apply]
  rw [mem_iff_evaluate_zero Q b A x]
  constructor
  · intro hx
    have hle : ideal Q b ≤ RingHom.ker f.hom.toRingHom := by
      rw [ideal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact (h i).trans (hx i)
    exact fun c hc => hle hc
  · intro hx i
    rw [← h i]
    exact hx _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The affine group scheme of Clifford lifts with their determinant-one vector action. -/
abbrev groupScheme : GroupScheme (Spec S) := Corepresented.cutGroupScheme (isCutOutBy Q b)

/-- The inclusion into the ambient affine group of tensor units and invertible matrices. -/
def inclusion : groupScheme Q b ⟶ Corepresented.groupScheme
    (ambientFunctor (n := n) Q) (ambientCorepresentation Q b) :=
  Corepresented.cutHom (isCutOutBy Q b)

/-- The inclusion is a closed subgroup scheme. -/
theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion Q b) :=
  Corepresented.isClosedSubgroup_cutHom (isCutOutBy Q b)

/-- Every affine point is the stated pair over its actual coefficient algebra. -/
def affinePairEquiv (A : CommAlgCat.{u} S) : (groupScheme Q b).affinePoints A ≃*
    coefficientSubgroup Q b A :=
  Corepresented.affinePointsEquiv (Corepresented.cutFunctor (isCutOutBy Q b))
    (Corepresented.cutCorepresentableBy (isCutOutBy Q b)) A

/-- Changing coefficients on a point changes both components of the pair. -/
theorem affinePairEquiv_naturality {A B : CommAlgCat.{u} S} (f : A ⟶ B)
    (x : (groupScheme Q b).affinePoints A) :
    (affinePairEquiv Q b B (GroupScheme.affinePointMap (groupScheme Q b) f x)).val =
      (ambientFunctor (n := n) Q).map f (affinePairEquiv Q b A x).val :=
  congrArg Subtype.val (Corepresented.affinePointsEquiv_naturality
    (Corepresented.cutFunctor (isCutOutBy Q b)) (Corepresented.cutCorepresentableBy (isCutOutBy Q b)) f x)

private def projectionNat : Corepresented.cutFunctor (isCutOutBy Q b) ⟶ matrixFunctor (n := n) where
  app A := GrpCat.ofHom ((MonoidHom.snd _ _).comp (coefficientSubgroup Q b A).subtype)
  naturality _ _ _ := by rfl

/-- The actual homomorphism giving the vector-action matrix. -/
def matrixProjection : groupScheme Q b ⟶ GeneralLinear.groupScheme (Fin n) S :=
  Corepresented.groupSchemeMap (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
    (GeneralLinear.corepresentableBy (Fin n) S) (projectionNat Q b)

/-- Its affine points project to the matrix entry of the pair. -/
theorem affine_matrixProjection (A : CommAlgCat.{u} S) (x : (groupScheme Q b).affinePoints A) :
    Corepresented.affinePointsEquiv (matrixFunctor (n := n))
        (GeneralLinear.corepresentableBy (Fin n) S) A (x ≫ (matrixProjection Q b).hom.hom) =
      (affinePairEquiv Q b A x).val.2 :=
  Corepresented.groupSchemeMap_affinePoints (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
    (GeneralLinear.corepresentableBy (Fin n) S) (projectionNat Q b) x

end Langlands.GroupScheme.CliffordSpin
