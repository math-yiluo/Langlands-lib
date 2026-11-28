import Langlands.GroupScheme.Quaternionic.SplittingMatrix
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.FiniteFreeAlgebraUnits
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.SymplecticInnerForm.AlgebraTransport

/-! # Scalar extension of the division-algebra unitary Gram equation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
set_option autoImplicit false

section Coordinates

variable {F D L : Type u} [Field F] [DivisionRing D] [Algebra F D] [Field L] [Algebra F L]
  {I : Type} [Fintype I] [DecidableEq I]

local notation "A" => Matrix I I D
local notation "Dₗ" => L ⊗[F] D
local notation "Aₗ" => Matrix I I Dₗ

private def gramCoefficientAlgEquiv : L ⊗[F] A ≃ₐ[L] Aₗ :=
  AlgEquiv.ofRingEquiv (f := (coefficientEquiv F D L).toRingEquiv) fun c => by
    ext i j
    change coefficientEquiv F D L (c ⊗ₜ[F] (1 : A)) i j = (algebraMap L Aₗ c) i j
    rw [coefficientEquiv_tmul, Matrix.algebraMap_matrix_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · simp

variable (τ : FirstKindInvolution F D) (H : A)

private def gramTensorChart (R : Type u) [CommRing R] [Algebra F R] [Algebra L R] [IsScalarTower F L R] :
    R ⊗[F] A ≃+* R ⊗[L] Aₗ :=
  (FiniteFreeAlgebraUnits.baseChangeTensorEquiv (R := CommRingCat.of F) A (CommRingCat.of L) R).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
      (gramCoefficientAlgEquiv (F := F) (D := D) (L := L) (I := I))).toRingEquiv

private theorem gramTensorChart_tmul (R : Type u) [CommRing R] [Algebra F R]
    [Algebra L R] [IsScalarTower F L R] (r : R) (M : A) :
    gramTensorChart (F := F) (D := D) (L := L) (I := I) R (r ⊗ₜ[F] M) =
      r ⊗ₜ[L] coefficientEquiv F D L ((1 : L) ⊗ₜ[F] M) := by
  rw [gramTensorChart, RingEquiv.trans_apply, FiniteFreeAlgebraUnits.baseChangeTensorEquiv_tmul]
  rfl

private theorem gramTensorChart_adjoint (R : Type u) [CommRing R] [Algebra F R]
    [Algebra L R] [IsScalarTower F L R] (x : R ⊗[F] A) :
    gramTensorChart (L := L) R ((τ.matrix I).baseChange R x) =
      ((τ.baseChange L).matrix I).baseChange R (gramTensorChart (L := L) R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    rw [FirstKindInvolution.baseChange_tmul, gramTensorChart_tmul,
      gramTensorChart_tmul, FirstKindInvolution.baseChange_tmul]
    congr 1
    ext i j
    simp only [coefficientEquiv_tmul, FirstKindInvolution.matrix_apply,
      FirstKindInvolution.baseChange_tmul]
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]

private theorem gramTensorChart_natural {R S : Type u} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] [Algebra L R] [Algebra L S]
    [IsScalarTower F L R] [IsScalarTower F L S]
    (f : R →ₐ[F] S) (g : R →ₐ[L] S) (h : ∀ r, f r = g r) (x : R ⊗[F] A) :
    gramTensorChart S (Algebra.TensorProduct.map f (AlgHom.id F A) x) =
      Algebra.TensorProduct.map g (AlgHom.id L Aₗ) (gramTensorChart R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, gramTensorChart_tmul, h]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

variable [FiniteDimensional F D]

local notation "b" => WeilGm.baseMap (CommRingCat.of F) (CommRingCat.of L)
local notation "U" => FiniteAlgebraUnits.groupScheme (Module.finBasis F A)
local notation "Uₗ" => FiniteAlgebraUnits.groupScheme (Module.finBasis L Aₗ)
local notation "Rₜ" T => WeilGm.restrictedSections (CommRingCat.of F) (CommRingCat.of L) T

private local instance restrictedAlgebra (T : Over (Spec (CommRingCat.of L))) : Algebra L (Rₜ T) :=
  WeilGm.restrictedSectionsAlgebra (CommRingCat.of F) (CommRingCat.of L) T

private local instance restrictedTower (T : Over (Spec (CommRingCat.of L))) : IsScalarTower F L (Rₜ T) :=
  WeilGm.restrictedSectionsScalarTower (CommRingCat.of F) (CommRingCat.of L) T

private def gramUnitPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ ((GroupScheme.baseChange b).obj U).X) ≃* (T ⟶ (Uₗ).X) :=
  (baseChangePointsEquiv b U T).trans
    ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis F A) ((Over.map b).obj T)).trans
      ((Units.mapEquiv (gramTensorChart (I := I) (Rₜ T)).toMulEquiv).trans
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis L Aₗ) T).symm))

private theorem gramUnitPointsEquiv_natural {T T' : Over (Spec (CommRingCat.of L))}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange b).obj U).X) :
    gramUnitPointsEquiv T' (a ≫ x) = a ≫ gramUnitPointsEquiv T x := by
  apply (FiniteAlgebraUnits.pointsEquiv (Module.finBasis L Aₗ) T').injective
  simp only [gramUnitPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    baseChangePointsEquiv_naturality, FiniteAlgebraUnits.pointsEquiv_naturality]
  apply Units.ext
  exact gramTensorChart_natural (((algΓ (CommRingCat.of F)).map ((Over.map b).map a)).unop.hom)
    (((algΓ (CommRingCat.of L)).map a).unop.hom) (fun _ => rfl) _

end Coordinates

/-- Scalar extension of the unitary group is the isometry cut defined by the
scalar-extended Gram matrix and conjugate transpose. -/
def UnitaryGramFieldExtensionStatement : Prop :=
  ∀ (F D L : Type u) [Field F] [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Field L] [Algebra F L] (I : Type) [Fintype I] [DecidableEq I]
    (τ : FirstKindInvolution F D) (H : Matrix I I D),
    Nonempty ((GroupScheme.baseChange (WeilGm.baseMap (CommRingCat.of F) (CommRingCat.of L))).obj
        (τ.unitaryGroup H) ≅
      IsometryCut.groupScheme (τ := (τ.baseChange L).matrix I) (M := ⊥)
        IsometryCut.isStable_bot (coefficientEquiv F D L ((1 : L) ⊗ₜ[F] H)))

theorem nonempty_unitaryGramFieldExtensionIso : UnitaryGramFieldExtensionStatement.{u} := by
  intro F D L _ _ _ _ _ _ I _ _ τ H
  refine ⟨?_⟩
  let b := WeilGm.baseMap (CommRingCat.of F) (CommRingCat.of L)
  let B := GroupScheme.baseChange b
  let A := Matrix I I D
  let Aₗ := Matrix I I (L ⊗[F] D)
  let M := coefficientEquiv F D L ((1 : L) ⊗ₜ[F] H)
  let τₗ := τ.baseChange L
  let i := τ.unitaryGroupι H
  let basis := Module.finBasis F A
  let basisₗ := Module.finBasis L Aₗ
  let E : B.obj (FiniteAlgebraUnits.groupScheme basis) ≅ FiniteAlgebraUnits.groupScheme basisₗ :=
    isoOfPoints gramUnitPointsEquiv gramUnitPointsEquiv_natural
  have hi : IsClosedSubgroup (B.map i) := (τ.isClosedSubgroup_unitaryGroupι H).baseChange b
  apply (hi.comp_iso E).sourceIsoOfRangeEq
    (IsometryCut.isClosedSubgroup_inclusion (τ := τₗ.matrix I) (M := ⊥) IsometryCut.isStable_bot M)
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro z
  let x := z ≫ E.inv.hom.hom
  have hx : x ≫ E.hom.hom.hom = z := by
    simp only [x, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [← hx]
  have hpre :
      (x ≫ E.hom.hom.hom) ∈ (SubgroupFunctor.range (B.map i ≫ E.hom)).carrier T ↔
        x ∈ (SubgroupFunctor.range (B.map i)).carrier T := by
    simp only [SubgroupFunctor.mem_range, Grp.comp_hom_hom, ← Category.assoc]
    exact exists_congr fun y => (cancel_mono E.hom.hom.hom)
  have hbase :
      x ∈ (SubgroupFunctor.range (B.map i)).carrier T ↔
        baseChangePointsEquiv b (FiniteAlgebraUnits.groupScheme basis) T x ∈
          (SubgroupFunctor.range i).carrier ((Over.map b).obj T) := by
    simp only [SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨baseChangePointsEquiv b (τ.unitaryGroup H) T y,
        (baseChangePointsEquiv_comp b i T y).symm.trans (congrArg _ hy)⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y', rfl⟩ := (baseChangePointsEquiv b (τ.unitaryGroup H) T).surjective y
      exact ⟨y', (baseChangePointsEquiv b (FiniteAlgebraUnits.groupScheme basis) T).injective
        ((baseChangePointsEquiv_comp b i T y').trans hy)⟩
  rw [hpre, hbase, τ.mem_range_unitaryGroupι_iff, IsometryCut.mem_range_inclusion_iff,
    Submodule.baseChange_bot, Submodule.mem_bot, IsometryCut.defect, sub_eq_zero]
  let R : Type u := WeilGm.restrictedSections (CommRingCat.of F) (CommRingCat.of L) T
  let : Algebra L R := WeilGm.restrictedSectionsAlgebra (CommRingCat.of F) (CommRingCat.of L) T
  let : IsScalarTower F L R := WeilGm.restrictedSectionsScalarTower
    (CommRingCat.of F) (CommRingCat.of L) T
  let g : (R ⊗[F] A)ˣ := FiniteAlgebraUnits.pointsEquiv basis ((Over.map b).obj T)
    (baseChangePointsEquiv b (FiniteAlgebraUnits.groupScheme basis) T x)
  let gₗ : (R ⊗[L] Aₗ)ˣ := FiniteAlgebraUnits.pointsEquiv basisₗ T (x ≫ E.hom.hom.hom)
  let C : R ⊗[F] A ≃+* R ⊗[L] Aₗ := gramTensorChart R
  have he : gₗ.val = C g.val := by
    dsimp only [gₗ, E]
    rw [comp_isoOfPoints_hom]
    change (FiniteAlgebraUnits.pointsEquiv basisₗ T
      ((FiniteAlgebraUnits.pointsEquiv basisₗ T).symm (Units.mapEquiv C.toMulEquiv g))).val = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  change g.val * ((1 : R) ⊗ₜ[F] H) * (τ.matrix I).baseChange R g.val =
      (1 : R) ⊗ₜ[F] H ↔
    gₗ.val * ((1 : R) ⊗ₜ[L] M) * (τₗ.matrix I).baseChange R gₗ.val =
      (1 : R) ⊗ₜ[L] M
  rw [he]
  change _ ↔ gramTensorChart R g.val * _ * _ = _
  rw [← gramTensorChart_tmul R (1 : R) H, ← gramTensorChart_adjoint τ, ← _root_.map_mul,
    ← _root_.map_mul]
  exact C.injective.eq_iff.symm

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
