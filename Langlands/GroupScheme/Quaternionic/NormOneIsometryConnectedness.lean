import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof
import Langlands.GroupScheme.Quaternionic.NormOneIsometry
import Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints
import Langlands.GroupScheme.CliffordSpin.ScalarNormOneConnectedness
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # Connectedness of quaternionic norm-one isometry groups

After splitting the quaternion algebra, the base change of the reduced-norm-one isometry
group of a quaternionic quadratic form is the scalar norm-one isometry group of the split
Gram matrix. The scalar group is connected, and connectedness descends along the field
extension.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic

namespace NormOneSplit

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

open FirstKindInvolution MoritaIsometry

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D] {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  {m : ℕ} [NeZero m] (q : σ.QuadraticForms (Fin m))

/-- The base change of the norm-one isometry group to `L`. -/
abbrev baseChangeNormOne : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.normOneIsometryGroup q)

/-- The unit of `Γ(T, ⊤) ⊗[K] M_m(D)` underlying a point of the base change. -/
def unitPoint (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeNormOne σ q (L := L)).X) →*
      (restrictedSections K L T ⊗[K] Matrix (Fin m) (Fin m) D)ˣ :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix (Fin m) (Fin m) D))
      ((Over.map (scalarBaseMap K L)).obj T)).toMonoidHom.comp
    (((yonedaGrp.map (σ.normOneIsometryAmbientι q)).app
        (Opposite.op ((Over.map (scalarBaseMap K L)).obj T))).hom.comp
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.normOneIsometryGroup q)
        T).toMonoidHom)

theorem unitPoint_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    unitPoint σ q T x = FiniteAlgebraUnits.pointsEquiv
      (Module.finBasis K (Matrix (Fin m) (Fin m) D)) ((Over.map (scalarBaseMap K L)).obj T)
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.normOneIsometryGroup q) T x ≫
        (σ.normOneIsometryAmbientι q).hom.hom) :=
  rfl

/-- The split matrix `Φ(u)` of a point of the base change. -/
def matrixPoint (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeNormOne σ q (L := L)).X) →* GL (Fin (2 * m)) Γ(T.left, ⊤) :=
  (Units.map (chartN e m (restrictedSections K L T)).toMonoidHom).comp (unitPoint σ q T)

theorem matrixPoint_val (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    (matrixPoint e σ q T x : Matrix (Fin (2 * m)) (Fin (2 * m)) Γ(T.left, ⊤)) =
      chartN e m (restrictedSections K L T) (unitPoint σ q T x) :=
  rfl

theorem unitPoint_injective (T : Over (Spec (CommRingCat.of L))) :
    Function.Injective (unitPoint σ q T) := by
  intro x y h
  rw [unitPoint_apply, unitPoint_apply] at h
  have h2 := (FiniteAlgebraUnits.pointsEquiv _ _).injective h
  exact (GroupScheme.baseChangePointsEquiv _ _ T).injective ((cancel_mono _).1 h2)

theorem matrixPoint_injective (T : Over (Spec (CommRingCat.of L))) :
    Function.Injective (matrixPoint e σ q T) := by
  intro x y h
  apply unitPoint_injective σ q T
  apply Units.ext
  apply (chartN e m (restrictedSections K L T)).injective
  rw [← matrixPoint_val, ← matrixPoint_val, h]

theorem det_chartN (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    (chartN e m R x).det = CentralSimple.reducedNorm K (Matrix (Fin m) (Fin m) D) R x := by
  rw [chartN_apply, Matrix.det_reindex_self, reducedNorm_eq_det_matrixChartR e R]

theorem unitPoint_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    unitPoint σ q T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.map
        ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom
        (AlgHom.id K (Matrix (Fin m) (Fin m) D))).toMonoidHom (unitPoint σ q T x) := by
  rw [unitPoint_apply, unitPoint_apply, GroupScheme.baseChangePointsEquiv_naturality,
    Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]

theorem matrixPoint_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    matrixPoint e σ q T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (matrixPoint e σ q T x) := by
  apply Units.ext
  change chartN e m (restrictedSections K L T') (unitPoint σ q T' (a ≫ x)) =
    (chartN e m (restrictedSections K L T) (unitPoint σ q T x)).map a.left.appTop.hom
  rw [unitPoint_naturality]
  let f : restrictedSections K L T →ₐ[L] restrictedSections K L T' :=
    { ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom.toRingHom
      with commutes' := fun c => ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes c }
  exact chartN_naturality e m f (unitPoint σ q T x)

/-- The scalar quadratic form over `L` represented by the split Gram matrix. -/
abbrev gramQ : (scalar L).QuadraticForms (Fin (2 * m)) :=
  Submodule.Quotient.mk (gramN e σ m (Quotient.out q))

local instance neZero_two_mul : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩

variable (hσ : finrank K σ.symmetricSubspace = 3)
include hσ

/-- The image of the split matrix chart on points of the base change: the matrices of
determinant one whose quadratic defect for the split Gram matrix is alternating. -/
theorem mem_range_matrixPoint_iff (T : Over (Spec (CommRingCat.of L)))
    (g : GL (Fin (2 * m)) Γ(T.left, ⊤)) :
    g ∈ (matrixPoint e σ q T).range ↔
      let C : Matrix (Fin (2 * m)) (Fin (2 * m)) Γ(T.left, ⊤) :=
        (gramN e σ m (Quotient.out q)).map
          (algebraMap L ((algΓ (CommRingCat.of L)).obj T).unop)
      OrthogonalMatrix.IsAlt (g.val * C * g.valᵀ - C) ∧ g.val.det = 1 := by
  let R := restrictedSections K L T
  let T' := (Over.map (scalarBaseMap K L)).obj T
  have hQ : (Submodule.Quotient.mk (Quotient.out q) : σ.QuadraticForms (Fin m)) = q :=
    Quotient.out_eq q
  constructor
  · rintro ⟨x, rfl⟩
    have hmem := (σ.mem_range_normOneIsometryAmbientι_iff_equations q (Quotient.out q) hQ
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.normOneIsometryGroup q) T x ≫
        (σ.normOneIsometryAmbientι q).hom.hom)).1 (SubgroupFunctor.mem_range.2 ⟨_, rfl⟩)
    have hiso : unitPoint σ q T x ∈ σ.isometryUnits (Quotient.out q) R := hmem.1
    obtain ⟨Y, hY⟩ := (mem_isometryUnits_iff e σ m R hσ (Quotient.out q) _).1 hiso
    refine ⟨⟨Y, ?_⟩, ?_⟩
    · exact hY
    · change (chartN e m R (unitPoint σ q T x)).det = 1
      rw [det_chartN]
      have h2 := hmem.2
      exact congrArg Units.val h2
  · rintro ⟨⟨Y, hY⟩, hdet⟩
    let u : (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ :=
      Units.map (chartN e m R).symm.toMonoidHom g
    have hu : chartN e m R (u : R ⊗[K] Matrix (Fin m) (Fin m) D) = g.val := by
      change chartN e m R ((chartN e m R).symm g.val) = _
      rw [RingEquiv.apply_symm_apply]
    have hiso : u ∈ σ.isometryUnits (Quotient.out q) R := by
      rw [mem_isometryUnits_iff e σ m R hσ]
      exact ⟨Y, by rw [hu]; exact hY⟩
    have hnorm : CentralSimple.reducedNormUnits K (Matrix (Fin m) (Fin m) D) R u = 1 := by
      apply Units.ext
      rw [CentralSimple.reducedNormUnits_val, ← det_chartN e R, hu, hdet, Units.val_one]
    let y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix (Fin m) (Fin m) D)) T').symm u
    have hy : y ∈ (SubgroupFunctor.range (σ.normOneIsometryAmbientι q)).carrier T' := by
      rw [σ.mem_range_normOneIsometryAmbientι_iff_equations q (Quotient.out q) hQ,
        MulEquiv.apply_symm_apply]
      exact ⟨hiso, hnorm⟩
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hy
    refine ⟨(GroupScheme.baseChangePointsEquiv _ _ T).symm z, Units.ext ?_⟩
    rw [matrixPoint_val, unitPoint_apply, MulEquiv.apply_symm_apply, hz, MulEquiv.apply_symm_apply,
      hu]

theorem range_matrixPoint_eq (T : Over (Spec (CommRingCat.of L))) :
    (matrixPoint e σ q T).range = (ScalarNormOnePoints.matrix (gramQ e σ q) T).range := by
  ext g
  rw [mem_range_matrixPoint_iff e σ q hσ T g,
    ScalarNormOnePoints.mem_range_matrix_iff _ (gramN e σ m (Quotient.out q)) rfl T g]

/-- Points of the base change of the quaternionic norm-one group are points of the scalar
norm-one group of the split Gram matrix, with the same matrix. -/
def splitPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeNormOne σ q (L := L)).X) ≃*
      (T ⟶ ((scalar L).normOneIsometryGroup (gramQ e σ q)).X) :=
  (MulEquiv.ofBijective (matrixPoint e σ q T).rangeRestrict
      ⟨fun _ _ h => matrixPoint_injective e σ q T (congrArg Subtype.val h),
        (matrixPoint e σ q T).rangeRestrict_surjective⟩).trans <|
    (MulEquiv.subgroupCongr (range_matrixPoint_eq e σ q hσ T)).trans
      (ScalarNormOnePoints.rangeEquiv (gramQ e σ q) T).symm

theorem matrix_splitPointsEquiv (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    ScalarNormOnePoints.matrix (gramQ e σ q) T (splitPointsEquiv e σ q hσ T x) =
      matrixPoint e σ q T x :=
  congrArg Subtype.val ((ScalarNormOnePoints.rangeEquiv (gramQ e σ q) T).apply_symm_apply _)

theorem splitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeNormOne σ q (L := L)).X) :
    splitPointsEquiv e σ q hσ T' (a ≫ x) = a ≫ splitPointsEquiv e σ q hσ T x := by
  apply ScalarNormOnePoints.matrix_injective (gramQ e σ q) T'
  rw [matrix_splitPointsEquiv, ScalarNormOnePoints.matrix_naturality, matrix_splitPointsEquiv,
    matrixPoint_naturality]

/-- The base change of the quaternionic norm-one isometry group to a splitting field is the
scalar norm-one isometry group of the split Gram matrix. -/
def splitIso : baseChangeNormOne σ q (L := L) ≅ (scalar L).normOneIsometryGroup (gramQ e σ q) :=
  isoOfPoints (splitPointsEquiv e σ q hσ) (splitPointsEquiv_naturality e σ q hσ)

/-- In characteristic zero the quaternionic norm-one isometry group of a nondegenerate form is
connected. -/
theorem connectedSpace_normOneIsometryGroup (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
    [CharZero K] (hq : σ.IsNondegenerateQuadratic q) :
    ConnectedSpace (σ.normOneIsometryGroup q).X.left := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : Invertible (2 : L) := invertibleOfNonzero two_ne_zero
  have : ConnectedSpace ((scalar L).normOneIsometryGroup (gramQ e σ q)).X.left :=
    CliffordSpin.connectedSpace_scalarNormOne (gramQ e σ q)
      (isNondegenerateQuadratic_gramN e σ m hσ q _ (Quotient.out_eq q) hq)
  have hL : ConnectedSpace (baseChangeNormOne σ q (L := L)).X.left :=
    DynamicConnected.connectedSpace_of_iso (splitIso e σ q hσ)
  have : Surjective (scalarBaseMap K L) := (fieldExtension_fpqc K L).1
  exact connectedSpace_of_baseChange (scalarBaseMap K L) _ hL

end NormOneSplit

end Langlands.GroupScheme.Quaternionic

namespace Langlands.GroupScheme

open Quaternionic

/-- The reduced-norm-one isometry group of a nondegenerate quadratic form over a quaternion
division algebra with an orthogonal involution is connected, in characteristic zero. -/
def QuaternionicNormOneIsometryConnectednessStatement : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D],
    Module.finrank K D = 4 → ∀ (σ : FirstKindInvolution K D),
    Module.finrank K σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n] (q : σ.QuadraticForms (Fin n)), σ.IsNondegenerateQuadratic q →
      ConnectedSpace (σ.normOneIsometryGroup q).X.left

/-- Proof of `QuaternionicNormOneIsometryConnectednessStatement`. -/
theorem quaternionicNormOneIsometryConnectedness :
    QuaternionicNormOneIsometryConnectednessStatement.{u} := by
  intro K _ _ D _ _ _ _ hD σ hσ m _ q hq
  let L := CentralSimple.finiteGaloisSplittingField K D
  let e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L :=
    (CentralSimple.finiteGaloisSplittingChart K D).trans
      (Matrix.reindexAlgEquiv L L (finCongr (FirstKindInvolution.reducedDegree_eq_two hD)))
  exact NormOneSplit.connectedSpace_normOneIsometryGroup σ q hσ e hq

end Langlands.GroupScheme
