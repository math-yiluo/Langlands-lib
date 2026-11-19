import Langlands.GroupScheme.Quaternionic.ScalarMatrixCoordinates

/-! # All-test matrix coordinates of scalar norm-one isometry groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints

open FirstKindInvolution ScalarMatrixCoordinates

variable {K : Type u} [Field K] {i j : Type}
  [Fintype i] [DecidableEq i] [Nonempty i]
  [Fintype j] [DecidableEq j] [Nonempty j]

/-- Ordinary matrix units of the ambient matrix-algebra unit group on every relative test. -/
def ambientEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (CentralSimpleUnits.groupScheme K (Matrix i i K)).X) ≃* GL i Γ(T.left, ⊤) :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix i i K)) T).trans
    (Units.mapEquiv (matrixEquiv K ((algΓ (CommRingCat.of K)).obj T).unop).toMulEquiv)

variable (q : (scalar K).QuadraticForms i)

/-- The invertible matrix of an actual scalar norm-one isometry point. -/
def matrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((scalar K).normOneIsometryGroup q).X) →* GL i Γ(T.left, ⊤) :=
  (ambientEquiv T).toMonoidHom.comp (((pointsMap ((scalar K).normOneIsometryAmbientι q)).app
    (op T)).hom)

@[simp] theorem matrix_apply (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((scalar K).normOneIsometryGroup q).X) :
    matrix q T x = ambientEquiv T (x ≫ ((scalar K).normOneIsometryAmbientι q).hom.hom) := rfl

/-- Pullback of any test induces entrywise coefficient pullback. -/
theorem matrix_naturality {T T' : Over (Spec (CommRingCat.of K))} (b : T' ⟶ T)
    (x : T ⟶ ((scalar K).normOneIsometryGroup q).X) :
    matrix q T' (b ≫ x) = Matrix.GeneralLinearGroup.map b.left.appTop.hom (matrix q T x) := by
  apply Units.ext
  rw [matrix_apply, matrix_apply, Category.assoc]
  change matrixEquiv K _ ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix i i K))
      T' (b ≫ (x ≫ ((scalar K).normOneIsometryAmbientι q).hom.hom))).val) = _
  rw [FiniteAlgebraUnits.pointsEquiv_naturality]
  exact matrixEquiv_naturality K _ _

/-- Matrix coordinates determine the actual point. -/
theorem matrix_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (matrix q T) := by
  intro x y h
  apply (cancel_mono ((scalar K).normOneIsometryAmbientι q).hom.hom).mp
  exact (ambientEquiv T).injective h

/-- The full image over an arbitrary relative test is given by the quadratic defect
and determinant equations over that test's relative global sections. -/
theorem mem_range_matrix_iff (Q : Matrix i i K) (hQ : Submodule.Quotient.mk Q = q)
    (T : Over (Spec (CommRingCat.of K))) (g : GL i Γ(T.left, ⊤)) :
    g ∈ (matrix q T).range ↔
      let D : Matrix i i Γ(T.left, ⊤) := Q.map (algebraMap K ((algΓ (CommRingCat.of K)).obj T).unop)
      OrthogonalMatrix.IsAlt (g.val * D * g.valᵀ - D) ∧ g.val.det = 1 := by
  let z := (ambientEquiv T).symm g
  have hg : ambientEquiv T z = g := (ambientEquiv T).apply_symm_apply g
  have hz : g ∈ (matrix q T).range ↔
      z ∈ (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι q)).carrier T := by
    rw [SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (ambientEquiv T).injective (hx.trans hg.symm)⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [matrix_apply, hx, hg]
  rw [hz, mem_range_normOneIsometryAmbientι_iff K q Q hQ]
  change (let D : Matrix i i Γ(T.left, ⊤) := Q.map (algebraMap K ((algΓ (CommRingCat.of K)).obj T).unop)
    OrthogonalMatrix.IsAlt ((ambientEquiv T z).val * D * (ambientEquiv T z).valᵀ - D) ∧
      (ambientEquiv T z).val.det = 1) ↔ _
  rw [hg]

/-- The chart is a multiplicative equivalence onto its exact matrix image. -/
def rangeEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((scalar K).normOneIsometryGroup q).X) ≃* (matrix q T).range :=
  MulEquiv.ofBijective (matrix q T).rangeRestrict
    ⟨fun _ _ h => matrix_injective q T (congrArg Subtype.val h),
      (matrix q T).rangeRestrict_surjective⟩

private theorem map_range_eq (q' : (scalar K).QuadraticForms j)
    (T : Over (Spec (CommRingCat.of K))) (e : GL i Γ(T.left, ⊤) ≃* GL j Γ(T.left, ⊤))
    (he : ∀ g, e g ∈ (matrix q' T).range ↔ g ∈ (matrix q T).range) :
    (matrix q T).range.map e.toMonoidHom = (matrix q' T).range := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (he a).mpr ha
  · intro hg
    exact ⟨e.symm g, (he _).mp ((e.apply_symm_apply g).symm ▸ hg), e.apply_symm_apply g⟩

/-- A matrix equivalence carrying the two exact images induces a point equivalence. -/
def pointsEquiv (q' : (scalar K).QuadraticForms j) (T : Over (Spec (CommRingCat.of K)))
    (e : GL i Γ(T.left, ⊤) ≃* GL j Γ(T.left, ⊤))
    (he : ∀ g, e g ∈ (matrix q' T).range ↔ g ∈ (matrix q T).range) :
    (T ⟶ ((scalar K).normOneIsometryGroup q).X) ≃*
      (T ⟶ ((scalar K).normOneIsometryGroup q').X) :=
  (rangeEquiv q T).trans <| (e.subgroupMap _).trans <|
    (MulEquiv.subgroupCongr (map_range_eq q q' T e he)).trans (rangeEquiv q' T).symm

/-- The induced point equivalence has the prescribed matrix formula. -/
theorem matrix_pointsEquiv (q' : (scalar K).QuadraticForms j) (T : Over (Spec (CommRingCat.of K)))
    (e : GL i Γ(T.left, ⊤) ≃* GL j Γ(T.left, ⊤))
    (he : ∀ g, e g ∈ (matrix q' T).range ↔ g ∈ (matrix q T).range)
    (x : T ⟶ ((scalar K).normOneIsometryGroup q).X) :
    matrix q' T (pointsEquiv q q' T e he x) = e (matrix q T x) := by
  let y := MulEquiv.subgroupCongr (map_range_eq q q' T e he)
    (e.subgroupMap _ (rangeEquiv q T x))
  exact congrArg Subtype.val ((rangeEquiv q' T).apply_symm_apply y)

end Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints
