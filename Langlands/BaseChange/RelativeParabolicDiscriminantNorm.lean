import Langlands.BaseChange.RelativeParabolicDiscriminant
import Langlands.BaseChange.RegularLeviNormRepresentative
import Langlands.BaseChange.CyclicSemilinearDeterminant
import Mathlib.RingTheory.Norm.Transitivity

/-! # Equality of the relative discriminants at an exact cyclic norm -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear (BlockShape)

universe u v

variable {n : ℕ} (B : BlockShape n)

private abbrev offBlockRank := Fintype.card (OffBlockPosition B)

private theorem even_offBlockRank : Even (offBlockRank B) := by
  let p (x : OffBlockPosition B) := B.coordinateBlock x.val.1 < B.coordinateBlock x.val.2
  let s : Equiv.Perm (OffBlockPosition B) :=
    { toFun := fun x => ⟨x.val.swap, x.property.symm⟩
      invFun := fun x => ⟨x.val.swap, x.property.symm⟩
      left_inv := fun x => Subtype.ext (Prod.swap_swap x.val)
      right_inv := fun x => Subtype.ext (Prod.swap_swap x.val) }
  let e : {x // p x} ≃ {x // ¬ p x} := s.subtypeEquiv fun x => by
    change (_ < _) ↔ ¬ (_ < _)
    rw [not_lt]
    exact lt_iff_le_and_ne.trans (and_iff_left x.property)
  refine ⟨Fintype.card {x // p x}, ?_⟩
  change Fintype.card (OffBlockPosition B) = _
  rw [← Fintype.card_congr (Equiv.sumCompl p), Fintype.card_sum, ← Fintype.card_congr e]

section Coordinates

variable (K : Type u) [Field K]

private noncomputable def offBlockIndex : OffBlockPosition B ≃ Fin (offBlockRank B) :=
  Fintype.equivFin _

private noncomputable def relativeLieFinCoordinates :
    RelativeParabolicLieQuotient B K ≃ₗ[K] (Fin (offBlockRank B) → K) :=
  (relativeParabolicLieCoordinates B K).trans
    { toFun := fun x i => x ((offBlockIndex B).symm i)
      invFun := fun x p => x (offBlockIndex B p)
      left_inv := fun x => by funext p; simp
      right_inv := fun x => by funext i; simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem relativeLieFinCoordinates_apply (x : RelativeParabolicLieQuotient B K)
    (i : Fin (offBlockRank B)) :
    relativeLieFinCoordinates B K x i = relativeParabolicLieCoordinates B K x ((offBlockIndex B).symm i) :=
  rfl

private def relativeAdjointHom : B.Levi K →* Module.End K (RelativeParabolicLieQuotient B K) where
  toFun := relativeParabolicAdjoint B K
  map_one' := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (blockDiagonalLieSubmodule B K) x ?_
    intro X
    rw [relativeParabolicAdjoint_mk]
    simp [linearAdjoint]
  map_mul' x y := by
    apply LinearMap.ext
    intro a
    refine Submodule.Quotient.induction_on (blockDiagonalLieSubmodule B K) a ?_
    intro X
    rw [Module.End.mul_apply, relativeParabolicAdjoint_mk, relativeParabolicAdjoint_mk,
      relativeParabolicAdjoint_mk]
    congr 1
    simp [linearAdjoint, mul_inv_rev, mul_assoc]

private noncomputable def relativeAdjointGL : B.Levi K →* GeneralLinear (offBlockRank B) K :=
  (LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (((relativeLieFinCoordinates B K).conjAlgEquiv K).toMonoidHom.comp
      (relativeAdjointHom B K))).toHomUnits

private theorem relativeAdjointGL_val (m : B.Levi K) :
    (relativeAdjointGL B K m).val = LinearMap.toMatrixAlgEquiv'
      ((relativeLieFinCoordinates B K).conj (relativeParabolicAdjoint B K m)) := rfl

private theorem toLin_relativeAdjointGL (m : B.Levi K) :
    Matrix.toLinAlgEquiv' (relativeAdjointGL B K m).val =
      (relativeLieFinCoordinates B K).conj (relativeParabolicAdjoint B K m) := by
  rw [relativeAdjointGL_val, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']

private theorem relativeAdjointGL_apply (m : B.Levi K) (i j : Fin (offBlockRank B)) :
    let p := (offBlockIndex B).symm i
    let q := (offBlockIndex B).symm j
    relativeAdjointGL B K m i j =
      B.leviEmbedding K m p.val.1 q.val.1 * B.leviEmbedding K m⁻¹ q.val.2 p.val.2 := by
  let p := (offBlockIndex B).symm i
  let q := (offBlockIndex B).symm j
  let e := relativeLieFinCoordinates B K
  let X : Matrix (Fin n) (Fin n) K := Matrix.single q.val.1 q.val.2 1
  have hX : e (Submodule.Quotient.mk X) = Pi.single j 1 := by
    funext k
    rw [relativeLieFinCoordinates_apply, relativeParabolicLieCoordinates_mk, offBlockEntries_apply]
    by_cases hk : k = j
    · subst k
      simp [X, q]
    · have hne : ¬(q.val.1 = ((offBlockIndex B).symm k).val.1 ∧
          q.val.2 = ((offBlockIndex B).symm k).val.2) := by
        intro h
        exact hk ((offBlockIndex B).symm.injective (Subtype.ext (Prod.ext h.1 h.2))).symm
      dsimp only [X]
      rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, Pi.single_eq_of_ne hk]
  change (relativeAdjointGL B K m).val i j = _
  rw [relativeAdjointGL_val, LinearMap.toMatrixAlgEquiv'_apply, LinearEquiv.conj_apply_apply,
    ← hX, LinearEquiv.symm_apply_apply, relativeParabolicAdjoint_mk,
    relativeLieFinCoordinates_apply, relativeParabolicLieCoordinates_mk, offBlockEntries_apply]
  change ((B.leviEmbedding K m).val * (X * ((B.leviEmbedding K m)⁻¹).val)) p.val.1 p.val.2 = _
  rw [← map_inv, Matrix.mul_apply, Finset.sum_eq_single q.val.1]
  · simp [X, p, q]
  · intro k _ hk
    dsimp only [X]
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk, mul_zero]
  · simp

private theorem relativeDiscriminant_eq_matrix (m : B.Levi K) :
    relativeParabolicDiscriminant B K m = (1 - (relativeAdjointGL B K m⁻¹).val).det := by
  let e := relativeLieFinCoordinates B K
  let R := relativeParabolicAdjoint B K m⁻¹
  rw [relativeParabolicDiscriminant, ← LinearMap.det_conj _ e]
  change (e.conj (LinearMap.id - R)).det = _
  rw [map_sub, LinearEquiv.conj_id]
  calc
    _ = (LinearMap.toMatrix' (LinearMap.id - e.conj R)).det := (LinearMap.det_toMatrix' _).symm
    _ = _ := by
      rw [map_sub, LinearMap.toMatrix'_id]
      rfl

end Coordinates

section Extension

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l : ℕ}

private theorem relativeAdjointGL_entrywiseAut (σ : E ≃ₐ[F] E) (δ : B.Levi E) :
    entrywiseAut σ (offBlockRank B) (relativeAdjointGL B E δ) =
      relativeAdjointGL B E (leviAut σ B δ) := by
  ext i j
  rw [entrywiseAut_apply_apply, relativeAdjointGL_apply, relativeAdjointGL_apply, ← map_inv,
    ← entrywiseAut_leviEmbedding, ← entrywiseAut_leviEmbedding, entrywiseAut_apply_apply,
    entrywiseAut_apply_apply, map_mul]

private theorem relativeAdjointGL_baseChange (γ : B.Levi F) :
    baseChange F E (offBlockRank B) (relativeAdjointGL B F γ) =
      relativeAdjointGL B E (fun i => baseChange F E (B.size i) (γ i)) := by
  ext i j
  rw [baseChange_apply_apply, relativeAdjointGL_apply, relativeAdjointGL_apply, ← baseChange_leviEmbedding,
    show (fun i => baseChange F E (B.size i) (γ i))⁻¹ =
      (fun i => baseChange F E (B.size i) (γ⁻¹ i)) from funext (fun i => (map_inv _ _).symm),
    ← baseChange_leviEmbedding, baseChange_apply_apply, baseChange_apply_apply, map_mul]

private theorem cyclicNorm_relativeAdjointGL (σ : E ≃ₐ[F] E) (l : ℕ) (δ : B.Levi E) :
    cyclicNorm σ l (relativeAdjointGL B E δ) =
      relativeAdjointGL B E (fun i => cyclicNorm σ l (δ i)) := by
  induction l with
  | zero => simp only [cyclicNorm_zero, ← Pi.one_def, map_one]
  | succ l ih =>
    rw [cyclicNorm_succ, ih, relativeAdjointGL_entrywiseAut, ← map_mul]
    congr 1
    funext i
    exact (cyclicNorm_succ σ l (δ i)).symm

private theorem twistedRelativeDiscriminant_eq_coordinates [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (δ : B.Levi E) :
    twistedRelativeParabolicDiscriminant B σ δ =
      LinearMap.det (coordinateFieldAut σ (Fin (offBlockRank B)) -
        (Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ⁻¹).val).restrictScalars F) := by
  let e := (relativeLieFinCoordinates B E).restrictScalars F
  rw [twistedRelativeParabolicDiscriminant, ← LinearMap.det_conj _ e]
  change (e.conj (relativeParabolicSigma B σ -
    (relativeParabolicAdjoint B E δ⁻¹).restrictScalars F)).det = _
  rw [map_sub, toLin_relativeAdjointGL]
  congr 2
  apply LinearMap.ext
  intro x
  funext i
  change relativeLieFinCoordinates B E (relativeParabolicSigma B σ (e.symm x)) i = σ (x i)
  rw [relativeLieFinCoordinates_apply, relativeParabolicLieCoordinates_sigma_apply,
    ← relativeLieFinCoordinates_apply]
  exact congrArg (fun y => σ (y i)) (e.apply_symm_apply x)

private theorem det_neg_toLin_relativeAdjointGL (δ : B.Levi E) :
    LinearMap.det (-Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ).val) =
      (GeneralLinear.determinant (relativeAdjointGL B E δ) : E) := by
  rw [← map_neg]
  change LinearMap.det (Matrix.toLin' (-(relativeAdjointGL B E δ).val)) = _
  rw [LinearMap.det_toLin', Matrix.det_neg, Fintype.card_fin, (even_offBlockRank B).neg_one_pow,
    one_mul]
  rfl

/-- At an exact cyclic norm in the actual Levi, the twisted and ordinary relative
parabolic discriminants agree as elements of the base field. -/
def RelativeParabolicDiscriminantNormStatement : Prop :=
  ∀ {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l n : ℕ} (B : BlockShape n)
    (h : IsCyclicAlgebra σ l) {δ : B.Levi E} {γ : B.Levi F},
    cyclicNorm σ l (B.leviEmbedding E δ) = baseChange F E n (B.leviEmbedding F γ) →
    letI : FiniteDimensional F E := h.1
    twistedRelativeParabolicDiscriminant B σ δ = relativeParabolicDiscriminant B F γ

/-- The relative twisted discriminant at an exact norm has no additional scalar factor. -/
theorem twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm :
    RelativeParabolicDiscriminantNormStatement.{u, v} := by
  intro F _ E _ _ σ l n B h δ γ hδγ
  let : FiniteDimensional F E := h.1
  let γE : B.Levi E := fun i => baseChange F E (B.size i) (γ i)
  have hγE : (fun i => cyclicNorm σ l (δ i)) = γE := by
    apply B.leviEmbedding_injective E
    rw [← cyclicNorm_leviEmbedding, ← baseChange_leviEmbedding]
    exact hδγ
  have hN : cyclicNorm σ l (relativeAdjointGL B E δ) = relativeAdjointGL B E γE := by
    rw [cyclicNorm_relativeAdjointGL, hγE]
  apply (algebraMap F E).injective
  rw [twistedRelativeDiscriminant_eq_coordinates, relativeDiscriminant_eq_matrix]
  let S := coordinateFieldAut σ (Fin (offBlockRank B))
  let a : Module.End F (Fin (offBlockRank B) → E) :=
    (Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ).val).restrictScalars F
  let b : Module.End F (Fin (offBlockRank B) → E) :=
    (Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ⁻¹).val).restrictScalars F
  have hab : b * a = 1 := by
    apply LinearMap.ext
    intro x
    change Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ⁻¹).val
      (Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ).val x) = x
    rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel,
      map_one, Units.val_one, map_one]
    rfl
  have hfac : S - b = (-b) * (1 - a * S) := by
    have hcomp : (-b) * (a * S) = -S := calc
      _ = -(b * (a * S)) := neg_mul b (a * S)
      _ = -S := by rw [← mul_assoc, hab, one_mul]
    rw [mul_sub, mul_one, hcomp]
    abel
  have hcoef : algebraMap F E (LinearMap.det (-b)) = (relativeAdjointGL B E γE⁻¹).val.det := by
    change algebraMap F E ((-(Matrix.toLinAlgEquiv' (relativeAdjointGL B E δ⁻¹).val)).restrictScalars F).det = _
    rw [LinearMap.det_restrictScalars, det_neg_toLin_relativeAdjointGL]
    have hm := h.determinant_cyclicNorm (relativeAdjointGL B E δ)
    rw [hN] at hm
    change _ = (GeneralLinear.determinant (relativeAdjointGL B E γE⁻¹) : E)
    simpa only [map_inv, Units.val_inv_eq_inv_val, Algebra.norm_inv, map_inv₀] using
      congrArg Inv.inv hm.symm
  have hdef : algebraMap F E (LinearMap.det (1 - a * S)) =
      (1 - (relativeAdjointGL B E γE).val).det := by
    rw [← hN]
    have he := h.det_cyclicSemilinearDefect (relativeAdjointGL B E δ).val
    rw [cyclicNorm]
    change _ = (1 - Units.coeHom _ ((List.range l).map fun i =>
      entrywiseAut (σ ^ i) (offBlockRank B) (relativeAdjointGL B E δ)).prod).det
    rw [map_list_prod, List.map_map]
    exact he
  change algebraMap F E (LinearMap.det (S - b)) = _
  rw [hfac, LinearMap.det.map_mul, map_mul, hcoef, hdef, ← Matrix.det_mul,
    Matrix.mul_sub, mul_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  rw [← neg_sub, Matrix.det_neg, Fintype.card_fin, (even_offBlockRank B).neg_one_pow, one_mul,
    (algebraMap F E).map_det]
  change (1 - (relativeAdjointGL B E γE⁻¹).val).det =
    ((1 - (relativeAdjointGL B F γ⁻¹).val).map (algebraMap F E)).det
  rw [Matrix.map_sub, Matrix.map_one] <;> try (solve | exact map_zero _ | exact map_one _ | exact map_sub _)
  have hbase : γE⁻¹ = fun i => baseChange F E (B.size i) (γ⁻¹ i) :=
    funext fun i => (map_inv _ _).symm
  rw [hbase]
  exact congrArg (fun M : Matrix (Fin (offBlockRank B)) (Fin (offBlockRank B)) E => (1 - M).det)
    (congrArg Units.val (relativeAdjointGL_baseChange (E := E) B γ⁻¹)).symm

end Extension

end Langlands.BaseChange
