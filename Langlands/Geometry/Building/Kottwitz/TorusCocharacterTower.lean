import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.GroupScheme.Torus.PointsTensorGalois
import Langlands.GroupScheme.GaloisPointTower
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Geometry.Building.Kottwitz.TorusNormCohomology

/-! # Cocharacter evaluations in a tower of coefficient fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPoint
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

section Tower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]

/-- The field inclusion, as a map from the test scheme with extended structure. -/
def extendTestArrow :
    (Over.map (baseMap L M)).obj (Over.mk (𝟙 (Spec (CommRingCat.of M)))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
  Over.homMk (baseMap L M) (by simp)

/-- Pullback of a unit point along `Spec M ⟶ Spec L` is the image unit. -/
theorem unitPoint_extend (x : Additive Lˣ) :
    (Gm.pointsEquiv _ ((Over.map (baseMap L M)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of M)))))).symm
      (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of M))))
        (unitsPointEquiv M
          (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x.toMul))).toMul) =
      extendTestArrow L M ≫ (unitsPointEquiv L x).toMul := by
  apply (Gm.pointsEquiv _ _).injective
  rw [MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  apply (Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of M)).commRingCatIsoToRingEquiv.toMulEquiv).injective
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of M)).hom
      (Gm.pointsEquiv _ _ (unitsPointEquiv M
        (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x.toMul))).toMul).val =
    (((Spec.map (CommRingCat.ofHom (algebraMap L M))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of M)).hom)
        (Gm.pointsEquiv _ _ (unitsPointEquiv L x).toMul).val)
  rw [Scheme.ΓSpecIso_naturality]
  change (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of M)))
      (unitsPointEquiv M
        (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x.toMul))).toMul : M) =
    algebraMap L M (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))
      (unitsPointEquiv L x).toMul : L)
  simp [unitsPointEquiv]

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Extending coefficients of a pure cocharacter evaluation extends unit and cocharacter. -/
theorem relativeExtend_coefficientEvaluation_tmul (x : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    relativeExtend k L M T.toGrp (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)).toMul =
      (coefficientEvaluation k M T
        (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x.toMul) ⊗ₜ[ULift.{u} ℤ]
          extendGeometricCocharacters k L M T ν)).toMul := by
  apply Over.OverMorphism.ext
  rw [coefficientEvaluation_tmul_left]
  have h := congrArg (fun f => f.left)
    (cocharacterLattice.baseChange_points (baseMap L M) (baseChanged k L T) ν
      (Over.mk (𝟙 (Spec (CommRingCat.of M))))
      (unitsPointEquiv M
        (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x.toMul))).toMul)
  rw [unitPoint_extend] at h
  simp only [baseChangePointsEquiv_left, Over.comp_left] at h
  change baseMap L M ≫ (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)).toMul.left = _
  rw [coefficientEvaluation_tmul_left]
  change _ = (unitsPointEquiv M _).toMul.left ≫
    ((CommGroupScheme.groupHom (cocharacterLattice.baseChange (baseMap L M)
      (baseChanged k L T) ν)).hom.hom.left ≫
      (towerBaseChangeIso k L M T.toGrp).hom.hom.hom.left) ≫
        pullback.fst T.X.hom (baseMap k M)
  rw [Category.assoc, towerBaseChangeIso_hom_fst]
  simp only [← Category.assoc] at h ⊢
  exact (congrArg (fun f => f ≫ pullback.fst T.X.hom (baseMap k L)) h).symm

/-- Extension intertwines two compatible coefficient automorphisms. -/
theorem relativeExtend_conjugate (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    (σ : L ≃ₐ[k] L) (τ : M ≃ₐ[k] M)
    (h : ∀ a : L, τ (algebraMap L M a) = algebraMap L M (σ a))
    (x : G.affinePoints (CommAlgCat.of k L)) :
    relativeExtend k L M G (conjugate k L G σ x) =
      conjugate k M G τ (relativeExtend k L M G x) := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeExtend, coordinates_conjugate]
  exact (h _).symm

end Tower

section Evaluation

variable {K : Type u} [Field K] (A : CommGroupScheme (Spec (CommRingCat.of K)))

/-- A cocharacter of a split torus is determined by its value at one unit of infinite order. -/
theorem cocharacterPoints_injective (hA : IsSplitTorus A.toGrp) {b : Kˣ} (hb : ¬IsOfFinOrder b)
    {c c' : cocharacterLattice A}
    (h : CocharacterUniformizer.cocharacterPoints K A c b =
      CocharacterUniformizer.cocharacterPoints K A c' b) : c = c' := by
  apply (cocharacterDualEquiv A hA).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply]
  have hχ := congrArg
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm χ)) h
  rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    CocharacterUniformizer.rationalCharacterEval_cocharacterPoints] at hχ
  exact (injective_zpow_iff_not_isOfFinOrder.2 hb) hχ

/-- The split valuation of a cocharacter evaluated at a unit is the order times the cocharacter. -/
theorem splitValuation_cocharacterPoints (hA : IsSplitTorus A.toGrp)
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (ν : cocharacterLattice A) (b : Kˣ) :
    splitValuation A hA v (CocharacterUniformizer.cocharacterPoints K A ν b) =
      Multiplicative.ofAdd ((IntegerValuation.orderUnits v b).toAdd • ν) := by
  apply Multiplicative.toAdd.injective
  apply (cocharacterDualEquiv A hA).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply, toAdd_ofAdd,
    splitValuation_pairing, CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    map_zpow, toAdd_zpow, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm]

end Evaluation

section PureTensor

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- A pure coefficient evaluation is the cocharacter evaluated at the unit. -/
theorem coefficientEvaluation_tmul_eq (x : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)).toMul =
      GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp
        (CocharacterUniformizer.cocharacterPoints L (baseChanged k L T) ν x.toMul) := rfl

/-- Pure tensor evaluations at a unit of infinite order detect cocharacters. -/
theorem coefficientEvaluation_tmul_injective (hL : IsSplitTorus (baseChanged k L T).toGrp)
    {x : Additive Lˣ} (hx : ¬IsOfFinOrder x.toMul) {c c' : cocharacterLattice (baseChanged k L T)}
    (h : coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] c) =
      coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] c')) : c = c' := by
  apply cocharacterPoints_injective (baseChanged k L T) hL hx
  apply (GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp).injective
  rw [← coefficientEvaluation_tmul_eq, ← coefficientEvaluation_tmul_eq, h]

/-- Two additive maps out of coefficient points of a split torus agree if they agree on
pure tensor evaluations. -/
theorem additive_ext_coefficientEvaluation (hL : IsSplitTorus (baseChanged k L T).toGrp)
    {X : Type*} [AddCommGroup X]
    {φ φ' : Additive (affinePoints T.toGrp (CommAlgCat.of k L)) →+ X}
    (h : ∀ x ν, φ (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)) =
      φ' (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν))) : φ = φ' := by
  apply AddMonoidHom.ext
  intro y
  obtain ⟨t, rfl⟩ := (coefficientPointEquiv k L T hL).surjective y
  induction t using TensorProduct.inductionOn with
  | tmul x ν => exact h x ν
  | add a b ha hb => simp only [map_add, ha, hb]

end PureTensor

section Compatibility

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- Extending cocharacters intertwines compatible coefficient automorphisms. -/
theorem extendGeometricCocharacters_galois (hM : IsSplitTorus (baseChanged k M T).toGrp)
    {u₀ : Lˣ} (hu₀ : ¬IsOfFinOrder u₀) (σ : L ≃ₐ[k] L) (τ : M ≃ₐ[k] M)
    (h : ∀ a : L, τ (algebraMap L M a) = algebraMap L M (σ a))
    (ν : cocharacterLattice (baseChanged k L T)) :
    extendGeometricCocharacters k L M T (cocharacterLattice.galoisRepresentation k L T σ ν) =
      cocharacterLattice.galoisRepresentation k M T τ (extendGeometricCocharacters k L M T ν) := by
  have hw : ¬IsOfFinOrder (Additive.toMul (Additive.ofMul
      (Units.map (algebraMap L M).toMonoidHom (Units.map σ.toMonoidHom u₀)))) := by
    rw [toMul_ofMul, (Units.map_injective (algebraMap L M).injective).isOfFinOrder_iff,
      (Units.map_injective σ.injective).isOfFinOrder_iff]
    exact hu₀
  have hu : Units.map τ.toMonoidHom (Units.map (algebraMap L M).toMonoidHom u₀) =
      Units.map (algebraMap L M).toMonoidHom (Units.map σ.toMonoidHom u₀) :=
    Units.ext (h (u₀ : L))
  have h1 := relativeExtend_coefficientEvaluation_tmul k L M T
    (Additive.ofMul (Units.map σ.toMonoidHom u₀)) (cocharacterLattice.galoisRepresentation k L T σ ν)
  have h2 := coefficientEvaluation_galois_tmul k L T σ (Additive.ofMul u₀) ν
  have h3 := coefficientEvaluation_galois_tmul k M T τ
    (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom u₀)) (extendGeometricCocharacters k L M T ν)
  have h4 := relativeExtend_coefficientEvaluation_tmul k L M T (Additive.ofMul u₀) ν
  simp only [toMul_ofMul] at h1 h2 h3 h4
  apply coefficientEvaluation_tmul_injective k M T hM hw
  apply Additive.toMul.injective
  rw [← h1, h2, toMul_ofMul, relativeExtend_conjugate k L M T.toGrp σ τ h, h4]
  exact (congrArg Additive.toMul h3).symm.trans (by rw [hu])

/-- Automorphisms over the intermediate field fix extended cocharacters. -/
theorem extendGeometricCocharacters_relative (hM : IsSplitTorus (baseChanged k M T).toGrp)
    {u₀ : Lˣ} (hu₀ : ¬IsOfFinOrder u₀) (σ : M ≃ₐ[L] M)
    (ν : cocharacterLattice (baseChanged k L T)) :
    cocharacterLattice.galoisRepresentation k M T (σ.restrictScalars k)
      (extendGeometricCocharacters k L M T ν) = extendGeometricCocharacters k L M T ν := by
  have h := extendGeometricCocharacters_galois k L M T hM hu₀ 1 (σ.restrictScalars k)
    (fun a => by simp) ν
  rw [show cocharacterLattice.galoisRepresentation k L T 1 ν = ν from
    LinearMap.congr_fun (map_one (cocharacterLattice.galoisRepresentation k L T)) ν] at h
  exact h.symm

end Compatibility

section Norm

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [FiniteDimensional L M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The relative norm of a pure evaluation of an extended cocharacter is the evaluation at the
field norm. -/
theorem relativeNorm_coefficientEvaluation_tmul (hM : IsSplitTorus (baseChanged k M T).toGrp)
    {u₀ : Lˣ} (hu₀ : ¬IsOfFinOrder u₀) (x : Additive Mˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    relativeNorm k L M T (coefficientEvaluation k M T
        (x ⊗ₜ[ULift.{u} ℤ] extendGeometricCocharacters k L M T ν)).toMul =
      (coefficientEvaluation k L T
        (Additive.ofMul (Units.map (Algebra.norm L : M →* L) x.toMul) ⊗ₜ[ULift.{u} ℤ] ν)).toMul := by
  apply relativeExtend_injective k L M T.toGrp
  rw [relativeExtend_norm, relativeExtend_coefficientEvaluation_tmul, toMul_ofMul]
  have hσ : ∀ σ : M ≃ₐ[L] M, relativeConjugate k L M T.toGrp σ
      (coefficientEvaluation k M T
        (x ⊗ₜ[ULift.{u} ℤ] extendGeometricCocharacters k L M T ν)).toMul =
      (coefficientEvaluation k M T (Additive.ofMul (Units.map σ.toMonoidHom x.toMul) ⊗ₜ[ULift.{u} ℤ]
        extendGeometricCocharacters k L M T ν)).toMul := by
    intro σ
    have h := coefficientEvaluation_galois_tmul k M T (σ.restrictScalars k) x
      (extendGeometricCocharacters k L M T ν)
    rw [extendGeometricCocharacters_relative k L M T hM hu₀ σ ν] at h
    exact (congrArg Additive.toMul h).symm
  have hsum : (∑ σ : M ≃ₐ[L] M, Additive.ofMul (Units.map σ.toMonoidHom x.toMul)) =
      Additive.ofMul (Units.map (algebraMap L M).toMonoidHom
        (Units.map (Algebra.norm L : M →* L) x.toMul)) := by
    rw [← ofMul_prod]
    congr 1
    apply Units.ext
    rw [Units.coe_prod]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [Algebra.norm_eq_prod_automorphisms]
    rfl
  rw [Finset.prod_congr rfl fun σ _ => hσ σ, ← toMul_sum, ← map_sum, ← TensorProduct.sum_tmul,
    hsum]

end Norm

section TowerComposition

variable (k L M E : Type u) [Field k] [Field L] [Field M] [Field E]
  [Algebra k L] [Algebra k M] [Algebra k E] [Algebra L M] [Algebra L E] [Algebra M E]
  [IsScalarTower k L M] [IsScalarTower k L E] [IsScalarTower k M E] [IsScalarTower L M E]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- Extending cocharacters is transitive in a tower of coefficient fields. -/
theorem extendGeometricCocharacters_extend (hE : IsSplitTorus (baseChanged k E T).toGrp)
    {u₀ : Lˣ} (hu₀ : ¬IsOfFinOrder u₀) (ν : cocharacterLattice (baseChanged k L T)) :
    extendGeometricCocharacters k M E T (extendGeometricCocharacters k L M T ν) =
      extendGeometricCocharacters k L E T ν := by
  have hw : ¬IsOfFinOrder (Additive.toMul (Additive.ofMul
      (Units.map (algebraMap L E).toMonoidHom u₀))) := by
    rw [toMul_ofMul, (Units.map_injective (algebraMap L E).injective).isOfFinOrder_iff]
    exact hu₀
  have h1 := relativeExtend_coefficientEvaluation_tmul k L E T (Additive.ofMul u₀) ν
  have h2 := relativeExtend_coefficientEvaluation_tmul k L M T (Additive.ofMul u₀) ν
  have h3 := relativeExtend_coefficientEvaluation_tmul k M E T
    (Additive.ofMul (Units.map (algebraMap L M).toMonoidHom u₀))
    (extendGeometricCocharacters k L M T ν)
  have h4 := relativeExtend_relativeExtend k L M E T.toGrp
    (coefficientEvaluation k L T (Additive.ofMul u₀ ⊗ₜ[ULift.{u} ℤ] ν)).toMul
  simp only [toMul_ofMul] at h1 h2 h3
  have hu : Units.map (algebraMap M E).toMonoidHom (Units.map (algebraMap L M).toMonoidHom u₀) =
      Units.map (algebraMap L E).toMonoidHom u₀ :=
    Units.ext (IsScalarTower.algebraMap_apply L M E (u₀ : L)).symm
  rw [hu] at h3
  apply coefficientEvaluation_tmul_injective k E T hE hw
  apply Additive.toMul.injective
  rw [← h3, ← h2, h4, h1]

end TowerComposition

section Bijective

variable (k L E : Type u) [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Extending cocharacters of a torus that is already split over `L` is bijective. -/
theorem extendGeometricCocharacters_bijective (hL : IsSplitTorus (baseChanged k L T).toGrp) :
    Function.Bijective (extendGeometricCocharacters k L E T) := by
  rw [extendGeometricCocharacters, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom]
  exact (AddEquiv.bijective _).comp (hL.cocharacterLattice_baseChange_bijective (baseMap L E) _)

end Bijective

end Langlands.Geometry.Building.Kottwitz
