import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicSplitCenterSubgroupHaar
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.GroupScheme.AffineWeilUnitGalois
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-!
# Automorphisms of an affine group over a number field acting on its adelic quotient

For an affine group scheme `G` over a number field `F` and an automorphism `e` of `G`
over `F`, the induced map on adelic points is a continuous automorphism of `G(𝔸_F)`.
It preserves the norm-one subgroup `G(𝔸_F)^1` and the principal subgroup `G(F)`.
If `e` has finite order, it preserves the Haar measure of `G(𝔸_F)^1` and the quotient
measure on `G(F) \ G(𝔸_F)^1`. These are the data `θ` of the simple twisted trace formula
(Getz–Hahn 2024, §18.5).

For a finite extension `L / K` and an affine group `H` over `K`, every `σ ∈ Aut(L/K)` gives an
automorphism `unitGaloisAut σ` of the Weil restriction `Res_{L/K} H_L`. The map
`σ ↦ unitGaloisAut σ` is a group homomorphism, so each of these automorphisms has finite order.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.TraceFormula.AdelicGroupAutomorphism

open Langlands.Global Langlands.Global.AdelicGroupPoints

section Generic

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The `k`-fold composite of a continuous multiplicative automorphism. -/
def iterateEquiv (φ : H ≃ₜ* H) : ℕ → (H ≃ₜ* H)
  | 0 => ContinuousMulEquiv.refl H
  | k + 1 => (iterateEquiv φ k).trans φ

theorem iterateEquiv_apply (φ : H ≃ₜ* H) (k : ℕ) (x : H) :
    iterateEquiv φ k x = φ^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change φ (iterateEquiv φ k x) = _
    rw [ih]

variable [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

theorem mulEquivHaarChar_iterateEquiv (φ : H ≃ₜ* H) (k : ℕ) :
    mulEquivHaarChar (iterateEquiv φ k) = mulEquivHaarChar φ ^ k := by
  induction k with
  | zero => exact mulEquivHaarChar_refl
  | succ k ih =>
    change mulEquivHaarChar ((iterateEquiv φ k).trans φ) = _
    rw [mulEquivHaarChar_trans, ih, pow_succ]

/-- A continuous automorphism with a positive iterate equal to the identity has Haar
character `1`. -/
theorem mulEquivHaarChar_eq_one_of_iterate (φ : H ≃ₜ* H) {m : ℕ} (hm : m ≠ 0)
    (hφ : ∀ x, φ^[m] x = x) : mulEquivHaarChar φ = 1 := by
  have h : iterateEquiv φ m = ContinuousMulEquiv.refl H := by
    ext x
    rw [iterateEquiv_apply, hφ]
    rfl
  have hpow : mulEquivHaarChar φ ^ m = 1 := by
    rw [← mulEquivHaarChar_iterateEquiv, h, mulEquivHaarChar_refl]
  exact (pow_eq_one_iff_of_nonneg zero_le hm).mp hpow

/-- Under the hypothesis of `mulEquivHaarChar_eq_one_of_iterate`, the automorphism preserves
every regular Haar measure. -/
theorem measurePreserving_of_iterate (φ : H ≃ₜ* H) {m : ℕ} (hm : m ≠ 0)
    (hφ : ∀ x, φ^[m] x = x) (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.Regular] :
    MeasurePreserving φ ρ ρ := by
  refine ⟨φ.continuous.measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map ρ φ
  rwa [mulEquivHaarChar_eq_one_of_iterate φ hm hφ, one_smul] at h

end Generic

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

theorem map_comp_apply {G₁ G₂ G₃ : GroupScheme (Spec (CommRingCat.of F))}
    (f : G₁ ⟶ G₂) (g : G₂ ⟶ G₃) (x : AdelicGroupPoints F G₁) :
    map F G₂ G₃ g (map F G₁ G₂ f x) = map F G₁ G₃ (f ≫ g) x := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
    Category.assoc]

theorem map_id_apply (x : AdelicGroupPoints F G) : map F G G (𝟙 G) x = x := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply]
  exact Category.comp_id x

/-- The continuous automorphism of `G(𝔸_F)` induced by an automorphism of `G` over `F`. -/
def adelicAut (e : Aut G) : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G where
  toFun := map F G G e.hom
  invFun := map F G G e.inv
  left_inv x := by rw [map_comp_apply, e.hom_inv_id, map_id_apply]
  right_inv x := by rw [map_comp_apply, e.inv_hom_id, map_id_apply]
  map_mul' := map_mul (map F G G e.hom)
  continuous_toFun := (map F G G e.hom).continuous
  continuous_invFun := (map F G G e.inv).continuous

@[simp] theorem adelicAut_apply (e : Aut G) (x : AdelicGroupPoints F G) :
    adelicAut F e x = map F G G e.hom x := rfl

@[simp] theorem adelicAut_symm_apply (e : Aut G) (x : AdelicGroupPoints F G) :
    (adelicAut F e).symm x = map F G G e.inv x := rfl

/-- In `Aut G`, `e * e'` applies `e'` first; so does the induced adelic map. -/
theorem adelicAut_mul_apply (e e' : Aut G) (x : AdelicGroupPoints F G) :
    adelicAut F (e * e') x = adelicAut F e (adelicAut F e' x) := by
  rw [adelicAut_apply, adelicAut_apply, adelicAut_apply, map_comp_apply, Aut.Aut_mul_def]
  rfl

theorem adelicAut_one_apply (x : AdelicGroupPoints F G) : adelicAut F 1 x = x :=
  map_id_apply F x

theorem adelicAut_pow_apply (e : Aut G) (k : ℕ) (x : AdelicGroupPoints F G) :
    adelicAut F (e ^ k) x = (adelicAut F e)^[k] x := by
  induction k with
  | zero => rw [pow_zero, adelicAut_one_apply]; rfl
  | succ k ih => rw [pow_succ', adelicAut_mul_apply, ih, Function.iterate_succ_apply']

theorem adelicAut_mem_normOneSubgroup_iff (e : Aut G) (x : AdelicGroupPoints F G) :
    adelicAut F e x ∈ normOneSubgroup F G ↔ x ∈ normOneSubgroup F G := by
  constructor
  · intro hx
    have h := map_normOneSubgroup_le F G G e.inv ⟨adelicAut F e x, hx, rfl⟩
    change (adelicAut F e).symm (adelicAut F e x) ∈ normOneSubgroup F G at h
    rwa [ContinuousMulEquiv.symm_apply_apply] at h
  · intro hx
    exact map_normOneSubgroup_le F G G e.hom ⟨x, hx, rfl⟩

theorem adelicAut_isOfFinOrder_iterate (e : Aut G) (he : IsOfFinOrder e) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x, (adelicAut F e)^[m] x = x := by
  obtain ⟨m, hm, hpow⟩ := he.exists_pow_eq_one
  refine ⟨m, hm.ne', fun x => ?_⟩
  rw [← adelicAut_pow_apply, hpow, adelicAut_one_apply]

/-- The restriction of `adelicAut F e` to the norm-one subgroup `G(𝔸_F)^1`. -/
def normOneAut (e : Aut G) : normOneSubgroup F G ≃ₜ* normOneSubgroup F G :=
  QuotientIntegration.subgroupAutomorphism (normOneSubgroup F G) (adelicAut F e)
    (adelicAut_mem_normOneSubgroup_iff F e)

@[simp] theorem normOneAut_val (e : Aut G) (x : normOneSubgroup F G) :
    (normOneAut F e x : AdelicGroupPoints F G) = map F G G e.hom x := rfl

@[simp] theorem normOneAut_symm_val (e : Aut G) (x : normOneSubgroup F G) :
    ((normOneAut F e).symm x : AdelicGroupPoints F G) = map F G G e.inv x := rfl

theorem normOneAut_eq_mapNormOne (e : Aut G) (x : normOneSubgroup F G) :
    normOneAut F e x = mapNormOne F G G e.hom x := rfl

theorem normOneAut_symm_eq_mapNormOne (e : Aut G) (x : normOneSubgroup F G) :
    (normOneAut F e).symm x = mapNormOne F G G e.inv x := rfl

theorem normOneAut_pow_apply (e : Aut G) (k : ℕ) (x : normOneSubgroup F G) :
    normOneAut F (e ^ k) x = (normOneAut F e)^[k] x := by
  induction k generalizing x with
  | zero => exact Subtype.ext (adelicAut_one_apply F (x : AdelicGroupPoints F G))
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact Subtype.ext (by
      rw [normOneAut_val, normOneAut_val, normOneAut_val, pow_succ', ← adelicAut_apply,
        adelicAut_mul_apply]
      rfl)

/-- The automorphism of `G(𝔸_F)^1` preserves the principal subgroup `G(F)`. -/
theorem normOneAut_mem_rationalNormOneSubgroup_iff (e : Aut G) (x : normOneSubgroup F G) :
    normOneAut F e x ∈ rationalNormOneSubgroup F G ↔ x ∈ rationalNormOneSubgroup F G := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨G.affinePointsTarget e.inv (CommAlgCat.of F F) y, ?_⟩
    rw [← mapNormOne_rationalNormOne, hy, ← normOneAut_symm_eq_mapNormOne,
      ContinuousMulEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨G.affinePointsTarget e.hom (CommAlgCat.of F F) y,
      (mapNormOne_rationalNormOne F G G e.hom y).symm⟩

/-- The homeomorphism of `G(F) \ G(𝔸_F)^1` induced by `e`: `G(F) x ↦ G(F) e(x)`. -/
def rationalQuotientAut (e : Aut G) :
    NormOneRationalQuotient F G ≃ₜ NormOneRationalQuotient F G :=
  QuotientIntegration.quotientAutomorphism (rationalNormOneSubgroup F G) (normOneAut F e)
    (normOneAut_mem_rationalNormOneSubgroup_iff F e)

section Measure

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A finite-order automorphism of `G` preserves the Haar measure of `G(𝔸_F)^1`. -/
theorem measurePreserving_normOneAut (e : Aut G) (he : IsOfFinOrder e) :
    MeasurePreserving (normOneAut F e) Measure.haar Measure.haar := by
  obtain ⟨m, hm, hpow⟩ := he.exists_pow_eq_one
  refine measurePreserving_of_iterate (normOneAut F e) hm.ne' (fun x => ?_) Measure.haar
  rw [← normOneAut_pow_apply, hpow]
  exact Subtype.ext (adelicAut_one_apply F (x : AdelicGroupPoints F G))

/-- A finite-order automorphism of `G` preserves the quotient Haar measure on
`G(F) \ G(𝔸_F)^1`. -/
theorem measurePreserving_rationalQuotientAut
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (e : Aut G) (he : IsOfFinOrder e) :
    MeasurePreserving (rationalQuotientAut F e) (normOneRationalQuotientHaarMeasure F G)
      (normOneRationalQuotientHaarMeasure F G) := by
  have := PositiveRealTorus.rationalNormOneSubgroup_count_isHaarMeasure F G
  have hΓ := (isDiscrete_rationalNormOneSubgroup F G)
  have hclosed := (rationalNormOneSubgroup F G).isClosed_of_isDiscrete hΓ
  have : LocallyCompactSpace (rationalNormOneSubgroup F G) := hclosed.locallyCompactSpace
  obtain ⟨m, hm, hpow⟩ := he.exists_pow_eq_one
  have hiter : ∀ x, (normOneAut F e)^[m] x = x := fun x => by
    rw [← normOneAut_pow_apply, hpow]
    exact Subtype.ext (adelicAut_one_apply F (x : AdelicGroupPoints F G))
  have hG : mulEquivHaarChar (normOneAut F e) = 1 :=
    mulEquivHaarChar_eq_one_of_iterate _ hm.ne' hiter
  have hH : mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism
      (rationalNormOneSubgroup F G) (normOneAut F e)
      (normOneAut_mem_rationalNormOneSubgroup_iff F e)) = 1 := by
    refine mulEquivHaarChar_eq_one_of_iterate _ hm.ne' (fun x => ?_)
    apply Subtype.ext
    have key : ∀ k : ℕ, ((QuotientIntegration.subgroupAutomorphism
        (rationalNormOneSubgroup F G) (normOneAut F e)
        (normOneAut_mem_rationalNormOneSubgroup_iff F e))^[k] x : normOneSubgroup F G) =
          (normOneAut F e)^[k] x := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          QuotientIntegration.subgroupAutomorphism_apply, ih]
    rw [key, hiter]
  refine ⟨(rationalQuotientAut F e).continuous.measurable, ?_⟩
  have h := (normOneRationalQuotientHaarMeasure_isCompatible F G).map_quotientAutomorphism
    (rationalNormOneSubgroup F G) hclosed (normOneAut F e)
    (normOneAut_mem_rationalNormOneSubgroup_iff F e)
  rw [hG, hH, div_one, ENNReal.coe_one, one_smul] at h
  exact h

/-- The inverse form used by the twist operator `I_θ φ = φ ∘ θ⁻¹`. -/
theorem measurePreserving_rationalQuotientAut_symm
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (e : Aut G) (he : IsOfFinOrder e) :
    MeasurePreserving (rationalQuotientAut F e).symm (normOneRationalQuotientHaarMeasure F G)
      (normOneRationalQuotientHaarMeasure F G) :=
  (measurePreserving_rationalQuotientAut F e he).symm
    (rationalQuotientAut F e).toMeasurableEquiv

end Measure

section Weil

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The Weil restriction `Res_{L/K} H_L` of the base change of `H` to `L`. -/
abbrev weilGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  AffineWeil.groupScheme K L (AffineWeil.unitBaseChange K L H)

omit [FiniteDimensional K L] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem unitGaloisPointHom_apply (σ : L ≃ₐ[K] L) (A : CommAlgCat.{u} (CommRingCat.of K))
    (q : (AffineWeil.pointFunctor K L (AffineWeil.unitBaseChange K L H)).obj A) :
    AffineWeil.unitGaloisPointHom K L H σ A q =
      affinePointsBaseChangeMulEquiv K L (L ⊗[K] A) H
        (TensorGaloisPoint.conjugate K L A H σ
          ((affinePointsBaseChangeMulEquiv K L (L ⊗[K] A) H).symm q)) := rfl

omit [FiniteDimensional K L] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem unitGaloisTransformation_mul (σ τ : L ≃ₐ[K] L) :
    AffineWeil.unitGaloisTransformation K L H τ ≫ AffineWeil.unitGaloisTransformation K L H σ =
      AffineWeil.unitGaloisTransformation K L H (σ * τ) := by
  ext A q
  change AffineWeil.unitGaloisPointHom K L H σ A (AffineWeil.unitGaloisPointHom K L H τ A q) =
    AffineWeil.unitGaloisPointHom K L H (σ * τ) A q
  rw [unitGaloisPointHom_apply, unitGaloisPointHom_apply, unitGaloisPointHom_apply,
    MulEquiv.symm_apply_apply, TensorGaloisPoint.conjugate_mul]

omit [FiniteDimensional K L] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem unitGaloisTransformation_one :
    AffineWeil.unitGaloisTransformation K L H 1 = 𝟙 _ := by
  ext A q
  change AffineWeil.unitGaloisPointHom K L H 1 A q = q
  rw [unitGaloisPointHom_apply, TensorGaloisPoint.conjugate_one, MulEquiv.apply_symm_apply]

/-- In diagram order: `σ * τ` acts by first `τ`, then `σ`. -/
theorem unitGaloisAction_mul (σ τ : L ≃ₐ[K] L) :
    AffineWeil.unitGaloisAction K L H (σ * τ) =
      AffineWeil.unitGaloisAction K L H τ ≫ AffineWeil.unitGaloisAction K L H σ := by
  rw [AffineWeil.unitGaloisAction, AffineWeil.unitGaloisAction, AffineWeil.unitGaloisAction,
    Corepresented.groupSchemeMap_comp, unitGaloisTransformation_mul]

theorem unitGaloisAction_one : AffineWeil.unitGaloisAction K L H 1 = 𝟙 _ := by
  apply Corepresented.hom_ext_affinePoints
  intro S f
  rw [AffineWeil.unitGaloisAction, Corepresented.groupSchemeMap_affinePoints,
    unitGaloisTransformation_one]
  simp

/-- The Galois automorphism of `Res_{L/K} H_L` attached to `σ ∈ Aut(L/K)`. -/
def unitGaloisAut (σ : L ≃ₐ[K] L) : Aut (weilGroup K L H) where
  hom := AffineWeil.unitGaloisAction K L H σ
  inv := AffineWeil.unitGaloisAction K L H σ⁻¹
  hom_inv_id := by rw [← unitGaloisAction_mul, inv_mul_cancel, unitGaloisAction_one]
  inv_hom_id := by rw [← unitGaloisAction_mul, mul_inv_cancel, unitGaloisAction_one]

@[simp] theorem unitGaloisAut_hom (σ : L ≃ₐ[K] L) :
    (unitGaloisAut K L H σ).hom = AffineWeil.unitGaloisAction K L H σ := rfl

/-- `σ ↦ unitGaloisAut σ` is a group homomorphism `Aut(L/K) →* Aut(Res_{L/K} H_L)`. -/
def unitGaloisAutHom : (L ≃ₐ[K] L) →* Aut (weilGroup K L H) where
  toFun := unitGaloisAut K L H
  map_one' := Iso.ext (unitGaloisAction_one K L H)
  map_mul' σ τ := Iso.ext (by
    rw [Aut.Aut_mul_def]
    exact unitGaloisAction_mul K L H σ τ)

@[simp] theorem unitGaloisAutHom_apply (σ : L ≃ₐ[K] L) :
    unitGaloisAutHom K L H σ = unitGaloisAut K L H σ := rfl

theorem isOfFinOrder_unitGaloisAut (σ : L ≃ₐ[K] L) : IsOfFinOrder (unitGaloisAut K L H σ) :=
  (unitGaloisAutHom K L H).isOfFinOrder (isOfFinOrder_of_finite σ)

end Weil

section WeilTwist

variable (K L : Type u) [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The Galois twist `θ_σ` of `Res_{L/K} H_L(𝔸_K)^1` preserves its Haar measure. -/
theorem measurePreserving_normOneAut_unitGaloisAut (σ : L ≃ₐ[K] L) :
    MeasurePreserving (normOneAut K (unitGaloisAut K L H σ)) Measure.haar Measure.haar :=
  measurePreserving_normOneAut K _ (isOfFinOrder_unitGaloisAut K L H σ)

/-- The inverse of the induced map on `Res_{L/K} H_L(K) \ Res_{L/K} H_L(𝔸_K)^1` preserves the
quotient Haar measure. -/
theorem measurePreserving_rationalQuotientAut_unitGaloisAut_symm
    [(Measure.haar : Measure (normOneSubgroup K (weilGroup K L H))).IsMulRightInvariant]
    (σ : L ≃ₐ[K] L) :
    MeasurePreserving (rationalQuotientAut K (unitGaloisAut K L H σ)).symm
      (normOneRationalQuotientHaarMeasure K (weilGroup K L H))
      (normOneRationalQuotientHaarMeasure K (weilGroup K L H)) :=
  measurePreserving_rationalQuotientAut_symm K _ (isOfFinOrder_unitGaloisAut K L H σ)

end WeilTwist

end Langlands.TraceFormula.AdelicGroupAutomorphism
