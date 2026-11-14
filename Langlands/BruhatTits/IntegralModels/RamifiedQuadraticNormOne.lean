import Langlands.BruhatTits.IntegralModels.NormOneTraceSmoothness
import Langlands.CommutativeAlgebra.FiniteSeparableLiftedPolynomialModel
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Mathlib.FieldTheory.KummerPolynomial

set_option backward.isDefEq.respectTransparency false

/-! # Regression: the ramified quadratic norm-one torus -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Algebra

section SquareRoot

variable {R : Type*} [CommRing R] [Nontrivial R] (d : R)

/-- The basis `1, α` of `R[X] / (X ^ 2 - d)`, where `α` is the class of `X`. -/
def sqrtBasis : Module.Basis (Fin 2) R (AdjoinRoot (X ^ 2 - C d)) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C d two_ne_zero)).basis.reindex
    (finCongr natDegree_X_pow_sub_C)

theorem sqrtBasis_apply (i : Fin 2) :
    sqrtBasis d i = AdjoinRoot.root (X ^ 2 - C d) ^ (i : ℕ) := by
  rw [sqrtBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem sqrtBasis_zero : sqrtBasis d 0 = 1 := by
  rw [sqrtBasis_apply]
  rfl

theorem sqrtBasis_one : sqrtBasis d 1 = AdjoinRoot.root (X ^ 2 - C d) := by
  rw [sqrtBasis_apply]
  exact pow_one _

omit [Nontrivial R] in
theorem root_sq : AdjoinRoot.root (X ^ 2 - C d) ^ 2 = AdjoinRoot.of (X ^ 2 - C d) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

end SquareRoot

section QuadraticBasis

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (d : R)
  (β : Module.Basis (Fin 2) R S) (r : S)

/-- If `1, r` is a basis of `S` over `R`, every element of `S` is `a + b r`. -/
theorem exists_eq_algebraMap_add_mul (h0 : β 0 = 1) (h1 : β 1 = r) (y : S) :
    ∃ a b : R, y = algebraMap R S a + algebraMap R S b * r := by
  refine ⟨β.repr y 0, β.repr y 1, ?_⟩
  conv_lhs => rw [← β.sum_repr y]
  rw [Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]

/-- If `1, r` is a basis of `S` over `R` with `r ^ 2 = d`, the norm of `a + b r`
is `a ^ 2 - d b ^ 2`. -/
theorem norm_algebraMap_add_mul (h0 : β 0 = 1) (h1 : β 1 = r) (hr : r ^ 2 = algebraMap R S d)
    (a b : R) :
    Algebra.norm R (algebraMap R S a + algebraMap R S b * r) = a ^ 2 - d * b ^ 2 := by
  classical
  set x := algebraMap R S a + algebraMap R S b * r with hx
  have hx0 : x * β 0 = a • β 0 + b • β 1 := by
    rw [h0, h1, mul_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hx1 : x * β 1 = (d * b) • β 0 + a • β 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul, hx]
    linear_combination (algebraMap R S b) * hr
  rw [Algebra.norm_eq_matrix_det β, Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hx0, hx1]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_smul,
    Pi.add_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp
  ring

end QuadraticBasis

section SquareRootNorm

variable {R : Type*} [CommRing R] [Nontrivial R] (d : R)

/-- The norm of `a + b α` in `R[X] / (X ^ 2 - d)` is `a ^ 2 - d b ^ 2`. -/
theorem norm_of_add_of_mul_root (a b : R) :
    Algebra.norm R (AdjoinRoot.of (X ^ 2 - C d) a +
      AdjoinRoot.of (X ^ 2 - C d) b * AdjoinRoot.root (X ^ 2 - C d)) = a ^ 2 - d * b ^ 2 := by
  rw [← AdjoinRoot.algebraMap_eq]
  exact norm_algebraMap_add_mul d (sqrtBasis d) _ (sqrtBasis_zero d) (sqrtBasis_one d)
    (by rw [root_sq, AdjoinRoot.algebraMap_eq]) a b

end SquareRootNorm

end Langlands.Algebra

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme WeilGm Langlands.CommutativeAlgebra
open scoped ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F]

/-- Data for a ramified quadratic extension in odd residue characteristic: an
irreducible element `ϖ` of `𝒪[F]` (a uniformizer), with `2` a unit in `𝒪[F]`. -/
structure RamifiedQuadraticData where
  uniformizer : 𝒪[F]
  irreducible : Irreducible uniformizer
  isUnit_two : IsUnit (2 : 𝒪[F])

namespace RamifiedQuadraticData

variable {F} (D : RamifiedQuadraticData F)

/-- The integral polynomial `X ^ 2 - ϖ`. -/
abbrev polynomial : 𝒪[F][X] := X ^ 2 - C D.uniformizer

/-- The finite free `𝒪[F]`-algebra `𝒪[F][X] / (X ^ 2 - ϖ)`. -/
abbrev Carrier : Type u := AdjoinRoot D.polynomial

instance : Module.Finite 𝒪[F] D.Carrier :=
  (monic_X_pow_sub_C D.uniformizer two_ne_zero).finite_adjoinRoot

instance : Module.Free 𝒪[F] D.Carrier :=
  (monic_X_pow_sub_C D.uniformizer two_ne_zero).free_adjoinRoot

theorem finrank_carrier : Module.finrank 𝒪[F] D.Carrier = 2 := by
  rw [Module.finrank_eq_card_basis (Langlands.Algebra.sqrtBasis D.uniformizer), Fintype.card_fin]

/-- `1 / 2` has trace one in `B = 𝒪[F][X] / (X ^ 2 - ϖ)`. -/
theorem hasTraceOne : Langlands.Algebra.HasTraceOne 𝒪[F] D.Carrier :=
  Langlands.Algebra.hasTraceOne_of_isUnit_finrank (by
    rw [finrank_carrier, Nat.cast_ofNat]
    exact D.isUnit_two)

/-- `ϖ` is not a square in `F`. -/
theorem not_isSquare (y : F) : y ^ 2 ≠ (D.uniformizer : F) := by
  intro hy
  have hint : IsIntegral 𝒪[F] y := by
    refine ⟨X ^ 2 - C D.uniformizer, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy, sub_eq_zero]
    rfl
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hz : z * z = D.uniformizer := by
    apply Subtype.val_injective
    change (algebraMap 𝒪[F] F z) * (algebraMap 𝒪[F] F z) = (D.uniformizer : F)
    rw [← pow_two, hy]
  rcases D.irreducible.isUnit_or_isUnit hz.symm with h | h
  · exact D.irreducible.not_isUnit (hz ▸ h.mul h)
  · exact D.irreducible.not_isUnit (hz ▸ h.mul h)

/-- The generic polynomial `X ^ 2 - ϖ` over `F`. -/
theorem polynomial_map_generic :
    D.polynomial.map (algebraMap 𝒪[F] F) = X ^ 2 - C (D.uniformizer : F) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  rfl

theorem irreducible_generic : Irreducible (D.polynomial.map (algebraMap 𝒪[F] F)) := by
  rw [polynomial_map_generic]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two D.not_isSquare

instance : Fact (Irreducible (D.polynomial.map (algebraMap 𝒪[F] F))) := ⟨D.irreducible_generic⟩

/-- The ramified quadratic extension `E = F[X] / (X ^ 2 - ϖ)`. -/
abbrev GenericField : Type u := AdjoinRoot (D.polynomial.map (algebraMap 𝒪[F] F))

instance : FiniteDimensional F D.GenericField :=
  ((monic_X_pow_sub_C D.uniformizer two_ne_zero).map _).finite_adjoinRoot

include D in
theorem two_ne_zero_generic : (2 : F) ≠ 0 := by
  have h := D.isUnit_two.map (algebraMap 𝒪[F] F)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem uniformizer_ne_zero_generic : (D.uniformizer : F) ≠ 0 := by
  intro h
  apply D.irreducible.ne_zero
  exact Subtype.ext h

instance : Algebra.IsSeparable F D.GenericField := by
  have hsep : IsSeparable F (AdjoinRoot.root (D.polynomial.map (algebraMap 𝒪[F] F))) := by
    rw [IsSeparable, AdjoinRoot.minpoly_root D.irreducible_generic.ne_zero,
      ((monic_X_pow_sub_C D.uniformizer two_ne_zero).map _).leadingCoeff, inv_one, C_1, mul_one,
      polynomial_map_generic]
    exact separable_X_pow_sub_C _ (by exact_mod_cast D.two_ne_zero_generic)
      D.uniformizer_ne_zero_generic
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F _).2 hsep
  rw [IntermediateField.adjoin_root_eq_top] at this
  exact (IntermediateField.isSeparable_top F _).1 this

/-- The generic fibre of `B` is the ramified quadratic extension. -/
abbrev genericEquiv : F ⊗[𝒪[F]] D.Carrier ≃ₐ[F] D.GenericField :=
  adjoinRootBaseChangeEquiv 𝒪[F] F D.polynomial

/-- The generic torus `R¹_{E/F} G_m` is anisotropic. -/
theorem isAnisotropic : IsAnisotropic (normOne (CommRingCat.of F) D.GenericField) :=
  normOne_isAnisotropic F _

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The norm-one kernel of `B` is smooth, by the trace criterion. -/
theorem smooth : Smooth (normOne (CommRingCat.of 𝒪[F]) D.Carrier).X.hom :=
  normOne_smooth_of_hasTraceOne (CommRingCat.of 𝒪[F]) D.Carrier D.hasTraceOne

/-- The norm-one model `R¹_{B/𝒪[F]} G_m` of the norm-one torus `R¹_{E/F} G_m`. -/
abbrev model : LocalFieldIntegralModel F (normOne (CommRingCat.of F) D.GenericField) :=
  normOneModel F D.Carrier D.GenericField D.genericEquiv D.smooth

theorem model_isSmooth : D.model.IsSmooth := D.smooth

/-! ### The special fibre: `{±1} × 𝓀` -/

/-- `ϖ` reduces to zero in the residue field. -/
theorem residue_uniformizer : IsLocalRing.residue 𝒪[F] D.uniformizer = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2
    ((IsLocalRing.mem_maximalIdeal _).2 D.irreducible.not_isUnit)

include D in
/-- `2 ≠ 0` in the residue field. -/
theorem two_ne_zero_residue : (2 : 𝓀[F]) ≠ 0 := by
  have h := D.isUnit_two.map (IsLocalRing.residue 𝒪[F])
  rw [map_ofNat] at h
  exact h.ne_zero

/-- The `𝒪[F]`-algebra map `B → 𝓀[F]` sending `α` to `0`. -/
def residueRootZero : D.Carrier →ₐ[𝒪[F]] 𝓀[F] :=
  AdjoinRoot.liftAlgHom D.polynomial (Algebra.ofId 𝒪[F] 𝓀[F]) 0 (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C]
    change 0 ^ 2 - IsLocalRing.residue 𝒪[F] D.uniformizer = 0
    rw [D.residue_uniformizer]
    ring)

/-- The evaluation `𝓀[F] ⊗ B = 𝓀[F][α] / (α ^ 2) → 𝓀[F]` at `α = 0`. -/
def specialFibreEval : 𝓀[F] ⊗[CommRingCat.of 𝒪[F]] D.Carrier →ₐ[𝓀[F]] 𝓀[F] :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝓀[F] 𝓀[F]) D.residueRootZero
    (fun _ _ => Commute.all _ _)

/-- The norm of `z ∈ 𝓀[F][α] / (α ^ 2)` is the square of `z(0)`. -/
theorem norm_eq_specialFibreEval_sq (z : 𝓀[F] ⊗[CommRingCat.of 𝒪[F]] D.Carrier) :
    Algebra.norm 𝓀[F] z = D.specialFibreEval z ^ 2 := by
  let β := (Langlands.Algebra.sqrtBasis D.uniformizer).baseChange 𝓀[F]
  let r : 𝓀[F] ⊗[CommRingCat.of 𝒪[F]] D.Carrier := 1 ⊗ₜ AdjoinRoot.root D.polynomial
  have h0 : β 0 = 1 := by
    rw [Module.Basis.baseChange_apply, Langlands.Algebra.sqrtBasis_zero]
    rfl
  have h1 : β 1 = r := by
    rw [Module.Basis.baseChange_apply, Langlands.Algebra.sqrtBasis_one]
  have hr : r ^ 2 = algebraMap 𝓀[F] _ (algebraMap 𝒪[F] 𝓀[F] D.uniformizer) := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.tmul_pow, one_pow, Langlands.Algebra.root_sq,
      AdjoinRoot.algebraMap_eq]
  have hr0 : D.specialFibreEval r = 0 := by
    change Algebra.ofId 𝓀[F] 𝓀[F] 1 * D.residueRootZero (AdjoinRoot.root D.polynomial) = 0
    rw [residueRootZero, AdjoinRoot.liftAlgHom_root, mul_zero]
  obtain ⟨a, b, rfl⟩ := Langlands.Algebra.exists_eq_algebraMap_add_mul β r h0 h1 z
  rw [Langlands.Algebra.norm_algebraMap_add_mul _ β r h0 h1 hr, map_add, map_mul,
    AlgHom.commutes, AlgHom.commutes, hr0, IsLocalRing.ResidueField.algebraMap_eq,
    D.residue_uniformizer]
  simp

/-- The special-fibre points are the norm-one units of `B ⊗ 𝓀[F]`. -/
def specialFibrePointsEquiv :
    rationalPoints D.model.specialFibre ≃*
      (Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]).ker :=
  ((GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      (normOne (CommRingCat.of 𝒪[F]) D.Carrier) (Over.mk (𝟙 _))).trans
    (normOnePointsEquiv (CommRingCat.of 𝒪[F]) D.Carrier _)).trans
    (normOneCoeffEquiv (CommRingCat.of 𝒪[F]) D.Carrier (residueSectionsEquiv F))

/-- The unit map `(B ⊗ 𝓀[F])ˣ → 𝓀[F]ˣ`, `x + y α ↦ x`. -/
def unitsEval :
    (D.Carrier ⊗[CommRingCat.of 𝒪[F]] 𝓀[F])ˣ →* 𝓀[F]ˣ :=
  Units.map (D.specialFibreEval.toMonoidHom.comp
    (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]).toMonoidHom)

theorem unitsEval_sq (u : (D.Carrier ⊗[CommRingCat.of 𝒪[F]] 𝓀[F])ˣ) :
    D.unitsEval u ^ 2 =
      Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F] u := by
  apply Units.ext
  change D.specialFibreEval (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]
      u.val) ^ 2 = Algebra.norm 𝓀[F]
        (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F] u.val)
  rw [norm_eq_specialFibreEval_sq]

theorem unitsEval_neg_one : D.unitsEval (-1) = -1 := by
  apply Units.ext
  change D.specialFibreEval (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]
      (-1)) = -1
  rw [map_neg, map_one, map_neg, map_one]

theorem neg_one_mem_ker :
    (-1 : (D.Carrier ⊗[CommRingCat.of 𝒪[F]] 𝓀[F])ˣ) ∈
      (Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]).ker := by
  rw [MonoidHom.mem_ker, ← unitsEval_sq, unitsEval_neg_one]
  exact neg_one_sq

/-- The sign of a special-fibre point `x + y α` (with `x ^ 2 = 1`): its value `x = ±1`
at `α = 0`. -/
def specialFibreSign : rationalPoints D.model.specialFibre →* 𝓀[F]ˣ :=
  D.unitsEval.comp
    ((Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier 𝓀[F]).ker.subtype.comp
      D.specialFibrePointsEquiv.toMonoidHom)

theorem specialFibreSign_sq (x : rationalPoints D.model.specialFibre) :
    D.specialFibreSign x ^ 2 = 1 := by
  change D.unitsEval (D.specialFibrePointsEquiv x).val ^ 2 = 1
  rw [unitsEval_sq]
  exact (D.specialFibrePointsEquiv x).2

theorem exists_specialFibreSign_eq_neg_one :
    ∃ x : rationalPoints D.model.specialFibre, D.specialFibreSign x = -1 := by
  refine ⟨D.specialFibrePointsEquiv.symm ⟨-1, D.neg_one_mem_ker⟩, ?_⟩
  change D.unitsEval (D.specialFibrePointsEquiv
    (D.specialFibrePointsEquiv.symm ⟨-1, D.neg_one_mem_ker⟩)).val = -1
  rw [MulEquiv.apply_symm_apply]
  exact D.unitsEval_neg_one

include D in
theorem one_ne_neg_one_units : (1 : 𝓀[F]ˣ) ≠ -1 := by
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_one, Units.val_neg, Units.val_one] at h'
  apply D.two_ne_zero_residue
  linear_combination h'

/-- The sign takes exactly the values `1` and `-1`. -/
theorem range_specialFibreSign :
    (D.specialFibreSign.range : Set 𝓀[F]ˣ) = {1, -1} := by
  ext y
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    have h := congrArg Units.val (D.specialFibreSign_sq x)
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq] at h
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · exact ⟨1, map_one _⟩
    · exact D.exists_specialFibreSign_eq_neg_one

/-- The kernel of the sign, the points `1 + y α` of the special fibre, has index two. -/
theorem index_ker_specialFibreSign : D.specialFibreSign.ker.index = 2 := by
  rw [Subgroup.index_ker, ← SetLike.coe_sort_coe, range_specialFibreSign,
    Nat.card_coe_set_eq, Set.ncard_pair D.one_ne_neg_one_units]

/-! ### Integral points: the index-two subgroup -/

/-- The sign of an integral section: the sign of its reduction. -/
def integralSign : D.model.integralSections →* 𝓀[F]ˣ :=
  D.specialFibreSign.comp D.model.reduction

theorem range_integralSign : D.integralSign.range = D.specialFibreSign.range := by
  let : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  rw [integralSign, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _
      (IntegralModel.reduction_surjective D.model D.model_isSmooth),
    ← MonoidHom.range_eq_map]

/-- The rational points of `R¹_{E/F} G_m` that come from integral sections whose
reduction has sign `1`. -/
def componentPoints : Subgroup (rationalPoints (normOne (CommRingCat.of F) D.GenericField)) :=
  D.integralSign.ker.map D.model.integralPointMap

theorem componentPoints_le_integralPoints : D.componentPoints ≤ D.model.integralPoints := by
  rintro g ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

/-- The congruence subgroup lies in the component points. -/
theorem congruenceSubgroup_le_componentPoints :
    D.model.congruenceSubgroup ≤ D.componentPoints := by
  rintro g ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  change D.specialFibreSign (D.model.reduction x) = 1
  rw [(IntegralModel.mem_congruenceKernel _ x).1 hx, map_one]

/-- **The ramified regression.** The component points have index two in the integral
points. -/
theorem relIndex_componentPoints :
    D.componentPoints.relIndex D.model.integralPoints = 2 := by
  rw [componentPoints, LocalFieldIntegralModel.integralPoints, IntegralModel.integralPoints,
    MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _
      (IntegralModel.integralPointMap_injective _), Subgroup.relIndex_top_right,
    Subgroup.index_ker, range_integralSign, ← Subgroup.index_ker,
    index_ker_specialFibreSign]

/-! ### Every norm-one point is integral -/

/-- If `a ^ 2 - ϖ b ^ 2 = 1` in `F`, then `b` lies in `𝒪[F]`. -/
theorem exists_integer_right_of_sq_sub (a b : F)
    (h : a ^ 2 - (D.uniformizer : F) * b ^ 2 = 1) : ∃ b₀ : 𝒪[F], (b₀ : F) = b := by
  by_contra hb
  have hb' : b ∉ 𝒪[F] := fun hm => hb ⟨⟨b, hm⟩, rfl⟩
  have hb0 : b ≠ 0 := fun h0 => hb' (h0 ▸ zero_mem _)
  have hinv : b⁻¹ ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff] at hb' ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hb'))
  obtain ⟨c, hcF⟩ : ∃ c : 𝒪[F], (c : F) = b⁻¹ := ⟨⟨b⁻¹, hinv⟩, rfl⟩
  have hc : ¬IsUnit c := by
    rintro ⟨w, hw⟩
    apply hb
    refine ⟨((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ?_⟩
    have h1 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * (c : F) = 1 := by
      rw [← hw, ← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
    rw [hcF] at h1
    exact (mul_inv_eq_one₀ hb0).1 h1
  obtain ⟨c', hc'⟩ : D.uniformizer ∣ c := by
    have hmem : c ∈ IsLocalRing.maximalIdeal 𝒪[F] := hc
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 D.irreducible,
      Ideal.mem_span_singleton] at hmem
  have ha : a ^ 2 = 1 + (D.uniformizer : F) * b ^ 2 := by linear_combination h
  have hint : IsIntegral 𝒪[F] (a * b⁻¹) := by
    refine ⟨X ^ 2 - C (c ^ 2 + D.uniformizer), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
    change (a * b⁻¹) ^ 2 = ((c ^ 2 + D.uniformizer : 𝒪[F]) : F)
    rw [Subring.coe_add, Subring.coe_pow, hcF, mul_pow, ha]
    field_simp
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have htc : t ^ 2 = c ^ 2 + D.uniformizer := by
    apply Subtype.val_injective
    rw [Subring.coe_pow, Subring.coe_add, Subring.coe_pow, hcF]
    change (algebraMap 𝒪[F] F t) ^ 2 = _
    rw [ht, mul_pow, ha]
    field_simp
  rw [hc'] at htc
  obtain ⟨s, rfl⟩ : D.uniformizer ∣ t :=
    D.irreducible.prime.dvd_of_dvd_pow (n := 2) ⟨D.uniformizer * c' ^ 2 + 1, by
      rw [htc]
      ring⟩
  have h1 : D.uniformizer * (D.uniformizer * (s ^ 2 - c' ^ 2)) = D.uniformizer * 1 := by
    linear_combination htc
  exact D.irreducible.not_isUnit
    (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ D.irreducible.ne_zero h1))

/-- If `a ^ 2 - ϖ b ^ 2 = 1` in `F`, then `a` and `b` come from `𝒪[F]`, where the
same equation holds. -/
theorem exists_integer_of_sq_sub (a b : F)
    (h : a ^ 2 - (D.uniformizer : F) * b ^ 2 = 1) :
    ∃ a₀ b₀ : 𝒪[F], (a₀ : F) = a ∧ (b₀ : F) = b ∧ a₀ ^ 2 - D.uniformizer * b₀ ^ 2 = 1 := by
  obtain ⟨b₀, rfl⟩ := D.exists_integer_right_of_sq_sub a b h
  have hint : IsIntegral 𝒪[F] a := by
    refine ⟨X ^ 2 - C (1 + D.uniformizer * b₀ ^ 2), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
    change a ^ 2 = ((1 + D.uniformizer * b₀ ^ 2 : 𝒪[F]) : F)
    rw [Subring.coe_add, Subring.coe_one, Subring.coe_mul, Subring.coe_pow]
    linear_combination h
  obtain ⟨a₀, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a₀, b₀, rfl, rfl, ?_⟩
  apply Subtype.val_injective
  push_cast
  exact h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The element `a + b α` of `B` and its conjugate `a - b α` multiply to
`a ^ 2 - ϖ b ^ 2`. -/
theorem mul_conj (a b : 𝒪[F]) :
    (AdjoinRoot.of D.polynomial a + AdjoinRoot.of D.polynomial b * AdjoinRoot.root D.polynomial) *
        (AdjoinRoot.of D.polynomial a -
          AdjoinRoot.of D.polynomial b * AdjoinRoot.root D.polynomial) =
      AdjoinRoot.of D.polynomial (a ^ 2 - D.uniformizer * b ^ 2) := by
  have h := Langlands.Algebra.root_sq D.uniformizer
  rw [map_sub, map_mul, map_pow, map_pow]
  linear_combination (-(AdjoinRoot.of D.polynomial b) ^ 2) * h

/-- **Norm-one units are constant.** If `S'` is an `𝒪[F]`-algebra isomorphic to
`F`, every norm-one unit of `B ⊗ S'` is `c ⊗ 1` for a norm-one unit `c` of `B`. -/
theorem exists_unit_of_normOne (S' : Type u) [CommRing S'] [Algebra 𝒪[F] S']
    (e : S' ≃ₐ[𝒪[F]] F) (u : (D.Carrier ⊗[CommRingCat.of 𝒪[F]] S')ˣ)
    (hu : Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier S' u = 1) :
    ∃ c : D.Carrierˣ, Algebra.norm 𝒪[F] (c : D.Carrier) = 1 ∧
      u.val = (c : D.Carrier) ⊗ₜ (1 : S') := by
  let β := (Langlands.Algebra.sqrtBasis D.uniformizer).baseChange S'
  let r : S' ⊗[CommRingCat.of 𝒪[F]] D.Carrier := 1 ⊗ₜ AdjoinRoot.root D.polynomial
  have h0 : β 0 = 1 := by
    rw [Module.Basis.baseChange_apply, Langlands.Algebra.sqrtBasis_zero]
    rfl
  have h1 : β 1 = r := by
    rw [Module.Basis.baseChange_apply, Langlands.Algebra.sqrtBasis_one]
  have hr : r ^ 2 = algebraMap S' _ (algebraMap 𝒪[F] S' D.uniformizer) := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.tmul_pow, one_pow, Langlands.Algebra.root_sq,
      AdjoinRoot.algebraMap_eq]
  obtain ⟨a, b, hy⟩ := Langlands.Algebra.exists_eq_algebraMap_add_mul β r h0 h1
    (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier S' u.val)
  have hN : a ^ 2 - algebraMap 𝒪[F] S' D.uniformizer * b ^ 2 = 1 := by
    have h := congrArg Units.val hu
    change Algebra.norm S' (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier S'
      u.val) = 1 at h
    rwa [hy, Langlands.Algebra.norm_algebraMap_add_mul _ β r h0 h1 hr] at h
  have hNF : (e a) ^ 2 - (D.uniformizer : F) * (e b) ^ 2 = 1 := by
    have h := congrArg e hN
    rwa [map_sub, map_mul, map_pow, map_pow, AlgEquiv.commutes, map_one] at h
  obtain ⟨a₀, b₀, ha, hb, hab⟩ := D.exists_integer_of_sq_sub (e a) (e b) hNF
  have ha' : a = algebraMap 𝒪[F] S' a₀ := by
    rw [← e.symm_apply_apply a, ← ha]
    exact e.symm.commutes a₀
  have hb' : b = algebraMap 𝒪[F] S' b₀ := by
    rw [← e.symm_apply_apply b, ← hb]
    exact e.symm.commutes b₀
  let x : D.Carrier :=
    AdjoinRoot.of D.polynomial a₀ + AdjoinRoot.of D.polynomial b₀ * AdjoinRoot.root D.polynomial
  let x' : D.Carrier :=
    AdjoinRoot.of D.polynomial a₀ - AdjoinRoot.of D.polynomial b₀ * AdjoinRoot.root D.polynomial
  have hxx' : x * x' = 1 := by
    rw [D.mul_conj, hab, map_one]
  refine ⟨Units.mkOfMulEqOne x x' hxx', ?_, ?_⟩
  · change Algebra.norm 𝒪[F] x = 1
    rw [Langlands.Algebra.norm_of_add_of_mul_root, hab]
  · apply (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) D.Carrier S').injective
    rw [hy, Units.val_mkOfMulEqOne, Algebra.TensorProduct.comm_tmul, ha', hb',
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add]
    rfl

/-- Global sections of `Spec F`, as an `𝒪[F]`-algebra through the inclusion,
are `F`. -/
def genericSectionsEquiv :
    ((algΓ (CommRingCat.of 𝒪[F])).obj
      ((Over.map (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))).obj
        (Over.mk (𝟙 _)))).unop ≃ₐ[CommRingCat.of 𝒪[F]] F :=
  { (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv with
    commutes' := fun r => by
      change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
          ((𝟙 _ ≫ baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).inv r)) =
        algebraMap 𝒪[F] F r
      rw [Category.id_comp]
      change ((baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of F)).hom)
            ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).inv r) = _
      rw [baseMap, Scheme.ΓSpecIso_naturality]
      simp }

/-- Base change of norm-one units from `B ⊗ Γ` to `(F ⊗ B) ⊗ Γ`, for `Γ` the global
sections of `Spec F`. The instance arguments are those of
`normOneAlgebraBaseChangeIso_hom_points`. -/
def genericTensorEquiv :=
  @normOneTensorEquiv (CommRingCat.of 𝒪[F]) (CommRingCat.of F) D.Carrier
    (restrictedSections (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
    (@CommRingCat.instCommRingObjForgetRingHomCarrier (CommRingCat.of 𝒪[F])) _ _ _ _ _
    (restrictedSectionsAlgebra _ _ _) _ (restrictedSectionsScalarTower _ _ _)

set_option maxRecDepth 4000 in
/-- The integral-point map on norm-one units: restrict to the generic point, then
transport along `F ⊗ B ≃ E`. -/
theorem integralPointMap_points (x : D.model.integralSections) :
    normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _))
        (D.model.integralPointMap x) =
      normOneCongrUnitsEquiv D.genericEquiv
        ((algΓ (CommRingCat.of F)).obj (Over.mk (𝟙 (Spec (CommRingCat.of F))))).unop
        (D.genericTensorEquiv
          (normOneUnitsRestrict (CommRingCat.of 𝒪[F]) D.Carrier
            (Over.homMk (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)) (by simp) :
              (Over.map (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))).obj
                (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _))
            (normOnePointsEquiv (CommRingCat.of 𝒪[F]) D.Carrier (Over.mk (𝟙 _)) x))) := by
  have h : D.model.integralPointMap x =
      (baseChangeSectionHom (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))
          (normOne (CommRingCat.of 𝒪[F]) D.Carrier) x ≫
        (normOneAlgebraBaseChangeIso (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
          D.Carrier).hom.hom.hom) ≫ (normOneCongrIso D.genericEquiv).hom.hom.hom := by
    rw [Category.assoc]
    rfl
  refine (congrArg (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _))) h).trans ?_
  have h2 := normOneCongrIso_hom_points D.genericEquiv (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    (baseChangeSectionHom (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))
          (normOne (CommRingCat.of 𝒪[F]) D.Carrier) x ≫
        (normOneAlgebraBaseChangeIso (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
          D.Carrier).hom.hom.hom)
  have h3 := normOneAlgebraBaseChangeIso_hom_points (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
    D.Carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    (baseChangeSectionHom (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))
          (normOne (CommRingCat.of 𝒪[F]) D.Carrier) x)
  have h4 := baseChangePointsEquiv_baseChangeSectionHom
    (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)) (normOne (CommRingCat.of 𝒪[F]) D.Carrier) x
  have h5 := normOnePointsEquiv_naturality (CommRingCat.of 𝒪[F]) D.Carrier
    (Over.homMk (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)) (by simp) :
      (Over.map (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))).obj
        (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _)) x
  refine h2.trans ?_
  congr 1
  refine h3.trans ?_
  exact congrArg D.genericTensorEquiv ((congrArg (normOnePointsEquiv (CommRingCat.of 𝒪[F])
    D.Carrier ((Over.map (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) h4).trans h5)

/-- The generic transport of norm-one units: base change from `B ⊗ Γ` to `(F ⊗ B) ⊗ Γ`,
then `F ⊗ B ≃ E`, for `Γ` the global sections of `Spec F`. -/
def genericNormOneEquiv :=
  D.genericTensorEquiv.trans (normOneCongrUnitsEquiv D.genericEquiv
    ((algΓ (CommRingCat.of F)).obj (Over.mk (𝟙 (Spec (CommRingCat.of F))))).unop)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem genericNormOneEquiv_apply (y : (Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F])
    D.Carrier ((algΓ (CommRingCat.of 𝒪[F])).obj ((Over.map (baseMap (CommRingCat.of 𝒪[F])
      (CommRingCat.of F))).obj (Over.mk (𝟙 _)))).unop).ker) :
    D.genericNormOneEquiv y = normOneCongrUnitsEquiv D.genericEquiv
      ((algΓ (CommRingCat.of F)).obj (Over.mk (𝟙 (Spec (CommRingCat.of F))))).unop
      (D.genericTensorEquiv y) := rfl

/-- A norm-one unit `c` of `B` gives the constant norm-one unit `c ⊗ 1` of `B ⊗ S`. -/
def constantNormOne (S : Type u) [CommRing S] [Algebra 𝒪[F] S] (c : D.Carrierˣ)
    (hc : Algebra.norm 𝒪[F] (c : D.Carrier) = 1) :
    (Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) D.Carrier S).ker :=
  ⟨Units.map (Algebra.TensorProduct.includeLeft :
      D.Carrier →ₐ[CommRingCat.of 𝒪[F]] D.Carrier ⊗[CommRingCat.of 𝒪[F]] S).toMonoidHom c, by
    apply Units.ext
    change Langlands.Algebra.tensorNorm _ D.Carrier S ((c : D.Carrier) ⊗ₜ 1) = 1
    have h := Langlands.Algebra.tensorNorm_naturality
      (Algebra.ofId (CommRingCat.of 𝒪[F]) S) ((c : D.Carrier) ⊗ₜ (1 : CommRingCat.of 𝒪[F]))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] at h
    rw [h]
    change algebraMap _ _ (Algebra.norm (CommRingCat.of 𝒪[F])
      ((Algebra.TensorProduct.lid (CommRingCat.of 𝒪[F]) D.Carrier).symm c)) = 1
    rw [Algebra.norm_eq_of_algEquiv]
    change algebraMap _ _ (Algebra.norm 𝒪[F] (c : D.Carrier)) = 1
    rw [hc, map_one]⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem constantNormOne_val (S : Type u) [CommRing S] [Algebra 𝒪[F] S] (c : D.Carrierˣ)
    (hc : Algebra.norm 𝒪[F] (c : D.Carrier) = 1) :
    ((D.constantNormOne S c hc).val : D.Carrier ⊗[CommRingCat.of 𝒪[F]] S) =
      (c : D.Carrier) ⊗ₜ 1 := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Constant norm-one units are unchanged by restriction along test morphisms. -/
theorem normOneUnitsRestrict_constantNormOne {T T' : Over (Spec (CommRingCat.of 𝒪[F]))}
    (a : T' ⟶ T) (c : D.Carrierˣ) (hc : Algebra.norm 𝒪[F] (c : D.Carrier) = 1) :
    normOneUnitsRestrict (CommRingCat.of 𝒪[F]) D.Carrier a (D.constantNormOne _ c hc) =
      D.constantNormOne _ c hc := by
  apply Subtype.ext
  apply Units.ext
  change Algebra.TensorProduct.lTensor (S := D.Carrier) D.Carrier _ ((c : D.Carrier) ⊗ₜ 1) =
    (c : D.Carrier) ⊗ₜ 1
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

/-- **Every norm-one point is integral.** The integral points of the model are
all of `R¹_{E/F} G_m (F)`. -/
theorem integralPoints_eq_top : D.model.integralPoints = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc, hcv⟩ := D.exists_unit_of_normOne
    (restrictedSections (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))) (genericSectionsEquiv (F := F))
    (D.genericNormOneEquiv.symm
      (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _)) g)).val
    (D.genericNormOneEquiv.symm
      (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _)) g)).property
  have hv : D.constantNormOne (restrictedSections (CommRingCat.of 𝒪[F]) (CommRingCat.of F)
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))) c hc =
      D.genericNormOneEquiv.symm
        (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _)) g) :=
    Subtype.ext (Units.ext hcv.symm)
  have e1 : normOneUnitsRestrict (CommRingCat.of 𝒪[F]) D.Carrier
      (Over.homMk (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F)) (by simp) :
        (Over.map (baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of F))).obj
          (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _))
      (normOnePointsEquiv (CommRingCat.of 𝒪[F]) D.Carrier (Over.mk (𝟙 _))
        ((normOnePointsEquiv (CommRingCat.of 𝒪[F]) D.Carrier (Over.mk (𝟙 _))).symm
          (D.constantNormOne _ c hc))) =
      D.genericNormOneEquiv.symm
        (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _)) g) :=
    (congrArg (normOneUnitsRestrict (CommRingCat.of 𝒪[F]) D.Carrier _)
      (MulEquiv.apply_symm_apply _ _)).trans
      ((D.normOneUnitsRestrict_constantNormOne _ c hc).trans hv)
  refine ⟨(normOnePointsEquiv (CommRingCat.of 𝒪[F]) D.Carrier (Over.mk (𝟙 _))).symm
    (D.constantNormOne _ c hc), ?_⟩
  apply (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _))).injective
  exact (D.integralPointMap_points _).trans ((D.genericNormOneEquiv_apply _).symm.trans
    ((congrArg D.genericNormOneEquiv e1).trans (MulEquiv.apply_symm_apply D.genericNormOneEquiv
      (normOnePointsEquiv (CommRingCat.of F) D.GenericField (Over.mk (𝟙 _)) g))))

/-- **The ramified regression, rational form.** The component points have index two
in the group of all rational points of `R¹_{E/F} G_m`. -/
theorem index_componentPoints : D.componentPoints.index = 2 := by
  rw [← Subgroup.relIndex_top_right, ← D.integralPoints_eq_top, relIndex_componentPoints]

end LocalField

end RamifiedQuadraticData

section Existence

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Ramified quadratic data exist exactly when `2` is a unit in `𝒪[F]`. -/
theorem RamifiedQuadraticData.nonempty_iff :
    Nonempty (RamifiedQuadraticData F) ↔ IsUnit (2 : 𝒪[F]) :=
  ⟨fun ⟨D⟩ => D.isUnit_two, fun h =>
    let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    ⟨⟨ϖ, hϖ, h⟩⟩⟩

end Existence

end Langlands.BruhatTits.IntegralModels
