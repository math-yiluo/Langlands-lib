import Langlands.GroupScheme.FiniteFreeAlgebraUnits
import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison
import Langlands.BruhatTits.IntegralModels.RelativeComponentConstruction
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integer


/-! # Unit group schemes of orders as integral models of `GL_N`, and the Iwahori model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

/-! ### The unit model attached to a generic matrix identification -/

section UnitModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [Ring A] [Algebra R A] {n : ℕ} (b : Module.Basis (Fin n) (CommRingCat.of R) A)
  (N : ℕ) (e : K ⊗[R] A ≃ₐ[K] Matrix (Fin N) (Fin N) K)


/-- Step 1 of the generic identification: base change of the unit group scheme. -/
def unitGenericIso₁ :
    (GroupScheme.baseChange (WeilGm.baseMap (CommRingCat.of R) (CommRingCat.of K))).obj
        (groupScheme (R := CommRingCat.of R) b) ≅
      groupScheme (b.baseChange (CommRingCat.of K)) :=
  baseChangeIso b (CommRingCat.of K)

/-- Step 2 of the generic identification: the algebra isomorphism `e`. -/
def unitGenericIso₂ :
    groupScheme (b.baseChange (CommRingCat.of K)) ≅
      groupScheme (matrixBasis (CommRingCat.of K) N) :=
  congrIso (b.baseChange (CommRingCat.of K)) (matrixBasis (CommRingCat.of K) N) e

/-- The generic identification of the unit group scheme with `GL_N` over `K`. -/
def unitGenericIso :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj
        (groupScheme (R := CommRingCat.of R) b) ≅
      GeneralLinear.groupScheme (Fin N) (CommRingCat.of K) :=
  unitGenericIso₁ R K b ≪≫ unitGenericIso₂ R K b N e ≪≫ generalLinearIso (CommRingCat.of K) N

/-- The unit group scheme of `A` over `R`, an integral model of `GL_N` over `K` through the
generic identification `e`. -/
def unitModel :
    IntegralModel R K (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)) where
  group := groupScheme (R := CommRingCat.of R) b
  affine := groupScheme_isAffineHom b
  flat := groupScheme_flat b
  finiteType := groupScheme_locallyOfFiniteType b
  genericIso := unitGenericIso R K b N e

/-- The unit model is smooth. -/
theorem unitModel_isSmooth : (unitModel R K b N e).IsSmooth :=
  smooth (R := CommRingCat.of R) b

/-- Restricting an integral section to the generic fibre sends its unit `u` to the matrix
`e (1 ⊗ u)`. -/
theorem unitModel_integralPointMap (x : (unitModel R K b N e).integralSections) :
    (GeneralLinear.rationalPointsEquiv N (CommRingCat.of K)
        ((unitModel R K b N e).integralPointMap x) : Matrix (Fin N) (Fin N) K) =
      e (1 ⊗ₜ (sectionUnitsEquiv (R := CommRingCat.of R) b x : A)) := by
  change rationalPoints (groupScheme (R := CommRingCat.of R) b) at x
  let A₀ := CommRingCat.of R
  let A' := CommRingCat.of K
  let T := Over.mk (𝟙 (Spec A'))
  let a : (Over.map (WeilGm.baseMap A₀ A')).obj T ⟶ Over.mk (𝟙 (Spec A₀)) :=
    Over.homMk (WeilGm.baseMap A₀ A') (by simp [T])
  let : Algebra A' (WeilGm.restrictedSections A₀ A' T) :=
    WeilGm.restrictedSectionsAlgebra A₀ A' T
  let : IsScalarTower A₀ A' (WeilGm.restrictedSections A₀ A' T) :=
    WeilGm.restrictedSectionsScalarTower A₀ A' T
  change ((GeneralLinear.glRingEquiv (GeneralLinear.globalSectionsEquiv A')
      (GeneralLinear.pointsEquiv (Fin N) A' T
        (baseChangeSectionHom (WeilGm.baseMap A₀ A') (groupScheme (R := A₀) b) x ≫
          (unitModel R K b N e).genericIso.hom.hom.hom)) : Matrix (Fin N) (Fin N) K)) = _
  dsimp only [unitModel, unitGenericIso, unitGenericIso₁, unitGenericIso₂, Iso.trans_hom]
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    generalLinearIso_hom_points, matrixPointsEquiv, MulEquiv.trans_apply,
    congrIso_hom_points, congrPointsEquiv, MulEquiv.trans_apply,
    baseChangeIso_hom_points b A' T, basePointsEquiv_apply b A' T,
    baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  let G : ((algΓ A₀).obj (Over.mk (𝟙 (Spec A₀)))).unop ⊗[A₀] A →+ Matrix (Fin N) (Fin N) K :=
    (WeilGm.selfSectionsAlgEquiv A').toRingEquiv.mapMatrix.toRingHom.toAddMonoidHom.comp
      ((matrixEquivTensor (Fin N) A' ((algΓ A').obj T).unop).symm.toAlgHom.toRingHom.toAddMonoidHom.comp
        ((Algebra.TensorProduct.congr
            (AlgEquiv.refl : ((algΓ A').obj T).unop ≃ₐ[A'] ((algΓ A').obj T).unop)
            e).toAlgHom.toRingHom.toAddMonoidHom.comp
          ((baseChangeTensorEquiv A A' (WeilGm.restrictedSections A₀ A' T)).toRingHom.toAddMonoidHom.comp
            (Algebra.TensorProduct.map ((algΓ A₀).map a).unop.hom
              (AlgHom.id A₀ A)).toRingHom.toAddMonoidHom)))
  suffices h : ∀ z : ((algΓ A₀).obj (Over.mk (𝟙 (Spec A₀)))).unop ⊗[A₀] A,
      G z = e (1 ⊗ₜ sectionTensorEquiv (R := A₀) (A := A) z) by
    exact h _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s c =>
      have hnat := ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K))) s
      change (Scheme.ΓSpecIso A').hom ((WeilGm.baseMap A₀ A').appTop s) =
        algebraMap R K ((Scheme.ΓSpecIso A₀).hom s) at hnat
      have hsec : ∀ k : K, WeilGm.selfSectionsAlgEquiv A'
          (algebraMap A' ((algΓ A').obj T).unop k) = k :=
        fun k => (WeilGm.selfSectionsAlgEquiv A').commutes k
      change (WeilGm.selfSectionsAlgEquiv A').toRingEquiv.mapMatrix
        ((matrixEquivTensor (Fin N) A' ((algΓ A').obj T).unop).symm
          (Algebra.TensorProduct.congr
            (AlgEquiv.refl : ((algΓ A').obj T).unop ≃ₐ[A'] ((algΓ A').obj T).unop) e
            (baseChangeTensorEquiv A A' (WeilGm.restrictedSections A₀ A' T)
              (Algebra.TensorProduct.map ((algΓ A₀).map a).unop.hom (AlgHom.id A₀ A)
                (s ⊗ₜ c))))) = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeTensorEquiv_tmul]
      ext i j
      change WeilGm.selfSectionsAlgEquiv A'
        (@id ((algΓ A').obj T).unop (((algΓ A₀).map a).unop.hom s) *
          algebraMap A' ((algΓ A').obj T).unop (e (1 ⊗ₜ c) i j)) = _
      rw [map_mul, hsec]
      change (Scheme.ΓSpecIso A').hom ((WeilGm.baseMap A₀ A').appTop s) * _ = _
      rw [hnat]
      change _ = e (1 ⊗ₜ ((Scheme.ΓSpecIso A₀).hom s • c)) i j
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K, map_smul]
      rfl
  | add z z' hz hz' =>
      rw [map_add, hz, hz', map_add, TensorProduct.tmul_add, map_add]

/-- Integral points of the unit model are the matrices `e (1 ⊗ u)` for units `u` of `A`. -/
theorem mem_unitModel_integralPoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K))) :
    g ∈ (unitModel R K b N e).integralPoints ↔
      ∃ u : Aˣ, (GeneralLinear.rationalPointsEquiv N (CommRingCat.of K) g :
        Matrix (Fin N) (Fin N) K) = e (1 ⊗ₜ (u : A)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sectionUnitsEquiv (R := CommRingCat.of R) b x, unitModel_integralPointMap R K b N e x⟩
  · rintro ⟨u, hu⟩
    let x : (unitModel R K b N e).integralSections :=
      (sectionUnitsEquiv (R := CommRingCat.of R) b).symm u
    have hx := unitModel_integralPointMap R K b N e x
    have hxu : sectionUnitsEquiv (R := CommRingCat.of R) b x = u :=
      MulEquiv.apply_symm_apply _ _
    refine ⟨x, ?_⟩
    apply (GeneralLinear.rationalPointsEquiv N (CommRingCat.of K)).injective
    apply Units.ext
    rw [hx, hxu]
    exact hu.symm

/-- The unit model as relative-component model data: it is smooth with geometrically connected
fibres, so it is its own relative identity component. -/
def unitModelData :
    BruhatTits.IntegralModels.RelativeComponentModelData R K
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)) where
  full := unitModel R K b N e
  neutral := unitModel R K b N e
  full_smooth := unitModel_isSmooth R K b N e
  neutral_smooth := unitModel_isSmooth R K b N e
  neutral_connectedFibres :=
    (unitModel R K b N e).hasConnectedFibres_of_geometricallyConnected
      (geometricallyConnected (R := CommRingCat.of R) b)
  inclusion :=
    { hom := 𝟙 _
      generic_comm := by simp }
  isRelativeComponent :=
    @isRelativeIdentityComponent_id_of_geometricallyConnected _ (groupScheme b)
      (geometricallyConnected (R := CommRingCat.of R) b)

/-- The neutral points of the unit model data are its integral points. -/
theorem unitModelData_neutralPoints :
    (unitModelData R K b N e).neutralPoints = (unitModel R K b N e).integralPoints :=
  (unitModelData R K b N e).neutralPoints_eq

end UnitModel

/-! ### Orders in the matrix algebra -/

section Order

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [Ring A] [Algebra R A] (N : ℕ) (φ : A →ₐ[R] Matrix (Fin N) (Fin N) K)

omit [IsDomain R] in
/-- An injective algebra map into `M_N(K)` whose image spans `M_N(K)` up to denominators is a
localization of modules at the nonzero elements of `R`. -/
theorem isLocalizedModule_of_order (hinj : Function.Injective φ)
    (hsurj : ∀ M : Matrix (Fin N) (Fin N) K, ∃ a : A, ∃ c ∈ nonZeroDivisors R, c • M = φ a) :
    IsLocalizedModule (nonZeroDivisors R) φ.toLinearMap where
  map_units c := by
    rw [← (Algebra.lsmul R (A := K) R (Matrix (Fin N) (Fin N) K)).commutes]
    exact (IsLocalization.map_units K c).map _
  surj M := by
    obtain ⟨a, c, hc, h⟩ := hsurj M
    exact ⟨(a, ⟨c, hc⟩), h⟩
  exists_of_eq {a a'} h := ⟨1, by rw [one_smul, one_smul]; exact hinj h⟩

/-- The generic identification `K ⊗[R] A ≃ M_N(K)`, `k ⊗ a ↦ k • φ a`, of an order. -/
def orderEquiv (hinj : Function.Injective φ)
    (hsurj : ∀ M : Matrix (Fin N) (Fin N) K, ∃ a : A, ∃ c ∈ nonZeroDivisors R, c • M = φ a) :
    K ⊗[R] A ≃ₐ[K] Matrix (Fin N) (Fin N) K :=
  AlgEquiv.ofBijective (AlgHom.liftEquiv R K A _ φ) (by
    have := isLocalizedModule_of_order R K N φ hinj hsurj
    have hbc := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K φ.toLinearMap
    have h : ⇑(AlgHom.liftEquiv R K A _ φ) = ⇑hbc.equiv := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul k a => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h]
    exact hbc.equiv.bijective)

omit [IsDomain R] in
@[simp]
theorem orderEquiv_tmul (hinj : Function.Injective φ)
    (hsurj : ∀ M : Matrix (Fin N) (Fin N) K, ∃ a : A, ∃ c ∈ nonZeroDivisors R, c • M = φ a)
    (k : K) (a : A) :
    orderEquiv R K N φ hinj hsurj (k ⊗ₜ a) = k • φ a :=
  rfl

variable {n : ℕ} (b : Module.Basis (Fin n) (CommRingCat.of R) A)
  (hinj : Function.Injective φ)
  (hsurj : ∀ M : Matrix (Fin N) (Fin N) K, ∃ a : A, ∃ c ∈ nonZeroDivisors R, c • M = φ a)

/-- The unit group scheme of an `R`-order `A` in `M_N(K)`, as an integral model of `GL_N`. -/
def orderModel :
    IntegralModel R K (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)) :=
  unitModel R K b N (orderEquiv R K N φ hinj hsurj)

/-- Integral points of an order model are the images of the units of the order. -/
theorem mem_orderModel_integralPoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K))) :
    g ∈ (orderModel R K N φ b hinj hsurj).integralPoints ↔
      ∃ u : Aˣ, (GeneralLinear.rationalPointsEquiv N (CommRingCat.of K) g :
        Matrix (Fin N) (Fin N) K) = φ (u : A) := by
  refine (mem_unitModel_integralPoints R K b N (orderEquiv R K N φ hinj hsurj) g).trans ?_
  simp only [orderEquiv_tmul, one_smul]

/-- The order model as relative-component model data with equal full and neutral models. -/
def orderModelData :
    BruhatTits.IntegralModels.RelativeComponentModelData R K
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)) :=
  unitModelData R K b N (orderEquiv R K N φ hinj hsurj)

theorem orderModelData_neutralPoints :
    (orderModelData R K N φ b hinj hsurj).neutralPoints =
      (orderModel R K N φ b hinj hsurj).integralPoints :=
  unitModelData_neutralPoints R K b N _

end Order

end Langlands.GroupScheme.FiniteFreeAlgebraUnits

/-! ### The standard Iwahori order -/

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits
open Langlands.GeneralLinear.BlockShape (singletons singletons_mem_parabolic_iff)
open scoped ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- The standard Iwahori order in `M_N(𝒪[F])`: integral matrices whose strictly lower
entries lie in the maximal ideal. -/
def iwahoriOrder : Subalgebra 𝒪[F] (Matrix (Fin N) (Fin N) 𝒪[F]) where
  carrier := {M | ∀ i j : Fin N, j < i → M i j ∈ IsLocalRing.maximalIdeal 𝒪[F]}
  mul_mem' {M M'} hM hM' i j hij := by
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · exact Ideal.mul_mem_right _ _ (hM i k hk)
    · exact Ideal.mul_mem_left _ _ (hM' k j (lt_of_lt_of_le hij hk))
  add_mem' {M M'} hM hM' i j hij := Ideal.add_mem _ (hM i j hij) (hM' i j hij)
  algebraMap_mem' r i j hij := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', smul_zero]
    exact Ideal.zero_mem _

variable {F N} in
theorem mem_iwahoriOrder (M : Matrix (Fin N) (Fin N) 𝒪[F]) :
    M ∈ iwahoriOrder F N ↔ ∀ i j : Fin N, j < i → M i j ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
  Iff.rfl

instance iwahoriOrder_finite : Module.Finite 𝒪[F] (iwahoriOrder F N) :=
  inferInstanceAs (Module.Finite 𝒪[F] (Subalgebra.toSubmodule (iwahoriOrder F N)))

instance iwahoriOrder_free : Module.Free 𝒪[F] (iwahoriOrder F N) :=
  inferInstanceAs (Module.Free 𝒪[F] (Subalgebra.toSubmodule (iwahoriOrder F N)))

/-- A basis of the Iwahori order over `𝒪[F]`. -/
noncomputable def iwahoriBasis :
    Module.Basis (Fin (Module.finrank 𝒪[F] (iwahoriOrder F N))) (CommRingCat.of 𝒪[F])
      (iwahoriOrder F N) :=
  Module.finBasis 𝒪[F] (iwahoriOrder F N)

/-- The inclusion of the Iwahori order into `M_N(F)`. -/
def iwahoriInclusion : iwahoriOrder F N →ₐ[𝒪[F]] Matrix (Fin N) (Fin N) F :=
  (Algebra.ofId 𝒪[F] F).mapMatrix.comp (iwahoriOrder F N).val

theorem iwahoriInclusion_apply (a : iwahoriOrder F N) :
    iwahoriInclusion F N a = (a : Matrix (Fin N) (Fin N) 𝒪[F]).map (algebraMap 𝒪[F] F) :=
  rfl

theorem iwahoriInclusion_injective : Function.Injective (iwahoriInclusion F N) := by
  intro a a' h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact IsFractionRing.injective 𝒪[F] F (congrFun (congrFun h i) j)

/-- Every matrix over `F` is a multiple of a matrix in the Iwahori order by a nonzero integer. -/
theorem iwahoriInclusion_spans (M : Matrix (Fin N) (Fin N) F) :
    ∃ a : iwahoriOrder F N, ∃ c ∈ nonZeroDivisors 𝒪[F], c • M = iwahoriInclusion F N a := by
  obtain ⟨⟨b₀, hb₀⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors 𝒪[F]) (fun p : Fin N × Fin N => M p.1 p.2)
  choose y hy using hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  refine ⟨⟨Matrix.of fun i j => ϖ * y (i, j), fun i j _ => Ideal.mul_mem_right _ _ hϖm⟩,
    ϖ * b₀, mul_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hb₀, ?_⟩
  ext i j
  have h := hy (i, j)
  simp only at h
  rw [iwahoriInclusion_apply, Matrix.smul_apply, Matrix.map_apply]
  change _ = algebraMap 𝒪[F] F (ϖ * y (i, j))
  rw [map_mul, h, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-- The Iwahori model: the unit group scheme of the Iwahori order, an integral model of
`GL_N` over `𝒪[F]`. -/
def iwahoriModel :
    IntegralModel 𝒪[F] F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  orderModel 𝒪[F] F N (iwahoriInclusion F N) (iwahoriBasis F N)
    (iwahoriInclusion_injective F N) (iwahoriInclusion_spans F N)

/-- The Iwahori model is smooth. -/
theorem iwahoriModel_isSmooth : (iwahoriModel F N).IsSmooth :=
  unitModel_isSmooth 𝒪[F] F (iwahoriBasis F N) N _

/-- The inverse of an invertible integral matrix whose strictly lower entries lie in the
maximal ideal has the same property. -/
theorem inv_mem_iwahoriOrder (v : GL (Fin N) 𝒪[F])
    (hv : (v : Matrix (Fin N) (Fin N) 𝒪[F]) ∈ iwahoriOrder F N) :
    ((v⁻¹ : GL (Fin N) 𝒪[F]) : Matrix (Fin N) (Fin N) 𝒪[F]) ∈ iwahoriOrder F N := by
  have h1 : glResidueMap F N v ∈ (singletons N).parabolic 𝓀[F] :=
    (singletons_mem_parabolic_iff 𝓀[F] _).mpr ((glResidueMap_isUpperTriangular_iff v).mpr hv)
  have h2 : glResidueMap F N v⁻¹ ∈ (singletons N).parabolic 𝓀[F] := by
    rw [map_inv]
    exact inv_mem h1
  exact (glResidueMap_isUpperTriangular_iff v⁻¹).mp ((singletons_mem_parabolic_iff 𝓀[F] _).mp h2)

/-- **Integral points of the Iwahori model.** They are the standard Iwahori subgroup `I` of
the published comparison. -/
theorem iwahoriModel_integralPoints :
    (iwahoriModel F N).integralPoints = generalLinearIwahoriPoints F N := by
  ext g
  rw [iwahoriModel, mem_orderModel_integralPoints, mem_generalLinearIwahoriPoints]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Units.map (iwahoriOrder F N).val.toMonoidHom u,
      fun i j hij => (u : iwahoriOrder F N).2 i j hij, ?_⟩
    apply Units.ext
    rw [hu]
    rfl
  · rintro ⟨v, hv, hg⟩
    let u : (iwahoriOrder F N)ˣ :=
      ⟨⟨v, hv⟩, ⟨((v⁻¹ : GL (Fin N) 𝒪[F]) : Matrix (Fin N) (Fin N) 𝒪[F]),
        inv_mem_iwahoriOrder F N v hv⟩,
        Subtype.ext v.mul_inv, Subtype.ext v.inv_mul⟩
    refine ⟨u, ?_⟩
    rw [hg]
    rfl

/-- The Iwahori model as relative-component model data: the full and neutral models are both
the Iwahori model. -/
def iwahoriModelData :
    RelativeComponentModelData 𝒪[F] F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  orderModelData 𝒪[F] F N (iwahoriInclusion F N) (iwahoriBasis F N)
    (iwahoriInclusion_injective F N) (iwahoriInclusion_spans F N)

/-- The neutral points of the Iwahori model data are the Iwahori subgroup `I`. -/
theorem iwahoriModelData_neutralPoints :
    (iwahoriModelData F N).neutralPoints = generalLinearIwahoriPoints F N :=
  (orderModelData_neutralPoints _ _ _ _ _ _ _).trans (iwahoriModel_integralPoints F N)

/-- **Hyperspecial versus Iwahori, at the level of models.** For `N ≥ 2` the neutral points of
the Iwahori model data form a proper subgroup of those of the standard model data
`GL_{N,𝒪[F]}`. -/
theorem iwahoriModelData_neutralPoints_lt (hN : 2 ≤ N) :
    (iwahoriModelData F N).neutralPoints < (generalLinearModelData F N).neutralPoints := by
  rw [iwahoriModelData_neutralPoints, (generalLinearModelData F N).neutralPoints_eq]
  exact generalLinearIwahoriPoints_lt_integralPoints hN

/-- For `N ≤ 1` the two model data have the same neutral points. -/
theorem iwahoriModelData_neutralPoints_of_le_one (hN : N ≤ 1) :
    (iwahoriModelData F N).neutralPoints = (generalLinearModelData F N).neutralPoints := by
  rw [iwahoriModelData_neutralPoints, (generalLinearModelData F N).neutralPoints_eq]
  exact generalLinearIwahoriPoints_of_le_one hN

end Langlands.BruhatTits.IntegralModels
