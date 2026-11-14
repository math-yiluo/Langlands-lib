import Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Torus.Split

/-! # Integral charts of the quadratic unitary parameter group

Let `O` be a domain with fraction field `K`, and let `L / K` be a separable quadratic extension.
A chart `D` of the unitary parameter group `U_{L/K}` (a `K`-basis `e` of `L`, a trace-one
element `λ` and a nonzero trace-zero element `f`) whose cocycle coefficients `cᵢⱼ` lie in `O`
defines the bilinear coordinate group scheme over `Spec O` with coefficients `cᵢⱼ`. This module
identifies its generic fibre with `U_{L/K}` on all test schemes over `Spec K`, packages it as an
`IntegralModel`, computes its integral points, and constructs the model homomorphisms induced by
integral changes of chart. This is the construction of Kaletha–Prasad (C.4.1)–(C.4.2) for an
arbitrary chart; the lattice charts giving `X_{r,s}` are in `SU3RootUnitaryIntegralModel`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w w'

open scoped TensorProduct
open CategoryTheory Opposite AlgebraicGeometry Module

attribute [local instance] CategoryTheory.Hom.group

namespace Langlands.GroupScheme.SU3Root

open BilinearCoordinate

/-! ### Coefficient changes of bilinear coordinates -/

section CoordinatesCongr

variable {ι : Type w} [Fintype ι] {S : Type v} {T : Type w'} [CommRing S] [CommRing T]

/-- A ring isomorphism matching the coefficients identifies the bilinear coordinate groups. -/
def coordinatesCongr {c : ι → ι → S} {d : ι → ι → T} (e : S ≃+* T) (h : ∀ i j, e (c i j) = d i j) :
    Coordinates c ≃* Coordinates d where
  toFun := Coordinates.map e.toRingHom h
  invFun := Coordinates.map e.symm.toRingHom (fun i j => by
    rw [← h i j]
    exact e.symm_apply_apply (c i j))
  left_inv x := by
    apply Coordinates.ext
    · funext i
      exact e.symm_apply_apply (x.vec i)
    · exact e.symm_apply_apply x.scalar
  right_inv x := by
    apply Coordinates.ext
    · funext i
      exact e.apply_symm_apply (x.vec i)
    · exact e.apply_symm_apply x.scalar
  map_mul' := (Coordinates.map e.toRingHom h).map_mul

@[simp] theorem vec_coordinatesCongr {c : ι → ι → S} {d : ι → ι → T} (e : S ≃+* T)
    (h : ∀ i j, e (c i j) = d i j) (x : Coordinates c) (i : ι) :
    (coordinatesCongr e h x).vec i = e (x.vec i) := rfl

@[simp] theorem scalar_coordinatesCongr {c : ι → ι → S} {d : ι → ι → T} (e : S ≃+* T)
    (h : ∀ i j, e (c i j) = d i j) (x : Coordinates c) :
    (coordinatesCongr e h x).scalar = e x.scalar := rfl

end CoordinatesCongr

/-! ### Changes of chart -/

section ChartChange

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local notation "σ" => conjugation k L

/-- The correction is bilinear for finite `k`-linear combinations. -/
theorem correction_sum_sum {ι κ : Type w} [Fintype ι] [Fintype κ] (lam : L) (a : ι → k)
    (x : ι → L) (b : κ → k) (y : κ → L) :
    correction k L lam (∑ i, algebraMap k L (a i) * x i) (∑ l, algebraMap k L (b l) * y l) =
      ∑ i, ∑ l, algebraMap k L (a i * b l) * correction k L lam (x i) (y l) := by
  have hl : ∀ (s : Finset ι) (f : ι → L) (z : L),
      correction k L lam (∑ i ∈ s, f i) z = ∑ i ∈ s, correction k L lam (f i) z := by
    intro s f z
    induction s using Finset.cons_induction with
    | empty => simp [correction]
    | cons p s hp ih => rw [Finset.sum_cons, Finset.sum_cons, correction_add_left, ih]
  have hr : ∀ (s : Finset κ) (z : L) (f : κ → L),
      correction k L lam z (∑ l ∈ s, f l) = ∑ l ∈ s, correction k L lam z (f l) := by
    intro s z f
    induction s using Finset.cons_induction with
    | empty => simp [correction]
    | cons p s hp ih => rw [Finset.sum_cons, Finset.sum_cons, correction_add_right, ih]
  rw [hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [correction_smul_left, correction_smul_right, map_mul]
  ring

variable {ι κ : Type w} [Fintype ι] [Fintype κ]

/-- `D'` is obtained from `D` by the change of chart `(M, t)`: both use the same trace-one
element, `eᵢ = ∑ₗ Mᵢₗ e'ₗ` and `f = t f'`. -/
structure CoordinateData.IsChartChange (D : CoordinateData k L ι) (D' : CoordinateData k L κ)
    (M : ι → κ → k) (t : k) : Prop where
  traceOne_eq : D.traceOne = D'.traceOne
  basis_eq : ∀ i, D.basis i = ∑ l, algebraMap k L (M i l) * D'.basis l
  center_eq : D.center = algebraMap k L t * D'.center

namespace CoordinateData.IsChartChange

variable {D : CoordinateData k L ι} {D' : CoordinateData k L κ} {M : ι → κ → k} {t : k}

/-- A change of chart transforms the cocycle coefficients compatibly. -/
theorem isCompatible (h : D.IsChartChange D' M t) : IsCompatible D.coeff D'.coeff M t := by
  intro i j
  apply (algebraMap k L).injective
  apply mul_right_cancel₀ D'.center_ne_zero
  have hD : ∀ i j, algebraMap k L (D.coeff i j) * D.center =
      correction k L D'.traceOne (D.basis i) (D.basis j) := by
    intro i j
    rw [← h.traceOne_eq]
    exact D.coeff_mul_center i j
  calc algebraMap k L (∑ p, ∑ q, M i p * M j q * D'.coeff p q) * D'.center
      = ∑ p, ∑ q, algebraMap k L (M i p * M j q) *
          (algebraMap k L (D'.coeff p q) * D'.center) := by
        simp only [map_sum, map_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = correction k L D'.traceOne (D.basis i) (D.basis j) := by
        rw [h.basis_eq i, h.basis_eq j, correction_sum_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [D'.coeff_mul_center]
    _ = algebraMap k L (t * D.coeff i j) * D'.center := by
        rw [← hD, h.center_eq, map_mul]
        ring

/-- The vector coordinates transform by the matrix of the change of chart. -/
theorem tensorVec_matrixVec (h : D.IsChartChange D' M t) (S : Type w') [CommRing S]
    [Algebra k S] (a : ι → S) :
    tensorVec D' S (matrixVec (fun i l => algebraMap k S (M i l)) a) = tensorVec D S a := by
  simp only [tensorVec, matrixVec, h.basis_eq, TensorProduct.tmul_sum, TensorProduct.sum_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
    mul_comm]

/-- **Change of chart.** The identifications of two charts related by `(M, t)` differ by the
coordinate change `(a, b) ↦ (M a, t b)`. -/
theorem toParameters_linearMap (h : D.IsChartChange D' M t) (S : Type w') [CommRing S]
    [Algebra k S] (x : Coordinates (coeffs D S)) :
    toParameters D' S (Coordinates.linearMap (fun i l => algebraMap k S (M i l))
        (algebraMap k S t) (h.isCompatible.map (algebraMap k S)) x) =
      toParameters D S x := by
  have hvec := h.tensorVec_matrixVec S x.vec
  apply Parameters.ext
  · exact hvec
  · change secondCoord D' S (matrixVec (fun i l => algebraMap k S (M i l)) x.vec)
        (algebraMap k S t * x.scalar) = secondCoord D S x.vec x.scalar
    rw [secondCoord, secondCoord, hvec, h.traceOne_eq, h.center_eq]
    congr 1
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact TensorProduct.smul_tmul t x.scalar D'.center

end CoordinateData.IsChartChange

end ChartChange

/-! ### Integral charts -/

section IntegralChart

variable (O K L : Type u) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- A chart of `U_{L/K}` whose cocycle coefficients lie in `O`. -/
structure IntegralChart (ι : Type u) [Fintype ι] where
  /-- The chart over `K`. -/
  data : CoordinateData K L ι
  /-- The cocycle coefficients, as elements of `O`. -/
  coeff : ι → ι → O
  algebraMap_coeff : ∀ i j, algebraMap O K (coeff i j) = data.coeff i j

variable {O K L}

/-- Global sections of a test scheme over `Spec K`, as an `O`-algebra through `Spec O`. -/
abbrev restrictedSections (T : Over (Spec (CommRingCat.of K))) : CommAlgCat (CommRingCat.of O) :=
  ((algΓ (CommRingCat.of O)).obj ((Over.map (Spec.algebraMap O K)).obj T)).unop

/-- The restricted sections of `T` are the global sections of `T` as a `K`-algebra. -/
instance restrictedSectionsAlgebra (T : Over (Spec (CommRingCat.of K))) :
    Algebra K (restrictedSections (O := O) T) :=
  inferInstanceAs (Algebra K ((algΓ (CommRingCat.of K)).obj T).unop)

instance restrictedSectionsScalarTower (T : Over (Spec (CommRingCat.of K))) :
    IsScalarTower O K (restrictedSections (O := O) T) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change (T.hom ≫ Spec.algebraMap O K).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) =
    T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (algebraMap O K r))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap O K))) r).symm

omit [IsDomain O] [IsFractionRing O K] in
/-- The coefficients through `Spec O` and through `Spec K` agree. -/
theorem algebraMap_restrictedSections (T : Over (Spec (CommRingCat.of K))) (a : O) :
    algebraMap O (restrictedSections (O := O) T) a =
      algebraMap K (restrictedSections (O := O) T) (algebraMap O K a) :=
  IsScalarTower.algebraMap_apply O K _ a

namespace IntegralChart

variable {ι : Type u} [Fintype ι] (C : IntegralChart O K L ι)

/-- The bilinear coordinate group scheme over `Spec O` of an integral chart. -/
abbrev group : GroupScheme (Spec (CommRingCat.of O)) :=
  BilinearCoordinate.groupScheme (CommRingCat.of O) C.coeff

/-- Over the restricted sections, the integral and generic coefficients agree. -/
def sectionsCoordinatesEquiv (T : Over (Spec (CommRingCat.of K))) :
    Coordinates (algebraCoefficients (CommRingCat.of O) C.coeff (restrictedSections (O := O) T)) ≃*
      Coordinates (coeffs C.data ((algΓ (CommRingCat.of K)).obj T).unop) :=
  coordinatesCongr (RingEquiv.refl _) (fun i j => by
    change algebraMap O (restrictedSections (O := O) T) (C.coeff i j) =
      algebraMap K (restrictedSections (O := O) T) (C.data.coeff i j)
    rw [algebraMap_restrictedSections, C.algebraMap_coeff])

/-- Points of the generic fibre over a test scheme `T` over `Spec K` are quadratic root
parameters over the global sections of `T`. -/
def genericPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((baseChange (Spec.algebraMap O K)).obj C.group).X) ≃*
      tensorParameters K L ((algΓ (CommRingCat.of K)).obj T).unop :=
  (GroupScheme.baseChangePointsEquiv (Spec.algebraMap O K) C.group T).trans
    ((BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff
        ((Over.map (Spec.algebraMap O K)).obj T)).trans
      ((C.sectionsCoordinatesEquiv T).trans (toParameters C.data _)))

omit [IsDomain O] [IsFractionRing O K] in
theorem genericPointsEquiv_apply (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((baseChange (Spec.algebraMap O K)).obj C.group).X) :
    C.genericPointsEquiv T x = toParameters C.data _ (C.sectionsCoordinatesEquiv T
      (BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff _
        (GroupScheme.baseChangePointsEquiv (Spec.algebraMap O K) C.group T x))) := rfl

omit [IsDomain O] [IsFractionRing O K] in
/-- The generic point model is natural in the test scheme. -/
theorem genericPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ ((baseChange (Spec.algebraMap O K)).obj C.group).X) :
    C.genericPointsEquiv T' (a ≫ x) =
      tensorParametersMap K L ((algΓ (CommRingCat.of K)).map a).unop.hom
        (C.genericPointsEquiv T x) := by
  rw [genericPointsEquiv_apply, genericPointsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_naturality, BilinearCoordinate.pointsEquiv_naturality,
    ← toParameters_naturality]
  rfl

/-- **The integral model of a chart.** The bilinear coordinate group scheme over `Spec O`, with
the identification of its generic fibre with `U_{L/K}` on all test schemes over `Spec K`. -/
def model : IntegralModel O K (unitaryParameterGroup K L) where
  group := C.group
  affine := BilinearCoordinate.isAffineHom _ _
  flat := BilinearCoordinate.flat _ _
  finiteType := BilinearCoordinate.locallyOfFiniteType _ _
  genericIso :=
    isoOfPointModels
      (fun T : Over (Spec (CommRingCat.of K)) =>
        tensorParameters K L ((algΓ (CommRingCat.of K)).obj T).unop)
      (fun a => tensorParametersMap K L ((algΓ (CommRingCat.of K)).map a).unop.hom)
      C.genericPointsEquiv (unitaryPointsEquiv K L)
      (fun a x => C.genericPointsEquiv_naturality a x)
      (fun a y => unitaryPointsEquiv_naturality K L a y)

@[simp] theorem model_group : C.model.group = C.group := rfl

/-- The model is smooth. -/
theorem model_isSmooth : C.model.IsSmooth := BilinearCoordinate.smooth _ _

/-- The model has geometrically connected fibres. -/
instance model_geometricallyConnected : GeometricallyConnected C.model.group.X.hom :=
  BilinearCoordinate.geometricallyConnected _ _

/-- On points over every test scheme, the generic identification is the chart identification. -/
theorem unitaryPointsEquiv_genericIso (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((baseChange (Spec.algebraMap O K)).obj C.group).X) :
    unitaryPointsEquiv K L T (x ≫ C.model.genericIso.hom.hom.hom) = C.genericPointsEquiv T x :=
  isoOfPointModels_hom
    (fun T : Over (Spec (CommRingCat.of K)) =>
      tensorParameters K L ((algΓ (CommRingCat.of K)).obj T).unop)
    (fun a => tensorParametersMap K L ((algΓ (CommRingCat.of K)).map a).unop.hom)
    C.genericPointsEquiv (unitaryPointsEquiv K L)
    (fun a x => C.genericPointsEquiv_naturality a x)
    (fun a y => unitaryPointsEquiv_naturality K L a y) T x

/-! #### Integral points -/

/-- Integral sections of the model are bilinear coordinates with entries in `O`. -/
def integralCoordinatesEquiv : C.model.integralSections ≃* Coordinates C.coeff :=
  (BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff (Over.mk (𝟙 _))).trans
    (coordinatesCongr (identitySectionsEquiv (CommRingCat.of O)).toRingEquiv (fun i j => by
      change identitySectionsEquiv (CommRingCat.of O)
        (algebraMap (CommRingCat.of O) _ (C.coeff i j)) = C.coeff i j
      rw [AlgEquiv.commutes]
      rfl))

@[simp] theorem vec_integralCoordinatesEquiv (x : C.model.integralSections) (i : ι) :
    (C.integralCoordinatesEquiv x).vec i = identitySectionsEquiv (CommRingCat.of O)
      ((BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff (Over.mk (𝟙 _)) x).vec i) :=
  rfl

@[simp] theorem scalar_integralCoordinatesEquiv (x : C.model.integralSections) :
    (C.integralCoordinatesEquiv x).scalar = identitySectionsEquiv (CommRingCat.of O)
      (BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff (Over.mk (𝟙 _)) x).scalar :=
  rfl

/-- The base change of an integral section is the section composed with `Spec K → Spec O`. -/
theorem baseChangePointsEquiv_baseChangeSectionHom (x : C.model.integralSections) :
    GroupScheme.baseChangePointsEquiv (Spec.algebraMap O K) C.group (Over.mk (𝟙 _))
        (baseChangeSectionHom (Spec.algebraMap O K) C.group x) =
      (Over.homMk (Spec.algebraMap O K) (by simp) :
        (Over.map (Spec.algebraMap O K)).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _)) ≫ x := by
  apply Over.OverMorphism.ext
  rw [GroupScheme.baseChangePointsEquiv_left, baseChangeSectionHom_fst]
  rfl

omit [IsDomain O] [IsFractionRing O K] in
/-- `identitySectionsEquiv` is natural for `Spec K → Spec O`. -/
theorem identitySectionsEquiv_appTop
    (z : ((algΓ (CommRingCat.of O)).obj (Over.mk (𝟙 (Spec (CommRingCat.of O))))).unop) :
    identitySectionsEquiv (CommRingCat.of K) ((Spec.algebraMap O K).appTop z) =
      algebraMap O K (identitySectionsEquiv (CommRingCat.of O) z) := by
  rw [identitySectionsEquiv_apply, identitySectionsEquiv_apply]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O K))) z

end IntegralChart

end IntegralChart

/-! ### Field points of a chart -/

section FieldPoint

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {ι : Type w} [Fintype ι]

/-- The field point of `U_{L/k}` with chart coordinates `(a, b)`:
`(u, v) = (∑ aᵢ eᵢ, b f + λ u σ(u))`. -/
def fieldPoint (D : CoordinateData k L ι) (a : ι → k) (b : k) : rationalParameters k L :=
  rationalParametersEquiv k L (toParameters D k ⟨a, b⟩)

theorem first_fieldPoint (D : CoordinateData k L ι) (a : ι → k) (b : k) :
    (fieldPoint D a b).first = ∑ i, algebraMap k L (a i) * D.basis i := by
  simp only [fieldPoint, rationalParametersEquiv_first, first_toParameters, map_sum,
    Algebra.TensorProduct.lid_tmul, Algebra.smul_def]

theorem second_fieldPoint (D : CoordinateData k L ι) (a : ι → k) (b : k) :
    (fieldPoint D a b).second = algebraMap k L b * D.center +
      D.traceOne * (fieldPoint D a b).first * conjugation k L (fieldPoint D a b).first := by
  have h1 : (fieldPoint D a b).first = Algebra.TensorProduct.lid k L (tensorVec D k a) := rfl
  rw [h1, ← fieldInvolution_bar, ← rationalTensor_bar]
  simp only [fieldPoint, rationalParametersEquiv_second, second_toParameters, map_add, map_mul,
    Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
  simp

end FieldPoint

/-! ### Integral points and changes of chart -/

section IntegralChartPoints

variable {O K L : Type u} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace IntegralChart

variable {ι : Type u} [Fintype ι] (C : IntegralChart O K L ι)

/-- **Integral points.** The image of an integral section in `U_{L/K}(K)` is the field point
whose chart coordinates are its coordinates in `O`. -/
theorem unitaryRationalPointsEquiv_integralPointMap (x : C.model.integralSections) :
    unitaryRationalPointsEquiv K L (C.model.integralPointMap x) =
      fieldPoint C.data (fun i => algebraMap O K ((C.integralCoordinatesEquiv x).vec i))
        (algebraMap O K (C.integralCoordinatesEquiv x).scalar) := by
  change rationalParametersEquiv K L (tensorParametersCongr K L _
      (unitaryPointsEquiv K L _ (baseChangeSectionHom (Spec.algebraMap O K) C.group x ≫
        C.model.genericIso.hom.hom.hom))) = _
  rw [unitaryPointsEquiv_genericIso, genericPointsEquiv_apply,
    baseChangePointsEquiv_baseChangeSectionHom, BilinearCoordinate.pointsEquiv_naturality]
  rw [fieldPoint]
  congr 1
  have hcongr : ∀ (S : Type u) [CommRing S] [Algebra K S] (e : S ≃ₐ[K] K)
      (p : tensorParameters K L S), tensorParametersCongr K L e p =
        tensorParametersMap K L e.toAlgHom p := by
    intro S _ _ e p
    have h : ∀ w : S ⊗[K] L, Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[K] L) w =
        tensorCoefficientMap K L e.toAlgHom w := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul s y => rfl
      | add w w' hw hw' => simp only [map_add, hw, hw']
    apply Parameters.ext
    · exact h p.first
    · exact h p.second
  rw [hcongr, ← toParameters_naturality]
  congr 1
  apply Coordinates.ext
  · funext i
    exact identitySectionsEquiv_appTop _
  · exact identitySectionsEquiv_appTop _

/-- **Integral points.** A rational point of `U_{L/K}` is integral for the model exactly when it
is the field point of chart coordinates in `O`. -/
theorem mem_integralPoints_iff (g : rationalPoints (unitaryParameterGroup K L)) :
    g ∈ C.model.integralPoints ↔ ∃ (a : ι → O) (b : O),
      unitaryRationalPointsEquiv K L g =
        fieldPoint C.data (fun i => algebraMap O K (a i)) (algebraMap O K b) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, _, C.unitaryRationalPointsEquiv_integralPointMap x⟩
  · rintro ⟨a, b, h⟩
    refine ⟨C.integralCoordinatesEquiv.symm ⟨a, b⟩, ?_⟩
    apply (unitaryRationalPointsEquiv K L).injective
    rw [C.unitaryRationalPointsEquiv_integralPointMap, MulEquiv.apply_symm_apply, h]

variable {κ : Type u} [Fintype κ]

omit [IsDomain O] in
/-- An integral change of chart is compatible with the integral cocycle coefficients. -/
theorem isCompatible_of_isChartChange (C' : IntegralChart O K L κ) (M : ι → κ → O) (t : O)
    (h : C.data.IsChartChange C'.data (fun i l => algebraMap O K (M i l)) (algebraMap O K t)) :
    IsCompatible C.coeff C'.coeff M t := by
  intro i j
  apply IsFractionRing.injective O K
  have := h.isCompatible i j
  simpa [map_sum, map_mul, C.algebraMap_coeff, C'.algebraMap_coeff] using this

/-- **Change of chart.** An integral change of chart `(M, t)` from `C` to `C'` gives the model
homomorphism `(a, b) ↦ (M a, t b)`, compatible with the identity of `U_{L/K}`. -/
def chartHom (C' : IntegralChart O K L κ) (M : ι → κ → O) (t : O)
    (h : C.data.IsChartChange C'.data (fun i l => algebraMap O K (M i l)) (algebraMap O K t)) :
    C.model.Hom C'.model (𝟙 _) where
  hom := BilinearCoordinate.linearHom (CommRingCat.of O) M t
    (C.isCompatible_of_isChartChange C' M t h)
  generic_comm := by
    apply hom_ext_points
    intro T x
    apply (unitaryPointsEquiv K L T).injective
    change unitaryPointsEquiv K L T ((x ≫ ((baseChange (Spec.algebraMap O K)).map
        (BilinearCoordinate.linearHom (CommRingCat.of O) M t
          (C.isCompatible_of_isChartChange C' M t h))).hom.hom) ≫
          C'.model.genericIso.hom.hom.hom) =
      unitaryPointsEquiv K L T (x ≫ C.model.genericIso.hom.hom.hom)
    rw [unitaryPointsEquiv_genericIso, unitaryPointsEquiv_genericIso, genericPointsEquiv_apply,
      genericPointsEquiv_apply, GroupScheme.baseChangePointsEquiv_comp,
      BilinearCoordinate.pointsEquiv_linearHom, ← h.toParameters_linearMap]
    congr 1
    apply Coordinates.ext
    · funext l
      change ∑ i, _ * algebraMap O (restrictedSections (O := O) T) (M i l) =
        ∑ i, _ * algebraMap K (restrictedSections (O := O) T) (algebraMap O K (M i l))
      simp only [algebraMap_restrictedSections]
      rfl
    · change algebraMap O (restrictedSections (O := O) T) t * _ =
        algebraMap K (restrictedSections (O := O) T) (algebraMap O K t) * _
      rw [algebraMap_restrictedSections]
      rfl

/-- On integral points, a change of chart acts by `(a, b) ↦ (M a, t b)`. -/
theorem integralCoordinatesEquiv_chartHom (C' : IntegralChart O K L κ) (M : ι → κ → O) (t : O)
    (h : C.data.IsChartChange C'.data (fun i l => algebraMap O K (M i l)) (algebraMap O K t))
    (x : C.model.integralSections) :
    C'.integralCoordinatesEquiv (rationalPoints.map (C.chartHom C' M t h).hom x) =
      Coordinates.linearMap M t (C.isCompatible_of_isChartChange C' M t h)
        (C.integralCoordinatesEquiv x) := by
  have key : BilinearCoordinate.pointsEquiv (CommRingCat.of O) C'.coeff (Over.mk (𝟙 _))
      (rationalPoints.map (C.chartHom C' M t h).hom x) =
      Coordinates.linearMap (fun i l => algebraMap (CommRingCat.of O) _ (M i l))
        (algebraMap (CommRingCat.of O) _ t)
        ((C.isCompatible_of_isChartChange C' M t h).map (algebraMap (CommRingCat.of O) _))
        (BilinearCoordinate.pointsEquiv (CommRingCat.of O) C.coeff (Over.mk (𝟙 _)) x) :=
    BilinearCoordinate.pointsEquiv_linearHom (CommRingCat.of O) M t _ x
  apply Coordinates.ext
  · funext l
    rw [vec_integralCoordinatesEquiv, key, Coordinates.vec_linearMap, Coordinates.vec_linearMap]
    simp only [matrixVec, map_sum, map_mul, vec_integralCoordinatesEquiv, AlgEquiv.commutes]
    rfl
  · rw [scalar_integralCoordinatesEquiv, key, Coordinates.scalar_linearMap,
      Coordinates.scalar_linearMap, map_mul, AlgEquiv.commutes, scalar_integralCoordinatesEquiv]
    rfl

end IntegralChart

end IntegralChartPoints

end Langlands.GroupScheme.SU3Root
