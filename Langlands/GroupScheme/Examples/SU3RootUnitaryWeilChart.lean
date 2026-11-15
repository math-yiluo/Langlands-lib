import Langlands.Geometry.Building.MultipliableRootGroupCoordinates
import Langlands.GroupScheme.AffineWeilBilinear
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Basis coordinates on the Weil restriction of the unitary parameter group

For a finite extension `E / K` with a `K`-basis `b` of `E` and a separable quadratic extension
`L / E`, the points of `W = R_{E/K} U_{L/E}` over a test scheme `T` with global functions `A`
are the bilinear coordinates `(a, z)` of the canonical chart of `U_{L/E}` over `E ⊗[K] A`.
Expanding them in the basis `b` gives basis components `a : I × Fin n → A` and
`z : Fin n → A`. In these components the group law is
`(a, z) (a', z') = (a + a', z + z' + weilForm a a')` for an `A`-bilinear form `weilForm`, natural
in `A`. The rational point of `W` attached to a parameter `p` of `U_{L/E}(E)` has as components
the images in the global functions of the basis components of the chart coordinates of `p`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root.WeilChart

open BilinearCoordinate

/-! ### Basis components over a coefficient algebra -/

section Components

variable {K E : Type u} [Field K] [Field E] [Algebra K E] {n : ℕ}
  (b : Module.Basis (Fin n) K E) {I : Type u} [Fintype I] (c : I → I → E)
  (A : Type u) [CommRing A] [Algebra K A]

/-- The cocycle coefficients of the chart in `E ⊗[K] A`. -/
abbrev tensorCoeffs : I → I → E ⊗[K] A := fun i j => algebraMap E (E ⊗[K] A) (c i j)

/-- The vector of `E ⊗[K] A` with basis components `a`: `i ↦ ∑ⱼ bⱼ ⊗ a(i, j)`. -/
def basisVec (a : I × Fin n → A) : I → E ⊗[K] A :=
  fun i => AffineWeil.tensorCoordinateEquiv b A (fun j => a (i, j))

/-- The basis components of a vector of `E ⊗[K] A`. -/
def vecComponents (v : I → E ⊗[K] A) : I × Fin n → A :=
  fun p => (AffineWeil.tensorCoordinateEquiv b A).symm (v p.1) p.2

omit [Fintype I] in
@[simp] theorem basisVec_vecComponents (v : I → E ⊗[K] A) :
    basisVec b A (vecComponents b A v) = v := by
  funext i
  exact (AffineWeil.tensorCoordinateEquiv b A).apply_symm_apply (v i)

omit [Fintype I] in
@[simp] theorem vecComponents_basisVec (a : I × Fin n → A) :
    vecComponents b A (basisVec b A a) = a := by
  funext p
  simp only [vecComponents, basisVec, AddEquiv.symm_apply_apply]

/-- The cocycle of the Weil restriction, in basis components. -/
def weilForm (a a' : I × Fin n → A) : Fin n → A :=
  (AffineWeil.tensorCoordinateEquiv b A).symm
    (form (tensorCoeffs (K := K) c A) (basisVec b A a) (basisVec b A a'))

/-- The basis components `(a, z)` of bilinear coordinates over `E ⊗[K] A`. -/
def components : Coordinates (tensorCoeffs (K := K) c A) ≃ (I × Fin n → A) × (Fin n → A) where
  toFun x := (vecComponents b A x.vec, (AffineWeil.tensorCoordinateEquiv b A).symm x.scalar)
  invFun x := ⟨basisVec b A x.1, AffineWeil.tensorCoordinateEquiv b A x.2⟩
  left_inv x := by
    apply Coordinates.ext
    · exact basisVec_vecComponents b A x.vec
    · exact (AffineWeil.tensorCoordinateEquiv b A).apply_symm_apply x.scalar
  right_inv x := by
    ext1
    · exact vecComponents_basisVec b A x.1
    · exact (AffineWeil.tensorCoordinateEquiv b A).symm_apply_apply x.2

theorem components_mul_fst (x y : Coordinates (tensorCoeffs (K := K) c A)) :
    (components b c A (x * y)).1 = (components b c A x).1 + (components b c A y).1 := by
  funext p
  simp only [components, Equiv.coe_fn_mk, Coordinates.vec_mul, vecComponents, Pi.add_apply,
    map_add]

theorem components_mul_snd (x y : Coordinates (tensorCoeffs (K := K) c A)) :
    (components b c A (x * y)).2 = (components b c A x).2 + (components b c A y).2 +
      weilForm b c A (components b c A x).1 (components b c A y).1 := by
  simp only [components, Equiv.coe_fn_mk, Coordinates.scalar_mul, map_add, weilForm,
    basisVec_vecComponents]

omit [Fintype I] in
theorem components_one : components b c A 1 = (0, 0) := by
  ext1
  · funext p
    simp [components, vecComponents]
  · simp [components]

/-! #### Naturality -/

variable {A} {A' : Type u} [CommRing A'] [Algebra K A']

omit [Fintype I] in
theorem basisVec_map (f : A →ₐ[K] A') (a : I × Fin n → A) :
    basisVec b A' (fun p => f (a p)) =
      fun i => Algebra.TensorProduct.lTensor (S := E) E f (basisVec b A a i) := by
  funext i
  exact (AffineWeil.lTensor_tensorCoordinateEquiv b f _).symm

theorem form_lTensor (f : A →ₐ[K] A') (v v' : I → E ⊗[K] A) :
    form (tensorCoeffs (K := K) c A') (fun i => Algebra.TensorProduct.lTensor (S := E) E f (v i))
        (fun i => Algebra.TensorProduct.lTensor (S := E) E f (v' i)) =
      Algebra.TensorProduct.lTensor (S := E) E f (form (tensorCoeffs (K := K) c A) v v') := by
  simp only [form, map_sum, map_mul, AlgHom.commutes]

theorem weilForm_map (f : A →ₐ[K] A') (a a' : I × Fin n → A) :
    weilForm b c A' (fun p => f (a p)) (fun p => f (a' p)) =
      fun l => f (weilForm b c A a a' l) := by
  rw [weilForm, basisVec_map, basisVec_map, form_lTensor,
    AffineWeil.tensorCoordinateEquiv_symm_lTensor]
  rfl

theorem components_map (f : A →ₐ[K] A') (x : Coordinates (tensorCoeffs (K := K) c A)) :
    components b c A' (Coordinates.map (Algebra.TensorProduct.lTensor (S := E) E f).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := E) E f).commutes (c i j)) x) =
      ((fun p => f ((components b c A x).1 p)), (fun l => f ((components b c A x).2 l))) := by
  ext1
  · funext p
    change (AffineWeil.tensorCoordinateEquiv b A').symm
        (Algebra.TensorProduct.lTensor (S := E) E f (x.vec p.1)) p.2 = _
    rw [AffineWeil.tensorCoordinateEquiv_symm_lTensor]
    rfl
  · change (AffineWeil.tensorCoordinateEquiv b A').symm
        (Algebra.TensorProduct.lTensor (S := E) E f x.scalar) = _
    rw [AffineWeil.tensorCoordinateEquiv_symm_lTensor]
    rfl

/-! #### Bilinearity -/

variable (A)

theorem tensorCoordinateEquiv_smul (r : A) (x : Fin n → A) :
    AffineWeil.tensorCoordinateEquiv b A (r • x) =
      ((1 : E) ⊗ₜ[K] r) * AffineWeil.tensorCoordinateEquiv b A x := by
  rw [AffineWeil.tensorCoordinateEquiv_apply, AffineWeil.tensorCoordinateEquiv_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, smul_eq_mul]

theorem tensorCoordinateEquiv_symm_smul (r : A) (y : E ⊗[K] A) :
    (AffineWeil.tensorCoordinateEquiv b A).symm (((1 : E) ⊗ₜ[K] r) * y) =
      r • (AffineWeil.tensorCoordinateEquiv b A).symm y := by
  apply (AffineWeil.tensorCoordinateEquiv b A).injective
  rw [AddEquiv.apply_symm_apply, tensorCoordinateEquiv_smul, AddEquiv.apply_symm_apply]

omit [Fintype I] in
theorem basisVec_add (a a' : I × Fin n → A) :
    basisVec b A (a + a') = basisVec b A a + basisVec b A a' := by
  funext i
  simp only [basisVec, Pi.add_apply, ← map_add]
  rfl

omit [Fintype I] in
theorem basisVec_smul (r : A) (a : I × Fin n → A) :
    basisVec b A (r • a) = fun i => ((1 : E) ⊗ₜ[K] r) * basisVec b A a i := by
  funext i
  rw [basisVec, basisVec, ← tensorCoordinateEquiv_smul]
  rfl

theorem weilForm_add_left (a a' a'' : I × Fin n → A) :
    weilForm b c A (a + a') a'' = weilForm b c A a a'' + weilForm b c A a' a'' := by
  rw [weilForm, basisVec_add, form_add_left, map_add]
  rfl

theorem weilForm_add_right (a a' a'' : I × Fin n → A) :
    weilForm b c A a (a' + a'') = weilForm b c A a a' + weilForm b c A a a'' := by
  rw [weilForm, basisVec_add, form_add_right, map_add]
  rfl

theorem weilForm_smul_left (r : A) (a a' : I × Fin n → A) :
    weilForm b c A (r • a) a' = r • weilForm b c A a a' := by
  rw [weilForm, weilForm, basisVec_smul, ← tensorCoordinateEquiv_symm_smul]
  congr 1
  simp only [form, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem weilForm_smul_right (r : A) (a a' : I × Fin n → A) :
    weilForm b c A a (r • a') = r • weilForm b c A a a' := by
  rw [weilForm, weilForm, basisVec_smul, ← tensorCoordinateEquiv_symm_smul]
  congr 1
  simp only [form, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Basis components of a pure tensor `e ⊗ 1`. -/
theorem tensorCoordinateEquiv_symm_algebraMap (x : E) :
    (AffineWeil.tensorCoordinateEquiv b A).symm (algebraMap E (E ⊗[K] A) x) =
      fun j => algebraMap K A (b.repr x j) := by
  apply (AffineWeil.tensorCoordinateEquiv b A).injective
  rw [AddEquiv.apply_symm_apply, AffineWeil.tensorCoordinateEquiv_apply]
  change x ⊗ₜ[K] (1 : A) = _
  conv_lhs => rw [← b.sum_repr x]
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end Components

/-! ### Points of the Weil restriction over every test scheme -/

section Scheme

variable (K E L : Type u) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L]
  [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] [FiniteDimensional K E]

/-- The Weil restriction `W = R_{E/K} U_{L/E}` of the unitary parameter group. -/
abbrev weilGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  AffineWeil.groupScheme K E (unitaryParameterGroup E L)

/-- The relative global sections of a test scheme, as a `K`-algebra. -/
abbrev sections (T : Over (Spec (CommRingCat.of K))) : CommAlgCat.{u} (CommRingCat.of K) :=
  ((algΓ (CommRingCat.of K)).obj T).unop

/-- The canonical chart of `U_{L/E}`. -/
abbrev chartData : CoordinateData E L (ULift.{u} (Fin 2)) := canonicalCoordinateData.{u, u, u} E L

/-- Points of `W` over a test scheme are points of `U_{L/E}` over `E ⊗[K] A`. -/
def weilPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (weilGroup K E L).X) ≃*
      (unitaryParameterGroup E L).affinePoints ((AffineWeil.tensorFunctor K E).obj (sections K T)) :=
  Corepresented.pointsEquiv (AffineWeil.pointFunctor K E (unitaryParameterGroup E L))
    (AffineWeil.corepresentableBy K E (unitaryParameterGroup E L)) T

/-- Points of `U_{L/E}` over an `E`-algebra `S` are the quadratic root parameters over `S`:
the published point identification on the affine test scheme `Spec S`, followed by the
identification of its relative global sections with `S`. -/
def unitaryAffinePointsEquiv (S : CommAlgCat.{u} (CommRingCat.of E)) :
    (unitaryParameterGroup E L).affinePoints S ≃* tensorParameters E L S :=
  (unitaryPointsEquiv E L ((algSpec (CommRingCat.of E)).obj (op S))).trans
    (tensorParametersCongr E L (Corepresented.affineSectionsAlgEquiv S))

theorem tensorParametersCongr_apply {S S' : Type u} [CommRing S] [CommRing S'] [Algebra E S]
    [Algebra E S'] (e : S ≃ₐ[E] S') (p : tensorParameters E L S) :
    tensorParametersCongr E L e p = tensorParametersMap E L e.toAlgHom p := by
  apply Parameters.ext <;> rfl

theorem unitaryAffinePointsEquiv_naturality {S S' : CommAlgCat.{u} (CommRingCat.of E)}
    (h : S ⟶ S') (w : (unitaryParameterGroup E L).affinePoints S) :
    unitaryAffinePointsEquiv E L S' ((algSpec (CommRingCat.of E)).map h.op ≫ w) =
      tensorParametersMap E L h.hom (unitaryAffinePointsEquiv E L S w) := by
  have hnat := Corepresented.affineSectionsIso_inv_naturality h
  have h2 : ((algΓ (CommRingCat.of E)).map ((algSpec (CommRingCat.of E)).map h.op)).unop ≫
      (Corepresented.affineSectionsIso S').hom =
        (Corepresented.affineSectionsIso S).hom ≫ h := by
    rw [← cancel_epi (Corepresented.affineSectionsIso S).inv, ← Category.assoc, hnat,
      Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  simp only [unitaryAffinePointsEquiv, MulEquiv.trans_apply, unitaryPointsEquiv_naturality,
    tensorParametersCongr_apply]
  rw [← MonoidHom.comp_apply, ← tensorParametersMap_comp, ← MonoidHom.comp_apply,
    ← tensorParametersMap_comp]
  exact congrArg (fun f => tensorParametersMap E L f _) (congrArg CommAlgCat.Hom.hom h2)

/-- Points of `W` over a test scheme are the quadratic root parameters over `E ⊗[K] A`, for the
relative global sections `A`. -/
def parametersEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (weilGroup K E L).X) ≃* tensorParameters E L (E ⊗[K] sections K T) :=
  (weilPointsEquiv K E L T).trans
    (unitaryAffinePointsEquiv E L ((AffineWeil.tensorFunctor K E).obj (sections K T)))

/-- Points of `W` over a test scheme in the bilinear coordinates of the canonical chart. -/
def coordinates (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (weilGroup K E L).X) ≃*
      Coordinates (tensorCoeffs (K := K) (chartData E L).coeff (sections K T)) :=
  (parametersEquiv K E L T).trans (toParameters (chartData E L) (E ⊗[K] sections K T)).symm

theorem parametersEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))} (f : T' ⟶ T)
    (x : T ⟶ (weilGroup K E L).X) :
    parametersEquiv K E L T' (f ≫ x) =
      tensorParametersMap E L (Algebra.TensorProduct.lTensor (S := E) E
        ((algΓ (CommRingCat.of K)).map f).unop.hom) (parametersEquiv K E L T x) := by
  have h := Corepresented.pointsEquiv_naturality
    (AffineWeil.pointFunctor K E (unitaryParameterGroup E L))
    (AffineWeil.corepresentableBy K E (unitaryParameterGroup E L)) f x
  change unitaryAffinePointsEquiv E L _ (weilPointsEquiv K E L T' (f ≫ x)) = _
  refine (congrArg (unitaryAffinePointsEquiv E L _) h).trans ?_
  exact unitaryAffinePointsEquiv_naturality E L
    ((AffineWeil.tensorFunctor K E).map ((algΓ (CommRingCat.of K)).map f).unop) _

theorem coordinates_naturality {T T' : Over (Spec (CommRingCat.of K))} (f : T' ⟶ T)
    (x : T ⟶ (weilGroup K E L).X) :
    coordinates K E L T' (f ≫ x) =
      Coordinates.map (Algebra.TensorProduct.lTensor (S := E) E
          ((algΓ (CommRingCat.of K)).map f).unop.hom).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := E) E
          ((algΓ (CommRingCat.of K)).map f).unop.hom).commutes ((chartData E L).coeff i j))
        (coordinates K E L T x) := by
  apply (toParameters (chartData E L) (E ⊗[K] sections K T')).injective
  rw [toParameters_naturality]
  simp only [coordinates, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  exact parametersEquiv_naturality K E L f x

end Scheme

/-! ### Basis components of points -/

section SchemeComponents

variable {K E : Type u} (L : Type u) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L]
  [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] [FiniteDimensional K E]
  {n : ℕ} (b : Module.Basis (Fin n) K E)

/-- The basis components `(a, z)` of a point of `W` over a test scheme. -/
def pointComponents (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (weilGroup K E L).X) :
    (ULift.{u} (Fin 2) × Fin n → sections K T) × (Fin n → sections K T) :=
  components b (chartData E L).coeff (sections K T) (coordinates K E L T x)

/-- The point of `W` with basis components `(a, z)`. -/
def componentPoint (T : Over (Spec (CommRingCat.of K)))
    (az : (ULift.{u} (Fin 2) × Fin n → sections K T) × (Fin n → sections K T)) :
    T ⟶ (weilGroup K E L).X :=
  (coordinates K E L T).symm ((components b (chartData E L).coeff (sections K T)).symm az)

@[simp] theorem pointComponents_componentPoint (T : Over (Spec (CommRingCat.of K)))
    (az : (ULift.{u} (Fin 2) × Fin n → sections K T) × (Fin n → sections K T)) :
    pointComponents L b T (componentPoint L b T az) = az := by
  rw [pointComponents, componentPoint, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] theorem componentPoint_pointComponents (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (weilGroup K E L).X) :
    componentPoint L b T (pointComponents L b T x) = x := by
  rw [pointComponents, componentPoint, Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem pointComponents_mul_fst (T : Over (Spec (CommRingCat.of K)))
    (x y : T ⟶ (weilGroup K E L).X) :
    (pointComponents L b T (x * y)).1 =
      (pointComponents L b T x).1 + (pointComponents L b T y).1 := by
  rw [pointComponents, map_mul]
  exact components_mul_fst b _ _ _ _

theorem pointComponents_mul_snd (T : Over (Spec (CommRingCat.of K)))
    (x y : T ⟶ (weilGroup K E L).X) :
    (pointComponents L b T (x * y)).2 =
      (pointComponents L b T x).2 + (pointComponents L b T y).2 +
        weilForm b (chartData E L).coeff (sections K T)
          (pointComponents L b T x).1 (pointComponents L b T y).1 := by
  rw [pointComponents, map_mul]
  exact components_mul_snd b _ _ _ _

theorem pointComponents_one (T : Over (Spec (CommRingCat.of K))) :
    pointComponents L b T 1 = (0, 0) := by
  rw [pointComponents, map_one]
  exact components_one b _ _

theorem pointComponents_naturality {T T' : Over (Spec (CommRingCat.of K))} (f : T' ⟶ T)
    (x : T ⟶ (weilGroup K E L).X) :
    pointComponents L b T' (f ≫ x) =
      ((fun p => f.left.appTop ((pointComponents L b T x).1 p)),
        (fun l => f.left.appTop ((pointComponents L b T x).2 l))) := by
  rw [pointComponents, coordinates_naturality]
  exact components_map b _ ((algΓ (CommRingCat.of K)).map f).unop.hom _

end SchemeComponents

/-! ### Rational points -/

section Rational

open Langlands.AlgebraicGeometry.PointTopology

variable (K E L : Type u) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L]
  [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] [FiniteDimensional K E]

/-- The identity test scheme over `Spec K`, whose points are the rational points. -/
abbrev baseTest : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 (Spec (CommRingCat.of K)))

/-- Inserting the composite of two isomorphisms and its inverse. -/
theorem comp_eq_comp_iso {C : Type*} [Category C] {A B B' Q P D : C} (m : A ⟶ B)
    (m' : B ⟶ B') (z : B' ⟶ D) (Mi : Q ≅ B') (R : Q ≅ P) :
    m ≫ m' ≫ z = ((m ≫ m') ≫ Mi.inv ≫ R.hom) ≫ R.inv ≫ Mi.hom ≫ z := by
  simp

/-- On a rational point of `W`, the Weil point over `E ⊗[K] K` factors through the
corresponding rational point of `U_{L/E}`. -/
theorem weilPointsEquiv_rational (x : rationalPoints (weilGroup K E L)) :
    ∃ g : (algSpec (CommRingCat.of E)).obj
        (op ((AffineWeil.tensorFunctor K E).obj (sections K (baseTest K)))) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of E))),
      weilPointsEquiv K E L (baseTest K) x =
        g ≫ AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L) x := by
  let F := AffineWeil.pointFunctor K E (unitaryParameterGroup E L)
  let c := AffineWeil.corepresentableBy K E (unitaryParameterGroup E L)
  let x' := AffineWeil.sectionsCoeffEquiv K (weilGroup K E L) x
  let z := Corepresented.affinePointsEquiv F c (CommAlgCat.of (CommRingCat.of K) K) x'
  let Mi := (algSpec (CommRingCat.of E)).mapIso
    (CommAlgCat.isoMk (Algebra.TensorProduct.rid K E E)).op
  have hy : AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L) x =
      (ringTestSelfIso E).inv ≫ Mi.hom ≫ z := rfl
  have hx : x = (ringTestSelfIso K).inv ≫ x' := by
    change x = (ringTestSelfIso K).inv ≫ (ringTestSelfIso K).hom ≫ x
    rw [Iso.inv_hom_id_assoc]
  have h1 := Corepresented.pointsEquiv_naturality F c (ringTestSelfIso K).inv x'
  have h2 := Corepresented.pointsEquiv_eq_affinePointsEquiv F c
    (CommAlgCat.of (CommRingCat.of K) K) x'
  let g1 := ((algΓ (CommRingCat.of K)).map (ringTestSelfIso K).inv).unop
  let g2 := (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of K) K)).inv
  let mA := (algSpec (CommRingCat.of E)).map ((AffineWeil.tensorFunctor K E).map g1).op
  let mB := (algSpec (CommRingCat.of E)).map ((AffineWeil.tensorFunctor K E).map g2).op
  have hm : weilPointsEquiv K E L (baseTest K) x = mA ≫ mB ≫ z := by
    change Corepresented.pointsEquiv F c (baseTest K) x = _
    conv_lhs => rw [hx]
    exact h1.trans (congrArg (ConcreteCategory.hom (F.map g1)) h2)
  refine ⟨(mA ≫ mB) ≫ Mi.inv ≫ (ringTestSelfIso E).hom, ?_⟩
  rw [hm, hy]
  exact comp_eq_comp_iso mA mB z Mi (ringTestSelfIso E)

/-- The Weil-restriction parameters of a rational point of `W` are the field parameters of the
corresponding rational point of `U_{L/E}`, extended along `E → E ⊗[K] K`. -/
theorem parametersEquiv_rational (x : rationalPoints (weilGroup K E L)) :
    parametersEquiv K E L (baseTest K) x =
      tensorParametersMap E L (Algebra.ofId E (E ⊗[K] sections K (baseTest K)))
        ((rationalParametersEquiv E L).symm (unitaryRationalPointsEquiv E L
          (AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L) x))) := by
  obtain ⟨g, hg⟩ := weilPointsEquiv_rational K E L x
  change unitaryAffinePointsEquiv E L _ (weilPointsEquiv K E L (baseTest K) x) = _
  rw [hg]
  simp only [unitaryAffinePointsEquiv, unitaryRationalPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, unitaryPointsEquiv_naturality, tensorParametersCongr_apply]
  rw [← MonoidHom.comp_apply, ← tensorParametersMap_comp, ← MonoidHom.comp_apply,
    ← tensorParametersMap_comp]
  congr 1
  refine congrArg (tensorParametersMap E L) ?_
  apply AlgHom.ext
  intro y
  obtain ⟨r, rfl⟩ : ∃ r : E, algebraMap E _ r = y :=
    ⟨identitySectionsEquiv (CommRingCat.of E) y,
      (identitySectionsEquiv (CommRingCat.of E)).injective (by
        rw [AlgEquiv.commutes]; rfl)⟩
  rw [AlgHom.commutes]
  change _ = Algebra.ofId E (E ⊗[K] sections K (baseTest K))
    (identitySectionsEquiv (CommRingCat.of E) (algebraMap E _ r))
  rw [AlgEquiv.commutes]
  rfl

/-- The chart coordinates of a rational point of `W`. -/
theorem coordinates_rational (x : rationalPoints (weilGroup K E L)) :
    coordinates K E L (baseTest K) x =
      Coordinates.map (Algebra.ofId E (E ⊗[K] sections K (baseTest K))).toRingHom
        (fun i j => (Algebra.ofId E (E ⊗[K] sections K (baseTest K))).commutes
          ((chartData E L).coeff i j))
        ((toParameters (chartData E L) E).symm ((rationalParametersEquiv E L).symm
          (unitaryRationalPointsEquiv E L
            (AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L) x)))) := by
  apply (toParameters (chartData E L) (E ⊗[K] sections K (baseTest K))).injective
  rw [toParameters_naturality]
  simp only [coordinates, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  exact parametersEquiv_rational K E L x

variable {K E} {n : ℕ} (b : Module.Basis (Fin n) K E)

/-- The rational point of `W` attached to a field parameter of `U_{L/E}`. -/
def rationalPoint (p : rationalParameters E L) : rationalPoints (weilGroup K E L) :=
  (AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L)).symm
    ((unitaryRationalPointsEquiv E L).symm p)

/-- The chart coordinates over `E` of a field parameter. -/
def rationalCoordinates (p : rationalParameters E L) :
    Coordinates (coeffs (chartData E L) E) :=
  (toParameters (chartData E L) E).symm ((rationalParametersEquiv E L).symm p)

/-- The basis components of the chart coordinates of a field parameter. -/
def rationalComponents (p : rationalParameters E L) :
    (ULift.{u} (Fin 2) × Fin n → K) × (Fin n → K) :=
  (fun q => b.repr ((rationalCoordinates L p).vec q.1) q.2,
    fun j => b.repr (rationalCoordinates L p).scalar j)

/-- **Components of rational points.** The basis components of the rational point attached to
a field parameter are the images of the basis components of its chart coordinates. -/
theorem pointComponents_rationalPoint (p : rationalParameters E L) :
    pointComponents L b (baseTest K) (rationalPoint L p) =
      ((fun q => algebraMap K (sections K (baseTest K)) ((rationalComponents L b p).1 q)),
        fun j => algebraMap K (sections K (baseTest K)) ((rationalComponents L b p).2 j)) := by
  rw [pointComponents, rationalPoint, coordinates_rational, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  ext1
  · funext q
    simp only [components, Equiv.coe_fn_mk, vecComponents, Coordinates.vec_map]
    exact congrFun (tensorCoordinateEquiv_symm_algebraMap b (sections K (baseTest K))
      ((rationalCoordinates L p).vec q.1)) q.2
  · funext j
    simp only [components, Equiv.coe_fn_mk, Coordinates.scalar_map]
    exact congrFun (tensorCoordinateEquiv_symm_algebraMap b (sections K (baseTest K))
      (rationalCoordinates L p).scalar) j

/-- The first coordinate of a field parameter is the image of its chart vector. -/
theorem lid_tensorVec_rationalCoordinates (p : rationalParameters E L) :
    Algebra.TensorProduct.lid E L (tensorVec (chartData E L) E (rationalCoordinates L p).vec) =
      p.first := by
  have hc : toParameters (chartData E L) E (rationalCoordinates L p) =
      (rationalParametersEquiv E L).symm p :=
    MulEquiv.apply_symm_apply _ _
  have h := congrArg (fun q => (rationalParametersEquiv E L q).first) hc
  simp only [MulEquiv.apply_symm_apply] at h
  exact h

/-- The first coordinate of a field parameter in its chart coordinates. -/
theorem first_eq_rationalCoordinates (p : rationalParameters E L) :
    p.first = ∑ i, (rationalCoordinates L p).vec i • (chartData E L).basis i := by
  rw [← lid_tensorVec_rationalCoordinates L p]
  simp only [tensorVec, map_sum, Algebra.TensorProduct.lid_tmul]

/-- The second coordinate of a field parameter in its chart coordinates. -/
theorem second_eq_rationalCoordinates (p : rationalParameters E L) :
    p.second = (rationalCoordinates L p).scalar • (chartData E L).center +
      (chartData E L).traceOne * p.first * conjugation E L p.first := by
  have hc : toParameters (chartData E L) E (rationalCoordinates L p) =
      (rationalParametersEquiv E L).symm p :=
    MulEquiv.apply_symm_apply _ _
  have hsecond : Algebra.TensorProduct.lid E L
      (toParameters (chartData E L) E (rationalCoordinates L p)).second = p.second := by
    rw [hc]
    exact congrArg Parameters.second (MulEquiv.apply_symm_apply (rationalParametersEquiv E L) p)
  rw [← hsecond, second_toParameters, map_add, map_mul, map_mul, Algebra.TensorProduct.lid_tmul,
    Algebra.TensorProduct.lid_tmul, one_smul, rationalTensor_bar,
    lid_tensorVec_rationalCoordinates, fieldInvolution_bar]

end Rational

end Langlands.GroupScheme.SU3Root.WeilChart
