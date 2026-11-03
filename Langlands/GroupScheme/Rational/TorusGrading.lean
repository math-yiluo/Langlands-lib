import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Character gradings of corepresented groups with split-torus actions -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

open splitTorus (exponentValue exponentValue_single)

variable {R : CommRingCat.{u}}

section Monomials

variable (I : Type u) [Fintype I] [DecidableEq I] (A : Type u) [CommRing A]

/-- The unit monomial of an exponent vector in the group algebra over `A`. -/
abbrev monomialUnit (m : I → ℤ) : (AddMonoidAlgebra A (I → ℤ))ˣ :=
  splitTorus.exponentUnit (R := CommRingCat.of A) I m

/-- The independent invertible monomials of the coordinate vectors. -/
def universalUnits : I → (AddMonoidAlgebra A (I → ℤ))ˣ :=
  fun i => monomialUnit I A (Pi.single i 1)

theorem exponentValue_universalUnits (m : I → ℤ) :
    exponentValue I (universalUnits I A) (Multiplicative.ofAdd m) = monomialUnit I A m := by
  change ∏ i, universalUnits I A i ^ m i = _
  simp only [universalUnits, monomialUnit, splitTorus.exponentUnit, ← map_zpow, ← map_prod, ← ofAdd_zsmul,
    ← ofAdd_sum]
  congr 2
  ext j
  simp [Pi.single_apply]

end Monomials

section Action

variable (F : CommAlgCat.{u} R ⥤ GrpCat.{u}) (I : Type u)

/-- An action of the split torus with unit coordinates indexed by `I` on a group-valued
functor of algebras, by group automorphisms and naturally in the algebra. -/
structure TorusAction where
  /-- The action of a family of units on points. -/
  act : ∀ {A : CommAlgCat.{u} R}, (I → Aˣ) → F.obj A → F.obj A
  act_one : ∀ {A : CommAlgCat.{u} R} (x : F.obj A), act 1 x = x
  act_mul : ∀ {A : CommAlgCat.{u} R} (t t' : I → Aˣ) (x : F.obj A),
    act (t * t') x = act t (act t' x)
  act_map_mul : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ) (x y : F.obj A),
    act t (x * y) = act t x * act t y
  naturality : ∀ {A A' : CommAlgCat.{u} R} (g : A ⟶ A') (t : I → Aˣ) (x : F.obj A),
    F.map g (act t x) = act (fun i => Units.map g.hom.toMonoidHom (t i)) (F.map g x)

end Action

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Coordinates

/-- The classifying algebra map of a point. -/
abbrev coord {A : CommAlgCat.{u} R} (x : F.obj A) : B →ₐ[R] A := (e.homEquiv.symm x).hom

/-- The point classified by an algebra map. -/
abbrev ofCoord {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) : F.obj A :=
  AffineLinearEmbedding.pt e f

@[simp] theorem coord_ofCoord {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) :
    coord e (ofCoord e f) = f := by
  simp [coord, ofCoord, AffineLinearEmbedding.pt]

@[simp] theorem ofCoord_coord {A : CommAlgCat.{u} R} (x : F.obj A) :
    ofCoord e (coord e x) = x := by
  simp [coord, ofCoord, AffineLinearEmbedding.pt]

theorem coord_injective {A : CommAlgCat.{u} R} :
    Function.Injective (coord e : F.obj A → (B →ₐ[R] A)) := by
  intro x y h
  rw [← ofCoord_coord e x, h, ofCoord_coord]

theorem coord_map {A A' : CommAlgCat.{u} R} (g : A ⟶ A') (x : F.obj A) :
    coord e (F.map g x) = g.hom.comp (coord e x) := by
  exact AffineLinearEmbedding.homEquiv_symm_map e g x

theorem coord_one {A : CommAlgCat.{u} R} :
    coord e (1 : F.obj A) = (Algebra.ofId R A).comp (AffineLinearEmbedding.counit e) := by
  exact AffineLinearEmbedding.homEquiv_symm_one e A

end Coordinates

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

section Grading

variable (I) in
/-- The group algebra of the exponent lattice over an algebra. -/
abbrev laurent (A : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (AddMonoidAlgebra A (I → ℤ))

variable (I) in
/-- Constant coefficients. -/
abbrev constHom (A : CommAlgCat.{u} R) : A ⟶ laurent I A :=
  CommAlgCat.ofHom AddMonoidAlgebra.singleZeroAlgHom

variable (I) in
/-- Evaluation of the exponent monomials at a family of units, with coefficients
mapped by an algebra map. -/
def evalHom {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) (t : I → Aˣ) :
    AddMonoidAlgebra B (I → ℤ) →ₐ[R] A :=
  AddMonoidAlgebra.liftNCAlgHom f ((Units.coeHom A).comp (exponentValue I t))
    (fun _ _ => Commute.all _ _)

omit [DecidableEq I] in
theorem evalHom_single {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) (t : I → Aˣ)
    (m : I → ℤ) (b : B) :
    evalHom I f t (AddMonoidAlgebra.single m b) =
      f b * (exponentValue I t (Multiplicative.ofAdd m) : A) := by
  simp [evalHom]

/-- The point twisted by the universal family of units, over the group algebra. -/
def hat {A : CommAlgCat.{u} R} : F.obj A →* F.obj (laurent I A) where
  toFun x := σ.act (universalUnits I A) (F.map (constHom I A) x)
  map_one' := by
    rw [map_one]
    have h := σ.act_map_mul (A := laurent I A) (universalUnits I A) 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  map_mul' x y := by
    rw [map_mul, σ.act_map_mul]

/-- The universal point. -/
abbrev univ : F.obj B := e.homEquiv (𝟙 B)

/-- The coaction of the exponent lattice on the representing algebra. -/
def rho : B →ₐ[R] AddMonoidAlgebra B (I → ℤ) := coord e (hat σ (univ e))

theorem eq_map_univ {A : CommAlgCat.{u} R} (x : F.obj A) :
    x = F.map (e.homEquiv.symm x) (univ e) := by
  have h := e.homEquiv_comp (e.homEquiv.symm x) (𝟙 B)
  rw [Category.id_comp, Equiv.apply_symm_apply] at h
  exact h

/-- The fundamental formula: the action is evaluation of the coaction. -/
theorem coord_act {A : CommAlgCat.{u} R} (t : I → Aˣ) (x : F.obj A) :
    coord e (σ.act t x) = (evalHom I (coord e x) t).comp (rho e σ) := by
  let E : laurent I B ⟶ A := CommAlgCat.ofHom (evalHom I (coord e x) t)
  have hconst : constHom I B ≫ E = e.homEquiv.symm x := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    change evalHom I (coord e x) t (AddMonoidAlgebra.single 0 b) = coord e x b
    rw [evalHom_single]
    simp
  have hunits : (fun i => Units.map E.hom.toMonoidHom (universalUnits I B i)) = t := by
    funext i
    apply Units.ext
    change evalHom I (coord e x) t (AddMonoidAlgebra.single (Pi.single i 1) 1) = (t i : A)
    rw [evalHom_single, map_one, one_mul, exponentValue_single]
  have key : σ.act t x = F.map E (hat σ (univ e)) := by
    change σ.act t x = F.map E (σ.act (universalUnits I B) (F.map (constHom I B) (univ e)))
    rw [σ.naturality, hunits]
    congr 1
    rw [eq_map_univ e x]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hconst]
  rw [key, coord_map]
  rfl

omit [DecidableEq I] in
theorem evalHom_apply {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) (t : I → Aˣ)
    (p : AddMonoidAlgebra B (I → ℤ)) :
    evalHom I f t p = p.coeff.sum fun m b => f b * (exponentValue I t (Multiplicative.ofAdd m) : A) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro m
      simp
    · intro m b b'
      rw [map_add, add_mul]
  | single m b =>
    rw [evalHom_single, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
    simp

/-- Evaluation at the universal units, after mapping coefficients to constants, is
coefficientwise mapping. -/
theorem evalHom_const {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) (p : AddMonoidAlgebra B (I → ℤ)) :
    evalHom I ((constHom I A).hom.comp f) (universalUnits I A) p =
      AddMonoidAlgebra.mapAlgHom (I → ℤ) f p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | single m b =>
    rw [evalHom_single, exponentValue_universalUnits, AddMonoidAlgebra.mapAlgHom_single]
    change AddMonoidAlgebra.single 0 (f b) * AddMonoidAlgebra.single m 1 = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- The coordinates of the twisted point are the coaction followed by the coordinates,
coefficientwise. -/
theorem coord_hat {A : CommAlgCat.{u} R} (x : F.obj A) :
    coord e (hat σ x) = (AddMonoidAlgebra.mapAlgHom (I → ℤ) (coord e x)).comp (rho e σ) := by
  change coord e (σ.act (universalUnits I A) (F.map (constHom I A) x)) = _
  rw [coord_act, coord_map]
  exact AlgHom.ext fun f => evalHom_const (coord e x) _

/-- The weight-`m` component of a coordinate function. -/
def comp (m : I → ℤ) : B →ₗ[R] B :=
  (Finsupp.lapply m).comp
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp (rho e σ).toLinearMap)

omit [Fintype I] in
theorem comp_apply (m : I → ℤ) (f : B) : comp e σ m f = (rho e σ f).coeff m := rfl

theorem coord_hat_coeff {A : CommAlgCat.{u} R} (x : F.obj A) (f : B) (m : I → ℤ) :
    (coord e (hat σ x) f).coeff m = coord e x (comp e σ m f) := by
  rw [coord_hat, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom, comp_apply]

theorem coord_univ : coord e (univ e) = AlgHom.id R B := by
  simp [coord, univ]

/-- The coaction followed by summation of coefficients is the identity. -/
theorem sum_comp (f : B) : (rho e σ f).coeff.sum (fun _ b => b) = f := by
  have h := congrArg (fun g : B →ₐ[R] B => g f) (congrArg (coord e) (σ.act_one (univ e)))
  simp only [coord_act, coord_univ, AlgHom.comp_apply, evalHom_apply] at h
  simpa [exponentValue] using h

/-- The augmentation of a weight component. -/
theorem counit_comp (m : I → ℤ) (f : B) :
    AffineLinearEmbedding.counit e (comp e σ m f) = if m = 0 then AffineLinearEmbedding.counit e f else 0 := by
  have h := coord_hat_coeff e σ (1 : F.obj (CommAlgCat.of R R)) f m
  rw [map_one, coord_one] at h
  change _ = AffineLinearEmbedding.counit e (comp e σ m f) at h
  rw [← h]
  change (algebraMap R (AddMonoidAlgebra R (I → ℤ)) (AffineLinearEmbedding.counit e f)).coeff m = _
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  simp [eq_comm]

omit [DecidableEq I] in
theorem exponentValue_mul {A : Type u} [CommRing A] (t t' : I → Aˣ) (m : I → ℤ) :
    exponentValue I (t * t') (Multiplicative.ofAdd m) =
      exponentValue I t (Multiplicative.ofAdd m) * exponentValue I t' (Multiplicative.ofAdd m) := by
  simp only [exponentValue, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, mul_zpow,
    Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem exponentValue_map {A A' : Type u} [CommRing A] [CommRing A'] (g : A →* A')
    (t : I → Aˣ) (m : I → ℤ) :
    exponentValue I (fun i => Units.map g (t i)) (Multiplicative.ofAdd m) =
      Units.map g (exponentValue I t (Multiplicative.ofAdd m)) := by
  simp only [exponentValue, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow]

/-- Twisting twice by the universal units is the diagonal twist. -/
theorem coord_hat_hat {A : CommAlgCat.{u} R} (x : F.obj A) (f : B) :
    coord e (hat σ (hat σ x)) f = (rho e σ f).coeff.sum fun m b =>
      AddMonoidAlgebra.single m (AddMonoidAlgebra.single m (coord e x b)) := by
  have key : hat σ (hat σ x) = σ.act (universalUnits I (laurent I A) *
      fun i => Units.map (constHom I (laurent I A)).hom.toMonoidHom (universalUnits I A i))
      (F.map (constHom I A ≫ constHom I (laurent I A)) x) := by
    change σ.act _ (F.map _ (σ.act _ (F.map _ x))) = _
    rw [σ.naturality, σ.act_mul, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [key, coord_act, coord_map, AlgHom.comp_apply, evalHom_apply]
  refine Finsupp.sum_congr fun m _ => ?_
  rw [exponentValue_mul, exponentValue_universalUnits, exponentValue_map,
    exponentValue_universalUnits, Units.val_mul, Units.coe_map]
  change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 (coord e x _)) *
    (AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single m 1)) = _
  simp only [AddMonoidAlgebra.single_mul_single, zero_add, add_zero, one_mul, mul_one]

omit [DecidableEq I] in
theorem coeff_coeff_diag {C : Type u} [CommSemiring C] (p : (I → ℤ) →₀ C) (m n : I → ℤ) :
    (((p.sum fun m b => AddMonoidAlgebra.single m (AddMonoidAlgebra.single m b)).coeff m).coeff
      n) = if n = m then p m else 0 := by
  rw [AddMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply, AddMonoidAlgebra.coeff_finsuppSum,
    Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m]
  · by_cases h : n = m
    · subst h
      simp
    · simp [h]
  · intro i _ hi
    simp [hi]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm]
    simp

/-- Weight components are idempotent and orthogonal. -/
theorem comp_comp (m n : I → ℤ) (f : B) :
    comp e σ n (comp e σ m f) = if n = m then comp e σ m f else 0 := by
  have h1 : comp e σ n (comp e σ m f) =
      ((coord e (hat σ (hat σ (univ e))) f).coeff m).coeff n := by
    rw [coord_hat_coeff, coord_hat_coeff, coord_univ, AlgHom.id_apply]
  rw [h1, coord_hat_hat]
  simp only [coord_univ, AlgHom.id_apply]
  exact coeff_coeff_diag (rho e σ f).coeff m n

/-- An element of the representing algebra is homogeneous of weight `m`. -/
def IsHomogeneous (m : I → ℤ) (f : B) : Prop :=
  rho e σ f = AddMonoidAlgebra.single m f

theorem isHomogeneous_iff (m : I → ℤ) (f : B) :
    IsHomogeneous e σ m f ↔ ∀ n, comp e σ n f = if n = m then f else 0 := by
  constructor
  · intro h n
    rw [comp_apply, h, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = m
    · simp [hn]
    · simp [hn, Ne.symm hn]
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    ext n
    rw [← comp_apply, h, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = m
    · simp [hn]
    · simp [hn, Ne.symm hn]

theorem isHomogeneous_comp (m : I → ℤ) (f : B) : IsHomogeneous e σ m (comp e σ m f) :=
  (isHomogeneous_iff e σ m _).2 fun n => comp_comp e σ m n f

variable {e σ} in
theorem IsHomogeneous.comp_eq {m : I → ℤ} {f : B} (h : IsHomogeneous e σ m f) (n : I → ℤ) :
    comp e σ n f = if n = m then f else 0 :=
  (isHomogeneous_iff e σ m f).1 h n

variable {e σ} in
theorem IsHomogeneous.comp_self {m : I → ℤ} {f : B} (h : IsHomogeneous e σ m f) :
    comp e σ m f = f := by
  simpa using h.comp_eq m

omit [Fintype I] in
variable {e σ} in
theorem IsHomogeneous.mul {m n : I → ℤ} {f g : B} (hf : IsHomogeneous e σ m f)
    (hg : IsHomogeneous e σ n g) : IsHomogeneous e σ (m + n) (f * g) := by
  rw [IsHomogeneous, map_mul, hf, hg, AddMonoidAlgebra.single_mul_single]

omit [Fintype I] in
variable {e σ} in
theorem IsHomogeneous.add {m : I → ℤ} {f g : B} (hf : IsHomogeneous e σ m f)
    (hg : IsHomogeneous e σ m g) : IsHomogeneous e σ m (f + g) := by
  rw [IsHomogeneous, map_add, hf, hg, AddMonoidAlgebra.single_add]

omit [Fintype I] in
variable {e σ} in
theorem IsHomogeneous.smul {m : I → ℤ} {f : B} (hf : IsHomogeneous e σ m f) (r : R) :
    IsHomogeneous e σ m (r • f) := by
  rw [IsHomogeneous, map_smul, hf, AddMonoidAlgebra.smul_single]

omit [Fintype I] in
theorem isHomogeneous_zero (m : I → ℤ) : IsHomogeneous e σ m 0 := by
  rw [IsHomogeneous, map_zero, AddMonoidAlgebra.single_zero]

omit [Fintype I] in
theorem isHomogeneous_algebraMap (r : R) : IsHomogeneous e σ 0 (algebraMap R B r) := by
  rw [IsHomogeneous, AlgHom.commutes]
  rfl

variable {e σ} in
theorem IsHomogeneous.counit_eq_zero {m : I → ℤ} {f : B} (h : IsHomogeneous e σ m f)
    (hm : m ≠ 0) : AffineLinearEmbedding.counit e f = 0 := by
  rw [← h.comp_self, counit_comp]
  simp [hm]

/-- The coordinates of the twisted point at a homogeneous function. -/
theorem coord_hat_of_isHomogeneous {A : CommAlgCat.{u} R} (x : F.obj A) {m : I → ℤ} {f : B}
    (h : IsHomogeneous e σ m f) :
    coord e (hat σ x) f = AddMonoidAlgebra.single m (coord e x f) := by
  rw [coord_hat, AlgHom.comp_apply, h, AddMonoidAlgebra.mapAlgHom_single]

/-- The torus acts on a homogeneous coordinate through its weight. -/
theorem coord_act_of_isHomogeneous {A : CommAlgCat.{u} R} (t : I → Aˣ) (x : F.obj A)
    {m : I → ℤ} {f : B} (h : IsHomogeneous e σ m f) :
    coord e (σ.act t x) f = coord e x f * (exponentValue I t (Multiplicative.ofAdd m) : A) := by
  rw [coord_act, AlgHom.comp_apply, h, evalHom_single]

/-- The product formula: the weight components of a product. -/
theorem comp_mul (χ : I → ℤ) (f g : B) :
    comp e σ χ (f * g) = (rho e σ f).coeff.sum fun ψ b => (rho e σ g).coeff.sum fun ψ' b' =>
      if ψ + ψ' = χ then b * b' else 0 := by
  rw [comp_apply, map_mul, AddMonoidAlgebra.coeff_mul]

/-- The coordinate function is the sum of its weight components. -/
theorem sum_support_comp (f : B) : ∑ m ∈ (rho e σ f).coeff.support, comp e σ m f = f :=
  sum_comp e σ f

omit [Fintype I] in
theorem comp_eq_zero_of_notMem {m : I → ℤ} {f : B} (h : m ∉ (rho e σ f).coeff.support) :
    comp e σ m f = 0 :=
  Finsupp.notMem_support_iff.mp h

omit [Fintype I] in
/-- The submodule of homogeneous elements of a weight. -/
def homogeneousSubmodule (m : I → ℤ) : Submodule R B where
  carrier := {f | IsHomogeneous e σ m f}
  zero_mem' := isHomogeneous_zero e σ m
  add_mem' hf hg := hf.add hg
  smul_mem' r _ hf := hf.smul r

omit [Fintype I] in
theorem mem_homogeneousSubmodule (m : I → ℤ) (f : B) :
    f ∈ homogeneousSubmodule e σ m ↔ IsHomogeneous e σ m f := Iff.rfl

section Regrading

variable {ι : Type*} [AddMonoid ι] [DecidableEq ι] (φ : ι →+ (I → ℤ))

omit [Fintype I] in
instance gradedMonoid_homogeneousSubmodule :
    SetLike.GradedMonoid fun i => homogeneousSubmodule e σ (φ i) where
  one_mem := by
    change IsHomogeneous e σ (φ 0) 1
    rw [map_zero, ← map_one (algebraMap R B)]
    exact isHomogeneous_algebraMap e σ 1
  mul_mem i j f g hf hg := by
    change IsHomogeneous e σ (φ (i + j)) (f * g)
    rw [map_add]
    exact IsHomogeneous.mul hf hg

variable {φ}

theorem comp_coeAddMonoidHom (hφ : Function.Injective φ)
    (x : DirectSum ι fun i => homogeneousSubmodule e σ (φ i)) (i : ι) :
    comp e σ (φ i) (DirectSum.coeAddMonoidHom (fun i => homogeneousSubmodule e σ (φ i)) x) =
      x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeAddMonoidHom_of, DirectSum.coe_of_apply, (y.2 : IsHomogeneous e σ _ _).comp_eq]
    by_cases h : i = j
    · subst h
      simp
    · have h' : φ i ≠ φ j := fun h' => h (hφ h')
      simp [h', Ne.symm h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, DirectSum.add_apply, Submodule.coe_add]

/-- If the weights of all coordinate functions lie in the image of an injective
homomorphism, the homogeneous submodules form an internal direct sum over its source. -/
theorem isInternal_homogeneousSubmodule (hφ : Function.Injective φ)
    (hsupp : ∀ f m, comp e σ m f ≠ 0 → m ∈ Set.range φ) :
    DirectSum.IsInternal fun i => homogeneousSubmodule e σ (φ i) := by
  constructor
  · intro x y h
    ext i
    rw [← comp_coeAddMonoidHom e σ hφ x i, h, comp_coeAddMonoidHom e σ hφ y i]
  · intro f
    rw [← AddMonoidHom.mem_mrange, ← sum_support_comp e σ f]
    refine AddSubmonoid.sum_mem _ fun m hm => ?_
    by_cases h0 : comp e σ m f = 0
    · rw [h0]
      exact AddSubmonoid.zero_mem _
    · obtain ⟨i, rfl⟩ := hsupp f m h0
      exact ⟨DirectSum.of (fun i => homogeneousSubmodule e σ (φ i)) i
        ⟨comp e σ (φ i) f, isHomogeneous_comp e σ _ f⟩, DirectSum.coeAddMonoidHom_of _ _ _⟩

/-- The graded algebra structure of the homogeneous submodules, reindexed along an
injective homomorphism containing all weights. -/
@[instance_reducible]
def gradedAlgebra (hφ : Function.Injective φ)
    (hsupp : ∀ f m, comp e σ m f ≠ 0 → m ∈ Set.range φ) :
    GradedAlgebra fun i => homogeneousSubmodule e σ (φ i) :=
  { gradedMonoid_homogeneousSubmodule e σ φ,
    (isInternal_homogeneousSubmodule e σ hφ hsupp).chooseDecomposition with }

end Regrading

/-- The graded algebra structure on the representing algebra given by the weights. -/
@[instance_reducible]
def weightGradedAlgebra : GradedAlgebra (homogeneousSubmodule e σ) :=
  gradedAlgebra e σ (φ := AddMonoidHom.id (I → ℤ)) Function.injective_id
    fun _ m _ => ⟨m, rfl⟩

end Grading

end Langlands.GroupScheme.Corepresented
