import Langlands.GroupScheme.PointwiseSchemeAction
import Langlands.GroupScheme.Multiplicative
import Langlands.CommutativeAlgebra.GradedFixedQuotient
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Laurent coactions of multiplicative group actions on affine schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineSchemeCoordinates

variable {R : CommRingCat.{u}} (X : Over (Spec R)) [IsAffine X.left]

/-- An affine scheme is in the essential image of relative spectrum. -/
theorem mem_essImage : (algSpec R).essImage X :=
  essImage_algSpec.mpr inferInstance

/-- A coordinate algebra of the supplied affine scheme. -/
abbrev algebra : CommAlgCat.{u} R := (mem_essImage X).witness.unop

/-- The coordinate comparison with the supplied scheme. -/
def schemeIso : (algSpec R).obj (op (algebra X)) ≅ X :=
  (mem_essImage X).getIso

/-- Coordinate algebra homomorphisms are points of the supplied affine scheme. -/
def pointEquiv (C : CommAlgCat.{u} R) :
    (algebra X ⟶ C) ≃ ((algSpec R).obj (op C) ⟶ X) where
  toFun x := (algSpec R).map x.op ≫ (schemeIso X).hom
  invFun x := (algSpec.fullyFaithful.preimage (x ≫ (schemeIso X).inv)).unop
  left_inv x := by
    apply Quiver.Hom.op_inj
    apply (algSpec R).map_injective
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp
  right_inv x := by
    change (algSpec R).map
      ((algSpec.fullyFaithful.preimage (x ≫ (schemeIso X).inv)).unop).op ≫
        (schemeIso X).hom = x
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp

/-- Algebra refinement is pullback of an actual point. -/
theorem pointEquiv_comp {C D : CommAlgCat.{u} R} (x : algebra X ⟶ C) (f : C ⟶ D) :
    pointEquiv X D (x ≫ f) = (algSpec R).map f.op ≫ pointEquiv X C x := by
  change (algSpec R).map (f.op ≫ x.op) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rfl

end AffineSchemeCoordinates

namespace GmCoordinateAction

variable {R : CommRingCat.{u}}

/-- Laurent polynomials over an algebra, viewed as an algebra over the same base. -/
abbrev laurentAlgebra (B : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (LaurentPolynomial B)

/-- Constant Laurent polynomials. -/
def constant (B : CommAlgCat.{u} R) : B ⟶ laurentAlgebra B :=
  CommAlgCat.ofHom AddMonoidAlgebra.singleZeroAlgHom

/-- The Laurent coordinate as a unit. -/
def universal (B : CommAlgCat.{u} R) : (laurentAlgebra B)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]

theorem universal_zpow_val (B : CommAlgCat.{u} R) (n : ℤ) :
    ((universal B ^ n : (laurentAlgebra B)ˣ) : laurentAlgebra B) =
      LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]
    rfl
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih, LaurentPolynomial.T_sub]
    rfl

/-- Evaluate the Laurent variable at a unit and the coefficients at an algebra point. -/
def evaluate {B C : CommAlgCat.{u} R} (x : B ⟶ C) (t : Cˣ) :
    laurentAlgebra B ⟶ C :=
  CommAlgCat.ofHom
    { LaurentPolynomial.eval₂ x.hom.toRingHom t with
      commutes' := fun r => by
        change LaurentPolynomial.eval₂ x.hom.toRingHom t
          (LaurentPolynomial.C (algebraMap R B r)) = _
        rw [LaurentPolynomial.eval₂_C]
        exact x.hom.commutes r }

@[simp] theorem evaluate_single {B C : CommAlgCat.{u} R} (x : B ⟶ C)
    (t : Cˣ) (n : ℤ) (b : B) :
    (evaluate x t).hom (AddMonoidAlgebra.single n b) = x.hom b * (t ^ n : Cˣ) := by
  change LaurentPolynomial.eval₂ x.hom.toRingHom t (AddMonoidAlgebra.single n b) = _
  rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
  rfl

@[simp] theorem constant_evaluate {B C : CommAlgCat.{u} R} (x : B ⟶ C) (t : Cˣ) :
    constant B ≫ evaluate x t = x := by
  apply CommAlgCat.hom_ext
  ext b
  change (evaluate x t).hom (AddMonoidAlgebra.single 0 b) = x.hom b
  rw [evaluate_single]
  simp

@[simp] theorem map_evaluate_universal {B C : CommAlgCat.{u} R} (x : B ⟶ C) (t : Cˣ) :
    Units.map (evaluate x t).hom.toRingHom.toMonoidHom (universal B) = t := by
  apply Units.ext
  change (evaluate x t).hom (AddMonoidAlgebra.single 1 1) = _
  rw [evaluate_single]
  simp

/-- Apply an algebra homomorphism to every Laurent coefficient. -/
def coefficientMap {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    laurentAlgebra B ⟶ laurentAlgebra C :=
  evaluate (f ≫ constant C) (universal C)

@[simp] theorem coefficientMap_single {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (n : ℤ) (b : B) :
    (coefficientMap f).hom (AddMonoidAlgebra.single n b) =
      AddMonoidAlgebra.single n (f.hom b) := by
  rw [coefficientMap, evaluate_single, universal_zpow_val]
  change AddMonoidAlgebra.single 0 (f.hom b) * AddMonoidAlgebra.single n 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

theorem coefficientMap_eq {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    (coefficientMap f).hom.toRingHom = AddMonoidAlgebra.mapRingHom ℤ f.hom.toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    change (coefficientMap f).hom (AddMonoidAlgebra.single 0 b) = _
    rw [coefficientMap_single, AddMonoidAlgebra.mapRingHom_single]
    rfl
  · intro n
    change (coefficientMap f).hom (AddMonoidAlgebra.single n 1) = _
    rw [coefficientMap_single, AddMonoidAlgebra.mapRingHom_single]
    rfl

@[simp] theorem coefficientMap_coeff {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (q : LaurentPolynomial B) (n : ℤ) :
    ((coefficientMap f).hom q).coeff n = f.hom (q.coeff n) := by
  change ((coefficientMap f).hom.toRingHom q).coeff n = _
  rw [coefficientMap_eq, AddMonoidAlgebra.coeff_mapRingHom]
  rfl

@[simp] theorem constant_coefficientMap {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    constant B ≫ coefficientMap f = f ≫ constant C := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  exact fun b => coefficientMap_single f 0 b

@[simp] theorem coefficientMap_evaluate {B C D : CommAlgCat.{u} R}
    (x : B ⟶ C) (f : C ⟶ D) (t : Dˣ) :
    coefficientMap x ≫ evaluate f t = evaluate (x ≫ f) t := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro n
    change (evaluate f t).hom ((coefficientMap x).hom (AddMonoidAlgebra.single n 1)) =
      (evaluate (x ≫ f) t).hom (AddMonoidAlgebra.single n 1)
    rw [coefficientMap_single, evaluate_single, evaluate_single]
    rfl
  · apply AlgHom.ext
    intro b
    change (evaluate f t).hom ((coefficientMap x).hom (AddMonoidAlgebra.single 0 b)) =
      (evaluate (x ≫ f) t).hom (AddMonoidAlgebra.single 0 b)
    rw [coefficientMap_single, evaluate_single, evaluate_single]
    rfl

@[simp] theorem map_coefficientMap_universal {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    Units.map (coefficientMap f).hom.toRingHom.toMonoidHom (universal B) = universal C := by
  apply Units.ext
  change (coefficientMap f).hom (AddMonoidAlgebra.single 1 1) = _
  rw [coefficientMap_single, map_one]
  rfl

/-- The substitution of the product of two Laurent variables. -/
def diagonalMap (B : CommAlgCat.{u} R) :
    laurentAlgebra B ⟶ laurentAlgebra (laurentAlgebra B) :=
  evaluate (constant B ≫ constant (laurentAlgebra B))
    (universal (laurentAlgebra B) *
      Units.map (constant (laurentAlgebra B)).hom.toRingHom.toMonoidHom (universal B))

@[simp] theorem diagonalMap_single (B : CommAlgCat.{u} R) (n : ℤ) (b : B) :
    (diagonalMap B).hom (AddMonoidAlgebra.single n b) =
      AddMonoidAlgebra.single n (AddMonoidAlgebra.single n b) := by
  rw [diagonalMap, evaluate_single, mul_zpow, Units.val_mul, universal_zpow_val,
    ← map_zpow]
  change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
    (LaurentPolynomial.T n *
      (constant (laurentAlgebra B)).hom (universal B ^ n : (laurentAlgebra B)ˣ)) = _
  rw [universal_zpow_val]
  simp only [constant, CommAlgCat.hom_ofHom, AddMonoidAlgebra.singleZeroAlgHom_apply]
  change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
    (AddMonoidAlgebra.single n 1 *
      AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single n 1)) = _
  simp only [AddMonoidAlgebra.single_mul_single, add_zero, zero_add, one_mul, mul_one]

@[simp] theorem diagonalMap_coeff (B : CommAlgCat.{u} R)
    (q : LaurentPolynomial B) (n : ℤ) :
    ((diagonalMap B).hom q).coeff n = AddMonoidAlgebra.single n (q.coeff n) := by
  classical
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q q' hq hq' =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hq, hq', AddMonoidAlgebra.single_add]
  | single m b =>
    rw [diagonalMap_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
    by_cases h : m = n
    · subst h
      simp
    · simp [Ne.symm h]

/-- A natural action of units on the points of an affine algebra. -/
structure Action (B : CommAlgCat.{u} R) where
  act : ∀ {C : CommAlgCat.{u} R}, Cˣ → (B ⟶ C) → (B ⟶ C)
  one : ∀ {C : CommAlgCat.{u} R} (x : B ⟶ C), act 1 x = x
  mul : ∀ {C : CommAlgCat.{u} R} (t s : Cˣ) (x : B ⟶ C),
    act (t * s) x = act t (act s x)
  naturality : ∀ {C D : CommAlgCat.{u} R} (f : C ⟶ D) (t : Cˣ) (x : B ⟶ C),
    act (Units.map f.hom.toRingHom.toMonoidHom t) (x ≫ f) = act t x ≫ f

variable {B : CommAlgCat.{u} R} (a : Action B)

/-- The actual Laurent coaction obtained at the universal unit. -/
def coaction : B ⟶ laurentAlgebra B := a.act (universal B) (constant B)

theorem act_eq_coaction_evaluate {C : CommAlgCat.{u} R} (t : Cˣ) (x : B ⟶ C) :
    a.act t x = coaction a ≫ evaluate x t := by
  have h := a.naturality (evaluate x t) (universal B) (constant B)
  rw [map_evaluate_universal, constant_evaluate] at h
  exact h

theorem act_universal {C : CommAlgCat.{u} R} (x : B ⟶ C) :
    a.act (universal C) (x ≫ constant C) = coaction a ≫ coefficientMap x := by
  have h := a.naturality (coefficientMap x) (universal B) (constant B)
  rw [map_coefficientMap_universal, constant_coefficientMap] at h
  exact h

theorem coaction_counit : coaction a ≫ evaluate (𝟙 B) 1 = 𝟙 B := by
  rw [← act_eq_coaction_evaluate, a.one]

theorem coaction_coassociative :
    coaction a ≫ coefficientMap (coaction a) = coaction a ≫ diagonalMap B := by
  have hi := a.naturality (constant (laurentAlgebra B)) (universal B) (constant B)
  change a.act (Units.map (constant (laurentAlgebra B)).hom.toRingHom.toMonoidHom
    (universal B)) (constant B ≫ constant (laurentAlgebra B)) =
      coaction a ≫ constant (laurentAlgebra B) at hi
  calc
    coaction a ≫ coefficientMap (coaction a) =
        a.act (universal (laurentAlgebra B)) (coaction a ≫ constant (laurentAlgebra B)) :=
      (act_universal a (coaction a)).symm
    _ = a.act (universal (laurentAlgebra B))
        (a.act (Units.map (constant (laurentAlgebra B)).hom.toRingHom.toMonoidHom
          (universal B)) (constant B ≫ constant (laurentAlgebra B))) := by rw [hi]
    _ = a.act (universal (laurentAlgebra B) *
        Units.map (constant (laurentAlgebra B)).hom.toRingHom.toMonoidHom (universal B))
          (constant B ≫ constant (laurentAlgebra B)) := (a.mul _ _ _).symm
    _ = coaction a ≫ diagonalMap B := act_eq_coaction_evaluate a _ _

theorem coaction_coefficient_homogeneous (b : B) (n : ℤ) :
    (coaction a).hom (((coaction a).hom b).coeff n) =
      AddMonoidAlgebra.single n (((coaction a).hom b).coeff n) := by
  have h := congrArg (fun f : B ⟶ laurentAlgebra (laurentAlgebra B) =>
    (f.hom b).coeff n) (coaction_coassociative a)
  change ((coefficientMap (coaction a)).hom ((coaction a).hom b)).coeff n =
    ((diagonalMap B).hom ((coaction a).hom b)).coeff n at h
  rwa [coefficientMap_coeff, diagonalMap_coeff] at h

theorem coaction_scalar (r : R) :
    (coaction a).hom (algebraMap R B r) = LaurentPolynomial.C (algebraMap R B r) := by
  rw [(coaction a).hom.commutes]
  rfl

/-- Fixedness after every refinement of the coefficient algebra. -/
def IsFixed {C : CommAlgCat.{u} R} (x : B ⟶ C) : Prop :=
  ∀ (D : CommAlgCat.{u} R) (f : C ⟶ D) (t : Dˣ), a.act t (x ≫ f) = x ≫ f

/-- The coefficient equations retain all algebra refinements. -/
theorem fixedIdeal_le_ker_iff_isFixed {C : CommAlgCat.{u} R} (x : B ⟶ C) :
    Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
      (coaction a).hom.toRingHom ≤ RingHom.ker x.hom.toRingHom ↔ IsFixed a x := by
  rw [Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal_le_ker_iff]
  constructor
  · intro h D f t
    have hx : coaction a ≫ coefficientMap x = x ≫ constant C := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      change (coefficientMap x).hom.toRingHom ((coaction a).hom.toRingHom b) = _
      rw [coefficientMap_eq]
      exact h b
    rw [act_eq_coaction_evaluate, ← coefficientMap_evaluate, ← Category.assoc,
      hx, Category.assoc, constant_evaluate]
  · intro h b
    have hx := h (laurentAlgebra C) (constant C) (universal C)
    rw [act_universal] at hx
    have hb := congrArg (fun f : B ⟶ laurentAlgebra C => f.hom b) hx
    change (coefficientMap x).hom.toRingHom ((coaction a).hom.toRingHom b) = _ at hb
    rw [coefficientMap_eq] at hb
    exact hb

/-- The fixed coordinate quotient of a formally smooth algebra is formally smooth. -/
theorem formallySmooth_fixedQuotient [Algebra.FormallySmooth R B] :
    Algebra.FormallySmooth R
      (B ⧸ Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
        (coaction a).hom.toRingHom) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.formallySmooth_quotient_fixedIdeal
    (coaction a).hom.toRingHom (coaction_scalar a) (coaction_coefficient_homogeneous a)

/-- The actual point of the chosen multiplicative group belonging to a unit. -/
def unitPoint {C : CommAlgCat.{u} R} (t : Cˣ) :
    (algSpec R).obj (op C) ⟶ (Gm (Spec R)).X :=
  (Gm.affinePointsEquiv ((algSpec R).obj (op C)).hom).symm t

@[simp] theorem unitPoint_one (C : CommAlgCat.{u} R) : unitPoint (1 : Cˣ) = 1 :=
  map_one _

@[simp] theorem unitPoint_mul {C : CommAlgCat.{u} R} (t s : Cˣ) :
    unitPoint (t * s) = unitPoint t * unitPoint s :=
  map_mul _ _ _

theorem affinePointsEquiv_comp {C D : CommAlgCat.{u} R} (f : C ⟶ D)
    (h : (algSpec R).obj (op C) ⟶ (Gm (Spec R)).X) :
    Gm.affinePointsEquiv ((algSpec R).obj (op D)).hom ((algSpec R).map f.op ≫ h) =
      Units.map f.hom.toRingHom.toMonoidHom
        (Gm.affinePointsEquiv ((algSpec R).obj (op C)).hom h) := by
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom f.hom.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of D)).hom) _ =
      f.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

@[simp] theorem unitPoint_map {C D : CommAlgCat.{u} R} (f : C ⟶ D) (t : Cˣ) :
    unitPoint (Units.map f.hom.toRingHom.toMonoidHom t) =
      (algSpec R).map f.op ≫ unitPoint t := by
  apply (Gm.affinePointsEquiv ((algSpec R).obj (op D)).hom).injective
  rw [unitPoint, MulEquiv.apply_symm_apply, affinePointsEquiv_comp]
  rw [unitPoint, MulEquiv.apply_symm_apply]

variable {X : Over (Spec R)} [IsAffine X.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)

/-- Transfer an actual action on an arbitrary affine scheme to its coordinates. -/
def ofPointwiseSchemeAction : Action (AffineSchemeCoordinates.algebra X) where
  act {C} t x := (AffineSchemeCoordinates.pointEquiv X C).symm
    (s.act (unitPoint t) (AffineSchemeCoordinates.pointEquiv X C x))
  one {C} x := by
    apply (AffineSchemeCoordinates.pointEquiv X C).injective
    simp only [Equiv.apply_symm_apply, unitPoint_one, s.act_one_left]
  mul {C} t r x := by
    apply (AffineSchemeCoordinates.pointEquiv X C).injective
    simp only [Equiv.apply_symm_apply, unitPoint_mul, s.act_mul_left]
  naturality {C D} f t x := by
    apply (AffineSchemeCoordinates.pointEquiv X D).injective
    simp only [Equiv.apply_symm_apply, AffineSchemeCoordinates.pointEquiv_comp,
      unitPoint_map, ← s.naturality]

theorem pointEquiv_schemeAct {C : CommAlgCat.{u} R} (t : Cˣ)
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    AffineSchemeCoordinates.pointEquiv X C ((ofPointwiseSchemeAction s).act t x) =
      s.act (unitPoint t) (AffineSchemeCoordinates.pointEquiv X C x) :=
  Equiv.apply_symm_apply _ _

/-- The coordinate criterion agrees with fixedness on all relative schemes. -/
theorem isFixed_iff_schemeAction {C : CommAlgCat.{u} R}
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    IsFixed (ofPointwiseSchemeAction s) x ↔
      s.IsFixed (AffineSchemeCoordinates.pointEquiv X C x) := by
  let : IsAffine (Gm (Spec R)).X.left := by
    change IsAffine (CategoryTheory.Limits.pullback _ _)
    dsimp [Gm.overSpecZ]
    infer_instance
  rw [s.isFixed_iff_affineRefinements]
  constructor
  · intro hx D f h
    let t := Gm.affinePointsEquiv ((algSpec R).obj (op D)).hom h
    have ht : unitPoint t = h := MulEquiv.symm_apply_apply _ h
    have e := congrArg (AffineSchemeCoordinates.pointEquiv X D) (hx D f t)
    rw [pointEquiv_schemeAct, AffineSchemeCoordinates.pointEquiv_comp, ht] at e
    exact e
  · intro hx D f t
    apply (AffineSchemeCoordinates.pointEquiv X D).injective
    rw [pointEquiv_schemeAct, AffineSchemeCoordinates.pointEquiv_comp]
    exact hx D f (unitPoint t)

/-- The actual coefficient ideal of an affine multiplicative-group action. -/
abbrev schemeActionFixedIdeal : Ideal (AffineSchemeCoordinates.algebra X) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
    (coaction (ofPointwiseSchemeAction s)).hom.toRingHom

theorem schemeActionFixedIdeal_le_ker_iff {C : CommAlgCat.{u} R}
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    schemeActionFixedIdeal s ≤ RingHom.ker x.hom.toRingHom ↔
      s.IsFixed (AffineSchemeCoordinates.pointEquiv X C x) := by
  rw [← isFixed_iff_schemeAction, ← fixedIdeal_le_ker_iff_isFixed]

end GmCoordinateAction

end Langlands.GroupScheme
