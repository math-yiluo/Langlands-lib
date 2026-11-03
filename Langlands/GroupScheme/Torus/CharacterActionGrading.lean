import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.CommutativeAlgebra.GradedFixedQuotient

/-! # Grading from a natural character-group action on an affine point functor -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

/-- The group algebra over an `R`-algebra, still viewed over `R`. -/
abbrev algebra (B : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (AddMonoidAlgebra B M)

/-- The constant functions in the group algebra. -/
def constant (B : CommAlgCat.{u} R) : B ⟶ algebra (M := M) B :=
  CommAlgCat.ofHom AddMonoidAlgebra.singleZeroAlgHom

@[simp] theorem constant_apply (B : CommAlgCat.{u} R) (b : B) :
    (constant (M := M) B).hom b = AddMonoidAlgebra.single 0 b := rfl

/-- The universal character, whose values are the monomial units. -/
abbrev universal (B : CommAlgCat.{u} R) : Multiplicative M →* (algebra (M := M) B)ˣ :=
  Diagonalizable.monomialUnits (CommRingCat.of B) M

/-- Change the coefficient algebra of a character. -/
abbrev mapCharacter {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (t : Multiplicative M →* Bˣ) : Multiplicative M →* Cˣ :=
  (Units.map f.hom.toRingHom.toMonoidHom).comp t

/-- Evaluate a group algebra at a point and a character. -/
def evaluate {B C : CommAlgCat.{u} R} (x : B ⟶ C) (t : Multiplicative M →* Cˣ) :
    algebra (M := M) B ⟶ C :=
  CommAlgCat.ofHom (AddMonoidAlgebra.liftNCAlgHom x.hom ((Units.coeHom C).comp t)
    (fun _ _ => Commute.all _ _))

@[simp] theorem evaluate_single {B C : CommAlgCat.{u} R} (x : B ⟶ C)
    (t : Multiplicative M →* Cˣ) (m : M) (b : B) :
    (evaluate x t).hom (AddMonoidAlgebra.single m b) = x.hom b * (t (.ofAdd m) : C) :=
  AddMonoidAlgebra.liftNCRingHom_single _ _ (fun _ _ => Commute.all _ _) _ _

@[simp] theorem constant_evaluate {B C : CommAlgCat.{u} R} (x : B ⟶ C)
    (t : Multiplicative M →* Cˣ) : constant B ≫ evaluate x t = x := by
  apply CommAlgCat.hom_ext
  ext b
  change (evaluate x t).hom (AddMonoidAlgebra.single 0 b) = x.hom b
  rw [evaluate_single]
  simp

@[simp] theorem mapCharacter_evaluate_universal {B C : CommAlgCat.{u} R} (x : B ⟶ C)
    (t : Multiplicative M →* Cˣ) : mapCharacter (evaluate x t) (universal B) = t := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change (evaluate x t).hom (AddMonoidAlgebra.single m.toAdd 1) = _
  rw [evaluate_single]
  simp

/-- Coefficient-wise application of an algebra homomorphism. -/
def coefficientMap {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    algebra (M := M) B ⟶ algebra (M := M) C :=
  evaluate (f ≫ constant C) (universal C)

@[simp] theorem coefficientMap_single {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (m : M) (b : B) :
    (coefficientMap (M := M) f).hom (AddMonoidAlgebra.single m b) =
      AddMonoidAlgebra.single m (f.hom b) := by
  rw [coefficientMap, evaluate_single]
  change AddMonoidAlgebra.single 0 (f.hom b) * AddMonoidAlgebra.single m 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- Coefficient-wise substitution agrees with Mathlib's group-algebra ring map. -/
theorem coefficientMap_eq {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    (coefficientMap (M := M) f).hom.toRingHom =
      AddMonoidAlgebra.mapRingHom M f.hom.toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    change (coefficientMap f).hom (AddMonoidAlgebra.single 0 b) = _
    rw [coefficientMap_single, AddMonoidAlgebra.mapRingHom_single]
    rfl
  · intro m
    change (coefficientMap f).hom (AddMonoidAlgebra.single m 1) = _
    rw [coefficientMap_single, AddMonoidAlgebra.mapRingHom_single]
    rfl

@[simp] theorem coefficientMap_coeff {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (q : AddMonoidAlgebra B M) (m : M) :
    ((coefficientMap (M := M) f).hom q).coeff m = f.hom (q.coeff m) := by
  change (((coefficientMap (M := M) f).hom.toRingHom) q).coeff m = _
  rw [coefficientMap_eq, AddMonoidAlgebra.coeff_mapRingHom]
  rfl

@[simp] theorem constant_coefficientMap {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    constant B ≫ coefficientMap (M := M) f = f ≫ constant C := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro b
  change (coefficientMap f).hom (AddMonoidAlgebra.single 0 b) =
    AddMonoidAlgebra.single 0 (f.hom b)
  exact coefficientMap_single f 0 b

/-- Evaluation commutes with applying a map to every coefficient. -/
@[simp] theorem coefficientMap_evaluate {B C D : CommAlgCat.{u} R}
    (x : B ⟶ C) (f : C ⟶ D) (t : Multiplicative M →* Dˣ) :
    coefficientMap (M := M) x ≫ evaluate f t = evaluate (x ≫ f) t := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    change (evaluate f t).hom ((coefficientMap x).hom (AddMonoidAlgebra.single m 1)) =
      (evaluate (x ≫ f) t).hom (AddMonoidAlgebra.single m 1)
    rw [coefficientMap_single, evaluate_single, evaluate_single]
    rfl
  · apply AlgHom.ext
    intro b
    change (evaluate f t).hom ((coefficientMap x).hom (AddMonoidAlgebra.single 0 b)) =
      (evaluate (x ≫ f) t).hom (AddMonoidAlgebra.single 0 b)
    rw [coefficientMap_single, evaluate_single, evaluate_single]
    rfl

@[simp] theorem mapCharacter_coefficientMap_universal {B C : CommAlgCat.{u} R}
    (f : B ⟶ C) : mapCharacter (coefficientMap (M := M) f) (universal B) = universal C := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change (coefficientMap (M := M) f).hom (AddMonoidAlgebra.single m.toAdd 1) = _
  rw [coefficientMap_single, map_one]
  rfl

/-- The diagonal substitution `Xᵐ ↦ XᵐYᵐ` into the iterated group algebra. -/
def diagonalMap (B : CommAlgCat.{u} R) :
    algebra (M := M) B ⟶ algebra (M := M) (algebra (M := M) B) :=
  evaluate (constant B ≫ constant (algebra B))
    (universal (algebra B) * mapCharacter (constant (algebra B)) (universal B))

@[simp] theorem diagonalMap_single (B : CommAlgCat.{u} R) (m : M) (b : B) :
    (diagonalMap (M := M) B).hom (AddMonoidAlgebra.single m b) =
      AddMonoidAlgebra.single m (AddMonoidAlgebra.single m b) := by
  rw [diagonalMap, evaluate_single]
  change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
    (AddMonoidAlgebra.single m 1 *
      AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single m 1)) = _
  simp only [AddMonoidAlgebra.single_mul_single, add_zero, zero_add,
    one_mul, mul_one]

@[simp] theorem diagonalMap_coeff (B : CommAlgCat.{u} R)
    (q : AddMonoidAlgebra B M) (m : M) :
    ((diagonalMap (M := M) B).hom q).coeff m = AddMonoidAlgebra.single m (q.coeff m) := by
  classical
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q q' hq hq' =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hq, hq', AddMonoidAlgebra.single_add]
  | single n b =>
    rw [diagonalMap_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
    by_cases h : n = m
    · subst h
      simp
    · simp [Ne.symm h]

/-- A natural action of the diagonalizable character functor on the points of
`Spec B`. No preservation of a group law on `Spec B` is required. -/
structure Action (B : CommAlgCat.{u} R) where
  act : ∀ {C : CommAlgCat.{u} R}, (Multiplicative M →* Cˣ) → (B ⟶ C) → (B ⟶ C)
  one : ∀ {C : CommAlgCat.{u} R} (x : B ⟶ C), act 1 x = x
  mul : ∀ {C : CommAlgCat.{u} R} (t s : Multiplicative M →* Cˣ) (x : B ⟶ C),
    act (t * s) x = act t (act s x)
  naturality : ∀ {C D : CommAlgCat.{u} R} (f : C ⟶ D)
    (t : Multiplicative M →* Cˣ) (x : B ⟶ C),
    act (mapCharacter f t) (x ≫ f) = act t x ≫ f

variable {B : CommAlgCat.{u} R} (a : Action (M := M) B)

/-- The coaction obtained at the universal character and universal affine point. -/
def coaction : B ⟶ algebra (M := M) B := a.act (universal B) (constant B)

/-- Every point action is recovered by evaluating the coaction. -/
theorem act_eq_coaction_evaluate {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ)
    (x : B ⟶ C) : a.act t x = coaction a ≫ evaluate x t := by
  have h := a.naturality (evaluate x t) (universal B) (constant B)
  simpa only [mapCharacter_evaluate_universal, constant_evaluate, coaction] using h

/-- Applying the action at the universal character after changing the affine point
amounts to applying that point to the coefficients of the coaction. -/
theorem act_universal {C : CommAlgCat.{u} R} (x : B ⟶ C) :
    a.act (universal C) (x ≫ constant C) = coaction a ≫ coefficientMap (M := M) x := by
  have h := a.naturality (coefficientMap (M := M) x) (universal B) (constant B)
  simpa only [mapCharacter_coefficientMap_universal, constant_coefficientMap, coaction] using h

/-- The identity of the point action is the counit identity of the coaction. -/
theorem coaction_counit : coaction a ≫ evaluate (𝟙 B) (1 : Multiplicative M →* Bˣ) = 𝟙 B := by
  rw [← act_eq_coaction_evaluate, a.one]

/-- Associativity of the point action gives coassociativity of the coaction. -/
theorem coaction_coassociative :
    coaction a ≫ coefficientMap (M := M) (coaction a) =
      coaction a ≫ diagonalMap (M := M) B := by
  have hi := a.naturality (constant (M := M) (algebra (M := M) B))
    (universal B) (constant B)
  change a.act (mapCharacter (constant (algebra B)) (universal B))
    (constant B ≫ constant (algebra B)) = coaction a ≫ constant (algebra B) at hi
  calc
    coaction a ≫ coefficientMap (M := M) (coaction a) =
        a.act (universal (algebra B)) (coaction a ≫ constant (algebra B)) :=
      (act_universal a (coaction a)).symm
    _ = a.act (universal (algebra B))
        (a.act (mapCharacter (constant (algebra B)) (universal B))
          (constant B ≫ constant (algebra B))) := by rw [hi]
    _ = a.act (universal (algebra B) *
        mapCharacter (constant (algebra B)) (universal B))
        (constant B ≫ constant (algebra B)) := (a.mul _ _ _).symm
    _ = coaction a ≫ diagonalMap (M := M) B := act_eq_coaction_evaluate a _ _

/-- Each coefficient of the coaction is homogeneous of its indicated degree. -/
theorem coaction_coefficient_homogeneous (b : B) (m : M) :
    (coaction a).hom (((coaction a).hom b).coeff m) =
      AddMonoidAlgebra.single m (((coaction a).hom b).coeff m) := by
  have h := congrArg (fun f : B ⟶ algebra (M := M) (algebra (M := M) B) =>
    (f.hom b).coeff m) (coaction_coassociative a)
  change ((coefficientMap (coaction a)).hom ((coaction a).hom b)).coeff m =
    ((diagonalMap B).hom ((coaction a).hom b)).coeff m at h
  rw [coefficientMap_coeff, diagonalMap_coeff] at h
  exact h

/-- Scalars in a character-action coaction have degree zero. -/
theorem coaction_scalar (r : R) :
    (coaction a).hom (algebraMap R B r) =
      AddMonoidAlgebra.single 0 (algebraMap R B r) := by
  rw [(coaction a).hom.commutes]
  rfl

/-- The quotient by the actual character-action fixed equations is formally smooth
whenever the original affine algebra is formally smooth. -/
theorem formallySmooth_fixedQuotient [Algebra.FormallySmooth R B] :
    Algebra.FormallySmooth R
      (B ⧸ Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
        (coaction a).hom.toRingHom) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.formallySmooth_quotient_fixedIdeal
    (coaction a).hom.toRingHom (coaction_scalar a) (coaction_coefficient_homogeneous a)

/-- A point is fixed if every character fixes it after every algebra refinement. -/
def IsFixed {C : CommAlgCat.{u} R} (x : B ⟶ C) : Prop :=
  ∀ (D : CommAlgCat.{u} R) (f : C ⟶ D) (t : Multiplicative M →* Dˣ),
    a.act t (x ≫ f) = x ≫ f

/-- Vanishing of the fixed ideal is equivalent to fixedness over all algebra
refinements. In particular the criterion retains scheme-theoretic, rather than
only rational-point, fixedness. -/
theorem fixedIdeal_le_ker_iff_isFixed {C : CommAlgCat.{u} R} (x : B ⟶ C) :
    Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
      (coaction a).hom.toRingHom ≤ RingHom.ker x.hom.toRingHom ↔ IsFixed a x := by
  rw [Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal_le_ker_iff]
  constructor
  · intro h D f t
    have hx : coaction a ≫ coefficientMap (M := M) x = x ≫ constant C := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      change (coefficientMap x).hom ((coaction a).hom b) =
        AddMonoidAlgebra.single 0 (x.hom b)
      change (coefficientMap x).hom.toRingHom ((coaction a).hom.toRingHom b) = _
      rw [coefficientMap_eq]
      exact h b
    rw [act_eq_coaction_evaluate, ← coefficientMap_evaluate, ← Category.assoc,
      hx, Category.assoc, constant_evaluate]
  · intro h b
    have hx := h (algebra (M := M) C) (constant C) (universal C)
    rw [act_universal] at hx
    have hb := congrArg (fun f : B ⟶ algebra (M := M) C => f.hom b) hx
    change (coefficientMap x).hom ((coaction a).hom b) =
      AddMonoidAlgebra.single 0 (x.hom b) at hb
    change (coefficientMap x).hom.toRingHom ((coaction a).hom.toRingHom b) = _ at hb
    rw [coefficientMap_eq] at hb
    exact hb

end Langlands.GroupScheme.CharacterAction
