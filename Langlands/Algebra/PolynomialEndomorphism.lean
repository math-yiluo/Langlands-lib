import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Polynomial modules and modules with an endomorphism -/

universe u v

open CategoryTheory Polynomial

noncomputable section

namespace Langlands.Algebra.PolynomialEndomorphism

/-- Modules with a specified linear endomorphism, and linear intertwiners. -/
abbrev EndomorphismCat (R : Type u) [CommRing R] :=
  Endofunctor.Algebra (𝟭 (ModuleCat.{v} R))

variable (R : Type u) [CommRing R]

/-- The structure morphism as an ordinary linear endomorphism. -/
abbrev endomorphism (A : EndomorphismCat.{u, v} R) : Module.End R A.a := A.str.hom

/-- Restriction of polynomial scalars along the constant-polynomial homomorphism. -/
abbrev restrict : ModuleCat.{v} R[X] ⥤ ModuleCat.{v} R :=
  ModuleCat.restrictScalars (C : R →+* R[X])

/-- The categorical compatibility equation is the ordinary intertwining equation. -/
theorem intertwining_iff (A B : EndomorphismCat.{u, v} R) (f : A.a ⟶ B.a) :
    ((𝟭 (ModuleCat R)).map f ≫ B.str = A.str ≫ f) ↔
      ∀ x : A.a, f (A.str x) = B.str (f x) := by
  constructor
  · intro h x
    exact (congrArg (fun g : A.a ⟶ B.a => g x) h).symm
  · intro h
    ext x
    exact (h x).symm

/-- Algebra morphisms correspond exactly to linear maps intertwining the endomorphisms. -/
def homEquiv (A B : EndomorphismCat.{u, v} R) :
    (A ⟶ B) ≃ {f : A.a →ₗ[R] B.a // ∀ x, f (A.str x) = B.str (f x)} where
  toFun f := ⟨f.f.hom, (intertwining_iff R A B f.f).mp f.h⟩
  invFun f :=
    { f := ModuleCat.ofHom f.1
      h := (intertwining_iff R A B (ModuleCat.ofHom f.1)).mpr f.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Multiplication by X on the given polynomial module, as an R-linear endomorphism. -/
def xAction (M : ModuleCat.{v} R[X]) : (restrict R).obj M ⟶ (restrict R).obj M :=
  ModuleCat.ofHom (X := (restrict R).obj M) (Y := (restrict R).obj M)
    { toFun := fun m => (X : R[X]) • (m : M)
      map_add' := smul_add _
      map_smul' := fun r m => by
        change (X : R[X]) • (C r • (m : M)) = C r • ((X : R[X]) • (m : M))
        exact smul_comm _ _ _ }

@[simp] theorem xAction_apply (M : ModuleCat.{v} R[X]) (m : M) :
    xAction R M m = (X : R[X]) • m := rfl

@[simp] theorem restrict_smul (M : ModuleCat.{v} R[X]) (r : R)
    (m : (restrict R).obj M) :
    r • m = C r • (m : M) := rfl

/-- Forget to R and retain the actual action of X. -/
def fromPolynomial : ModuleCat.{v} R[X] ⥤ EndomorphismCat.{u, v} R where
  obj M := { a := (restrict R).obj M, str := xAction R M }
  map f :=
    { f := (restrict R).map f
      h := by
        ext x
        exact (f.hom.map_smul (X : R[X]) x).symm }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem fromPolynomial_map_apply {M N : ModuleCat.{v} R[X]} (f : M ⟶ N)
    (m : M) :
    ((fromPolynomial R).map f).f m = f m := rfl

/-- Evaluation at the specified endomorphism supplies the polynomial module. -/
noncomputable def toPolynomialObj (A : EndomorphismCat.{u, v} R) : ModuleCat.{v} R[X] :=
  ModuleCat.of R[X] (Module.AEval' (endomorphism R A))

/-- An intertwiner is polynomial-linear for the evaluation actions. -/
noncomputable def toPolynomialMap {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    toPolynomialObj R A ⟶ toPolynomialObj R B :=
  ModuleCat.ofHom <| LinearMap.ofAEval (endomorphism R A)
    ((Module.AEval'.of (endomorphism R B)).toLinearMap.comp f.f.hom) (fun x => by
      change Module.AEval'.of (endomorphism R B) (f.f (A.str x)) =
        (X : R[X]) • Module.AEval'.of (endomorphism R B) (f.f x)
      rw [(intertwining_iff R A B f.f).mp f.h x, Module.AEval'.X_smul_of])

/-- Polynomial evaluation is functorial on linear intertwiners. -/
noncomputable def toPolynomial : EndomorphismCat.{u, v} R ⥤ ModuleCat.{v} R[X] where
  obj := toPolynomialObj R
  map := toPolynomialMap R
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem toPolynomialMap_of {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B)
    (x : A.a) :
    (toPolynomial R).map f (Module.AEval'.of (endomorphism R A) x) =
      Module.AEval'.of (endomorphism R B) (f.f x) := rfl

/-- The evaluation action of an arbitrary polynomial. -/
theorem toPolynomial_smul (A : EndomorphismCat.{u, v} R) (p : R[X]) (x : A.a) :
    p • Module.AEval'.of (endomorphism R A) x =
      Module.AEval'.of (endomorphism R A) ((aeval (endomorphism R A) p) x) := rfl

@[simp] theorem toPolynomial_C_smul (A : EndomorphismCat.{u, v} R) (r : R) (x : A.a) :
    (C r : R[X]) • Module.AEval'.of (endomorphism R A) x =
      Module.AEval'.of (endomorphism R A) (r • x) := by
  rw [Module.AEval.C_smul, map_smul]

@[simp] theorem toPolynomial_X_smul (A : EndomorphismCat.{u, v} R) (x : A.a) :
    (X : R[X]) • Module.AEval'.of (endomorphism R A) x =
      Module.AEval'.of (endomorphism R A) (A.str x) :=
  Module.AEval'.X_smul_of _ _

/-- The restricted R-action and the original polynomial action form a scalar tower. -/
local instance restrictScalarTower (M : ModuleCat.{v} R[X]) :
    IsScalarTower R R[X] ((restrict R).obj M) where
  smul_assoc r p m := by
    change (r • p) • (m : M) = C r • (p • (m : M))
    rw [smul_eq_C_mul, mul_smul]

/-- Evaluation at the original X-action recovers the given polynomial module. -/
def polynomialRoundTrip (M : ModuleCat.{v} R[X]) :
    (toPolynomial R).obj ((fromPolynomial R).obj M) ≅ M :=
  (LinearEquiv.ofAEval (xAction R M).hom
    (LinearEquiv.refl R ((restrict R).obj M)) (fun _ => rfl)).toModuleIso

@[simp] theorem polynomialRoundTrip_hom_apply (M : ModuleCat.{v} R[X])
    (x : (toPolynomial R).obj ((fromPolynomial R).obj M)) :
    (polynomialRoundTrip R M).hom x = (Module.AEval'.of (xAction R M).hom).symm x := rfl

@[simp] theorem polynomialRoundTrip_inv_apply (M : ModuleCat.{v} R[X]) (x : M) :
    (polynomialRoundTrip R M).inv x = Module.AEval'.of (xAction R M).hom x := rfl

/-- The polynomial-module round trip retains every scalar of the original action. -/
theorem polynomialRoundTrip_smul (M : ModuleCat.{v} R[X]) (p : R[X]) (x : M) :
    (Module.AEval'.of (xAction R M).hom).symm
      (p • Module.AEval'.of (xAction R M).hom x) = p • x :=
  (polynomialRoundTrip R M).hom.hom.map_smul p _

/-- The polynomial-module round trip is also an R-linear equivalence along constants. -/
def polynomialRoundTripLinear (M : ModuleCat.{v} R[X]) :
    ((fromPolynomial R).obj ((toPolynomial R).obj ((fromPolynomial R).obj M))).a ≃ₗ[R]
      ((fromPolynomial R).obj M).a :=
  ((restrict R).mapIso (polynomialRoundTrip R M)).toLinearEquiv

/-- The underlying R-linear round trip preserves the specified X-endomorphisms. -/
theorem polynomialRoundTripLinear_intertwines (M : ModuleCat.{v} R[X])
    (x : ((fromPolynomial R).obj ((toPolynomial R).obj ((fromPolynomial R).obj M))).a) :
    polynomialRoundTripLinear R M
      (((fromPolynomial R).obj ((toPolynomial R).obj ((fromPolynomial R).obj M))).str x) =
        ((fromPolynomial R).obj M).str (polynomialRoundTripLinear R M x) :=
  (polynomialRoundTrip R M).hom.hom.map_smul (X : R[X]) x

/-- The evaluation module, restricted along constants, has the original R-module as carrier. -/
def endomorphismRoundTripLinear (A : EndomorphismCat.{u, v} R) :
    ((fromPolynomial R).obj ((toPolynomial R).obj A)).a ≃ₗ[R] A.a where
  toFun := (Module.AEval'.of (endomorphism R A)).symm
  invFun := Module.AEval'.of (endomorphism R A)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (Module.AEval'.of (endomorphism R A)).symm
      (C r • (show Module.AEval' (endomorphism R A) from x)) =
      r • (Module.AEval'.of (endomorphism R A)).symm x
    rw [Module.AEval.C_smul, map_smul]

/-- The underlying R-linear round trip preserves the given endomorphism. -/
theorem endomorphismRoundTripLinear_intertwines (A : EndomorphismCat.{u, v} R)
    (x : ((fromPolynomial R).obj ((toPolynomial R).obj A)).a) :
    endomorphismRoundTripLinear R A
      (((fromPolynomial R).obj ((toPolynomial R).obj A)).str x) =
        A.str (endomorphismRoundTripLinear R A x) :=
  Module.AEval'.of_symm_X_smul (endomorphism R A) x

/-- The carrier identification intertwines the recovered X-action with the given endomorphism. -/
def endomorphismRoundTrip (A : EndomorphismCat.{u, v} R) :
    (fromPolynomial R).obj ((toPolynomial R).obj A) ≅ A :=
  Endofunctor.Algebra.isoMk (endomorphismRoundTripLinear R A).toModuleIso (by
    ext x
    exact (Module.AEval'.of_symm_X_smul (endomorphism R A) x).symm)

@[simp] theorem endomorphismRoundTrip_hom_apply (A : EndomorphismCat.{u, v} R)
    (x : ((fromPolynomial R).obj ((toPolynomial R).obj A)).a) :
    (endomorphismRoundTrip R A).hom.f x =
      (Module.AEval'.of (endomorphism R A)).symm x := rfl

@[simp] theorem endomorphismRoundTrip_inv_apply (A : EndomorphismCat.{u, v} R) (x : A.a) :
    (endomorphismRoundTrip R A).inv.f x =
      Module.AEval'.of (endomorphism R A) x := rfl

/-- The polynomial-module round trip is naturally isomorphic to the identity. -/
def unitIso : 𝟭 (ModuleCat.{v} R[X]) ≅ fromPolynomial R ⋙ toPolynomial R :=
  NatIso.ofComponents (fun M => (polynomialRoundTrip R M).symm) (fun _ => by ext x; rfl)

/-- The endomorphism round trip is naturally isomorphic to the identity. -/
def counitIso : toPolynomial R ⋙ fromPolynomial R ≅ 𝟭 (EndomorphismCat.{u, v} R) :=
  NatIso.ofComponents (endomorphismRoundTrip R) (fun _ => by ext x; rfl)

@[simp] theorem unitIso_hom_app_apply (M : ModuleCat.{v} R[X]) (x : M) :
    (unitIso R).hom.app M x = Module.AEval'.of (xAction R M).hom x := rfl

@[simp] theorem unitIso_inv_app_apply (M : ModuleCat.{v} R[X])
    (x : (toPolynomial R).obj ((fromPolynomial R).obj M)) :
    (unitIso R).inv.app M x = (Module.AEval'.of (xAction R M).hom).symm x := rfl

@[simp] theorem counitIso_hom_app_apply (A : EndomorphismCat.{u, v} R)
    (x : ((fromPolynomial R).obj ((toPolynomial R).obj A)).a) :
    ((counitIso R).hom.app A).f x = (Module.AEval'.of (endomorphism R A)).symm x := rfl

@[simp] theorem counitIso_inv_app_apply (A : EndomorphismCat.{u, v} R) (x : A.a) :
    ((counitIso R).inv.app A).f x = Module.AEval'.of (endomorphism R A) x := rfl

/-- Polynomial modules are equivalent to modules equipped with a linear endomorphism. -/
def equivalence : ModuleCat.{v} R[X] ≌ EndomorphismCat.{u, v} R where
  functor := fromPolynomial R
  inverse := toPolynomial R
  unitIso := unitIso R
  counitIso := counitIso R
  functor_unitIso_comp _ := by ext x; rfl

/-- Renard's equivalence for an arbitrary field and arbitrary module dimension. -/
abbrev fieldEquivalence (k : Type u) [Field k] :
    ModuleCat.{v} k[X] ≌ EndomorphismCat.{u, v} k :=
  equivalence k

end Langlands.Algebra.PolynomialEndomorphism
