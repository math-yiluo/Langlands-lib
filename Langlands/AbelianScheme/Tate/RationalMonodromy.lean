import Langlands.AbelianScheme.Tate.IntegralMonodromy
import Langlands.AbelianScheme.Tate.AwayRationalScalars

/-! # Actual geometric monodromy on rational Tate modules -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- Extend the actual integral action to the existing rationalization. -/
def rationalMonodromyMap (g : FundamentalGroup s hfin) :
    Rational A (Over.mk s) P →ₗ[ℚ] Rational A (Over.mk s) P :=
  (integralMonodromyHom s hfin htor A P hu g).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalMonodromyMap_tmul (g : FundamentalGroup s hfin)
    (q : ℚ) (x : Integral A (Over.mk s) P) :
    rationalMonodromyMap s hfin htor A P hu g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s hfin htor A P hu g x := rfl

@[simp] theorem rationalMonodromyMap_one (x : Rational A (Over.mk s) P) :
    rationalMonodromyMap s hfin htor A P hu 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp
  | add x y hx hy => simp_all

theorem rationalMonodromyMap_mul (g h : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    rationalMonodromyMap s hfin htor A P hu (g * h) x =
      rationalMonodromyMap s hfin htor A P hu g
        (rationalMonodromyMap s hfin htor A P hu h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp [integralMonodromyHom_mul]
  | add x y hx hy => simp_all

/-- Rational geometric monodromy, with inverse given by the inverse group element. -/
def rationalMonodromy (g : FundamentalGroup s hfin) :
    Rational A (Over.mk s) P ≃ₗ[ℚ] Rational A (Over.mk s) P :=
  { rationalMonodromyMap s hfin htor A P hu g with
    invFun := rationalMonodromyMap s hfin htor A P hu g⁻¹
    left_inv := fun x => by
      change rationalMonodromyMap s hfin htor A P hu g⁻¹
        (rationalMonodromyMap s hfin htor A P hu g x) = x
      rw [← rationalMonodromyMap_mul, inv_mul_cancel, rationalMonodromyMap_one]
    right_inv := fun x => by
      change rationalMonodromyMap s hfin htor A P hu g
        (rationalMonodromyMap s hfin htor A P hu g⁻¹ x) = x
      rw [← rationalMonodromyMap_mul, mul_inv_cancel, rationalMonodromyMap_one] }

@[simp] theorem rationalMonodromy_apply (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g x =
      rationalMonodromyMap s hfin htor A P hu g x := rfl

/-- Locally installable action on the existing rational Tate carrier. -/
@[instance_reducible] def rationalMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Rational A (Over.mk s) P) where
  smul := fun g x => rationalMonodromyMap s hfin htor A P hu g x
  one_smul := rationalMonodromyMap_one s hfin htor A P hu
  mul_smul := rationalMonodromyMap_mul s hfin htor A P hu
  smul_zero g := map_zero (rationalMonodromyMap s hfin htor A P hu g)
  smul_add g := _root_.map_add (rationalMonodromyMap s hfin htor A P hu g)

/-- The integral-to-rational map intertwines the two actual geometric actions. -/
theorem toRational_monodromy (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) P) :
    GroupScheme.Tate.toRational A.toGrp (Over.mk s) P
        (integralMonodromy s hfin htor A P hu g x) =
      rationalMonodromy s hfin htor A P hu g
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) P x) := rfl

/-- Monodromy preserves the rationalized full residue scalar action. -/
theorem rationalMonodromy_scalarAction (g : FundamentalGroup s hfin)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g
        (GroupScheme.Tate.rationalScalarAction A.toGrp (Over.mk s) P a x) =
      GroupScheme.Tate.rationalScalarAction A.toGrp (Over.mk s) P a
        (rationalMonodromy s hfin htor A P hu g x) :=
  TateScalarExtension.map_action
    (integralMonodromyLinearEquiv s hfin htor A P hu g).toLinearMap a x

variable {A} {B : AbelianScheme S}

/-- The rational Tate map of an actual homomorphism is geometrically equivariant. -/
theorem rationalMonodromy_map (f : A ⟶ B) (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor B P hu g (rationalMap (Over.mk s) P f x) =
      rationalMap (Over.mk s) P f (rationalMonodromy s hfin htor A P hu g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralMonodromy s hfin htor B P hu g
      (map (Over.mk s) P f x) =
      q ⊗ₜ[ℤ] map (Over.mk s) P f (integralMonodromy s hfin htor A P hu g x)
    rw [integralMonodromy_map]
  | add x y hx hy => simp_all

/-- Equivariance extends to actual rational homomorphisms without a new hypothesis. -/
theorem rationalMonodromy_homMap (f : Rationalization.Hom A B)
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor B P hu g (rationalHomMap (Over.mk s) P f x) =
      rationalHomMap (Over.mk s) P f (rationalMonodromy s hfin htor A P hu g x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalHomMap_tmul, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => q • y) (rationalMonodromy_map s hfin htor P hu f g x)
  | add f f' hf hf' => simp_all

/-- Invertible rational homomorphisms transport the actual geometric action. -/
theorem rationalMonodromy_iso (e : Rationalization.of A ≅ Rationalization.of B)
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor B P hu g (rationalIso (Over.mk s) P e x) =
      rationalIso (Over.mk s) P e (rationalMonodromy s hfin htor A P hu g x) :=
  rationalMonodromy_homMap s hfin htor P hu e.hom g x

variable (A)

/-- The rational endomorphism action commutes with actual geometric monodromy. -/
theorem rationalMonodromy_endAction (f : Rationalization.End A)
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g (rationalEndAction A (Over.mk s) P f x) =
      rationalEndAction A (Over.mk s) P f (rationalMonodromy s hfin htor A P hu g x) :=
  rationalMonodromy_homMap s hfin htor P hu f g x

/-- Any action through actual rational endomorphisms commutes with monodromy. -/
theorem rationalMonodromy_algebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (d : D) (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g (algebraAction A (Over.mk s) P i d x) =
      algebraAction A (Over.mk s) P i d (rationalMonodromy s hfin htor A P hu g x) :=
  rationalMonodromy_endAction s hfin htor A P hu (i d) g x

/-- The actual action as a homomorphism to rational linear automorphisms. -/
def rationalMonodromyRepresentation :
    FundamentalGroup s hfin →* (Rational A (Over.mk s) P ≃ₗ[ℚ] Rational A (Over.mk s) P) where
  toFun := rationalMonodromy s hfin htor A P hu
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact rationalMonodromyMap_one s hfin htor A P hu x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact rationalMonodromyMap_mul s hfin htor A P hu g h x

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Actual monodromy preserves the finite-adelic scalar action. -/
theorem rationalMonodromy_finiteAdeleAction (g : FundamentalGroup s hfin)
    (a : Global.FiniteAdeles ℚ) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g (finiteAdeleAction A (Over.mk s) P h a x) =
      finiteAdeleAction A (Over.mk s) P h a (rationalMonodromy s hfin htor A P hu g x) :=
  rationalMonodromy_scalarAction s hfin htor A P hu g _ x

/-- The same geometric action bundled over the constructed finite-adelic module. -/
def finiteAdeleMonodromy (g : FundamentalGroup s hfin) :
    let := finiteAdeleModule A (Over.mk s) P h
    Rational A (Over.mk s) P ≃ₗ[Global.FiniteAdeles ℚ] Rational A (Over.mk s) P := by
  let := finiteAdeleModule A (Over.mk s) P h
  exact { (rationalMonodromy s hfin htor A P hu g).toEquiv with
    map_add' := (rationalMonodromy s hfin htor A P hu g).map_add
    map_smul' := rationalMonodromy_finiteAdeleAction s hfin htor A P hu h g }

@[simp] theorem finiteAdeleMonodromy_apply (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    finiteAdeleMonodromy s hfin htor A P hu h g x =
      rationalMonodromy s hfin htor A P hu g x := rfl

/-- Monodromy preserves the actual endomorphism/finite-adele tensor algebra action. -/
theorem rationalMonodromy_finiteAdeleAlgebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (a : D ⊗[ℚ] Global.FiniteAdeles ℚ)
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalMonodromy s hfin htor A P hu g (finiteAdeleAlgebraAction A (Over.mk s) P h i a x) =
      finiteAdeleAlgebraAction A (Over.mk s) P h i a
        (rationalMonodromy s hfin htor A P hu g x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [finiteAdeleAlgebraAction_tmul, finiteAdeleAlgebraAction_tmul,
      rationalMonodromy_endAction, rationalMonodromy_finiteAdeleAction]
  | add a b ha hb => simp_all

/-- Monodromy is linear over the tensor algebra used by PEL level structures. -/
def finiteAdeleAlgebraMonodromy {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (g : FundamentalGroup s hfin) :
    let := finiteAdeleAlgebraModule A (Over.mk s) P h i
    Rational A (Over.mk s) P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational A (Over.mk s) P := by
  let := finiteAdeleAlgebraModule A (Over.mk s) P h i
  exact { (rationalMonodromy s hfin htor A P hu g).toEquiv with
    map_add' := (rationalMonodromy s hfin htor A P hu g).map_add
    map_smul' := fun a x => rationalMonodromy_finiteAdeleAlgebraAction
      s hfin htor A P hu h i a g x }

@[simp] theorem finiteAdeleAlgebraMonodromy_apply {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) P) :
    finiteAdeleAlgebraMonodromy s hfin htor A P hu h i g x =
      rationalMonodromy s hfin htor A P hu g x := rfl

/-- The PEL tensor-linear automorphisms form the actual geometric representation. -/
def finiteAdeleAlgebraMonodromyRepresentation {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    let := finiteAdeleAlgebraModule A (Over.mk s) P h i
    FundamentalGroup s hfin →*
      (Rational A (Over.mk s) P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ]
        Rational A (Over.mk s) P) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) P h i
  exact {
    toFun := finiteAdeleAlgebraMonodromy s hfin htor A P hu h i
    map_one' := LinearEquiv.ext (rationalMonodromyMap_one s hfin htor A P hu)
    map_mul' := fun g k => LinearEquiv.ext (rationalMonodromyMap_mul s hfin htor A P hu g k) }

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- Full rational geometric monodromy. -/
abbrev rationalFullMonodromy
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) :
    RationalFull A (Over.mk s) ≃ₗ[ℚ] RationalFull A (Over.mk s) :=
  rationalMonodromy s hfin htor A (fun _ => True) hu g

/-- Prime-to-modulus rational geometric monodromy. -/
abbrev rationalAwayMonodromy (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) :
    RationalAway A (Over.mk s) m ≃ₗ[ℚ] RationalAway A (Over.mk s) m :=
  rationalMonodromy s hfin htor A (fun n => Nat.Coprime n m) hu g

/-- Rationalized full-to-away restriction intertwines the actual geometric actions. -/
theorem rationalRestrictAway_monodromy (m : ℕ)
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : RationalFull A (Over.mk s)) :
    GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk s) m
        (rationalFullMonodromy s hfin htor A hu g x) =
      rationalAwayMonodromy s hfin htor A m
        (fun n => hu ⟨n.val, n.property.1, trivial⟩) g
        (GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk s) m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

variable (m : ℕ)
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- Away geometric monodromy preserves rationalized away residue scalars. -/
theorem rationalAwayMonodromy_scalarAction (g : FundamentalGroup s hfin)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : RationalAway A (Over.mk s) m) :
    rationalAwayMonodromy s hfin htor A m hu g
        (GroupScheme.Tate.rationalAwayScalarAction A.toGrp (Over.mk s) m a x) =
      GroupScheme.Tate.rationalAwayScalarAction A.toGrp (Over.mk s) m a
        (rationalAwayMonodromy s hfin htor A m hu g x) :=
  TateScalarExtension.map_action
    (awayMonodromyLinearEquiv s hfin htor A m hu g).toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Away geometric monodromy preserves the constructed away finite-adelic action. -/
theorem rationalAwayMonodromy_primeToFiniteAdeleAction (g : FundamentalGroup s hfin)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway A (Over.mk s) m) :
    rationalAwayMonodromy s hfin htor A m hu g
        (primeToFiniteAdeleAction A (Over.mk s) hAway a x) =
      primeToFiniteAdeleAction A (Over.mk s) hAway a
        (rationalAwayMonodromy s hfin htor A m hu g x) :=
  rationalAwayMonodromy_scalarAction s hfin htor A m hu g _ x

/-- The same away geometric action bundled over the away finite-adeles. -/
def primeToFiniteAdeleMonodromy (g : FundamentalGroup s hfin) :
    let := primeToFiniteAdeleModule A (Over.mk s) hAway
    RationalAway A (Over.mk s) m ≃ₗ[Global.PrimeToFiniteAdeles m]
      RationalAway A (Over.mk s) m := by
  let := primeToFiniteAdeleModule A (Over.mk s) hAway
  exact { (rationalAwayMonodromy s hfin htor A m hu g).toEquiv with
    map_add' := (rationalAwayMonodromy s hfin htor A m hu g).map_add
    map_smul' := rationalAwayMonodromy_primeToFiniteAdeleAction s hfin htor A m hu hAway g }

@[simp] theorem primeToFiniteAdeleMonodromy_apply (g : FundamentalGroup s hfin)
    (x : RationalAway A (Over.mk s) m) :
    primeToFiniteAdeleMonodromy s hfin htor A m hu hAway g x =
      rationalAwayMonodromy s hfin htor A m hu g x := rfl

/-- Away monodromy preserves the tensor action of actual endomorphisms and away adeles. -/
theorem rationalAwayMonodromy_primeToFiniteAdeleAlgebraAction
    {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (a : D ⊗[ℚ] Global.PrimeToFiniteAdeles m)
    (g : FundamentalGroup s hfin) (x : RationalAway A (Over.mk s) m) :
    rationalAwayMonodromy s hfin htor A m hu g
        (primeToFiniteAdeleAlgebraAction A (Over.mk s) hAway i a x) =
      primeToFiniteAdeleAlgebraAction A (Over.mk s) hAway i a
        (rationalAwayMonodromy s hfin htor A m hu g x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [primeToFiniteAdeleAlgebraAction_tmul, primeToFiniteAdeleAlgebraAction_tmul,
      rationalMonodromy_endAction, rationalAwayMonodromy_primeToFiniteAdeleAction]
  | add a b ha hb => simp_all

/-- Away monodromy as an equivalence over the PEL tensor algebra. -/
def primeToFiniteAdeleAlgebraMonodromy {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (g : FundamentalGroup s hfin) :
    let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
    RationalAway A (Over.mk s) m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
      RationalAway A (Over.mk s) m := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact { (rationalAwayMonodromy s hfin htor A m hu g).toEquiv with
    map_add' := (rationalAwayMonodromy s hfin htor A m hu g).map_add
    map_smul' := fun a x => rationalAwayMonodromy_primeToFiniteAdeleAlgebraAction
      s hfin htor A m hu hAway i a g x }

@[simp] theorem primeToFiniteAdeleAlgebraMonodromy_apply
    {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (g : FundamentalGroup s hfin)
    (x : RationalAway A (Over.mk s) m) :
    primeToFiniteAdeleAlgebraMonodromy s hfin htor A m hu hAway i g x =
      rationalAwayMonodromy s hfin htor A m hu g x := rfl

/-- The away PEL tensor-linear automorphisms form the geometric representation. -/
def primeToFiniteAdeleAlgebraMonodromyRepresentation {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
    FundamentalGroup s hfin →*
      (RationalAway A (Over.mk s) m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
        RationalAway A (Over.mk s) m) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact {
    toFun := primeToFiniteAdeleAlgebraMonodromy s hfin htor A m hu hAway i
    map_one' := LinearEquiv.ext
      (rationalMonodromyMap_one s hfin htor A (fun n => Nat.Coprime n m) hu)
    map_mul' := fun g k => LinearEquiv.ext
      (rationalMonodromyMap_mul s hfin htor A (fun n => Nat.Coprime n m) hu g k) }

end Langlands.AbelianScheme.Tate
