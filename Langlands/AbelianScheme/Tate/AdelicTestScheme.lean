import Langlands.AbelianScheme.Tate.RationalTestScheme

/-! # Tensor-algebra-linear restriction and isomorphisms of actual test schemes -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate
variable {S : Scheme.{u}} (A : AbelianScheme S) {T T' T'' : Over S}
  (P : ℕ → Prop)

/-- Actual test-scheme restriction preserves the actual rational endomorphism action. -/
theorem rationalTestRestrict_endAction (a : T' ⟶ T) (f : Rationalization.End A)
    (x : Rational A T P) :
    rationalTestRestrict A P a (rationalEndAction A T P f x) =
      rationalEndAction A T' P f (rationalTestRestrict A P a x) :=
  rationalTestRestrict_homMap P a f x

variable {D : Type*} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Both commuting factors in the full tensor-algebra action preserve restriction. -/
theorem rationalTestRestrict_finiteAdeleAlgebraAction (a : T' ⟶ T)
    (r : D ⊗[ℚ] Global.FiniteAdeles ℚ) (x : Rational A T P) :
    rationalTestRestrict A P a (finiteAdeleAlgebraAction A T P h i r x) =
      finiteAdeleAlgebraAction A T' P h i r (rationalTestRestrict A P a x) := by
  induction r using TensorProduct.inductionOn with
  | tmul d r =>
    simp only [finiteAdeleAlgebraAction_tmul]
    rw [rationalTestRestrict_endAction,
      GroupScheme.Tate.rationalTestRestrict_finiteAdeleAction]
  | add r q hr hq => simp_all

/-- Contravariant restriction, linear for the actual full tensor-algebra action. -/
def finiteAdeleAlgebraTestRestrict (a : T' ⟶ T) :
    let := finiteAdeleAlgebraModule A T P h i
    let := finiteAdeleAlgebraModule A T' P h i
    Rational A T P →ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational A T' P := by
  let := finiteAdeleAlgebraModule A T P h i
  let := finiteAdeleAlgebraModule A T' P h i
  exact { (rationalTestRestrict A P a).toAddHom with
    map_smul' := rationalTestRestrict_finiteAdeleAlgebraAction A P i h a }

@[simp] theorem finiteAdeleAlgebraTestRestrict_apply (a : T' ⟶ T)
    (x : Rational A T P) :
    finiteAdeleAlgebraTestRestrict A P i h a x = rationalTestRestrict A P a x := rfl

@[simp] theorem finiteAdeleAlgebraTestRestrict_id (x : Rational A T P) :
    finiteAdeleAlgebraTestRestrict A P i h (𝟙 T) x = x :=
  LinearMap.congr_fun (GroupScheme.Tate.rationalTestRestrict_id A.toGrp P) x

/-- Restriction along a composite acts in the contravariant order. -/
theorem finiteAdeleAlgebraTestRestrict_comp (a : T' ⟶ T) (b : T'' ⟶ T')
    (x : Rational A T P) :
    finiteAdeleAlgebraTestRestrict A P i h (b ≫ a) x =
      finiteAdeleAlgebraTestRestrict A P i h b
        (finiteAdeleAlgebraTestRestrict A P i h a x) :=
  LinearMap.congr_fun (GroupScheme.Tate.rationalTestRestrict_comp A.toGrp P a b) x

/-- Transport along an actual test-scheme isomorphism uses restriction by its inverse. -/
def finiteAdeleAlgebraTestIso (e : T ≅ T') :
    let := finiteAdeleAlgebraModule A T P h i
    let := finiteAdeleAlgebraModule A T' P h i
    Rational A T P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational A T' P := by
  let := finiteAdeleAlgebraModule A T P h i
  let := finiteAdeleAlgebraModule A T' P h i
  exact {
    finiteAdeleAlgebraTestRestrict A P i h e.inv with
    invFun := finiteAdeleAlgebraTestRestrict A P i h e.hom
    left_inv := fun x => by
      change finiteAdeleAlgebraTestRestrict A P i h e.hom
        (finiteAdeleAlgebraTestRestrict A P i h e.inv x) = x
      rw [← finiteAdeleAlgebraTestRestrict_comp, e.hom_inv_id,
        finiteAdeleAlgebraTestRestrict_id]
    right_inv := fun x => by
      change finiteAdeleAlgebraTestRestrict A P i h e.inv
        (finiteAdeleAlgebraTestRestrict A P i h e.hom x) = x
      rw [← finiteAdeleAlgebraTestRestrict_comp, e.inv_hom_id,
        finiteAdeleAlgebraTestRestrict_id] }

@[simp] theorem finiteAdeleAlgebraTestIso_apply (e : T ≅ T') (x : Rational A T P) :
    finiteAdeleAlgebraTestIso A P i h e x = rationalTestRestrict A P e.inv x := rfl

@[simp] theorem finiteAdeleAlgebraTestIso_symm_apply (e : T ≅ T') (x : Rational A T' P) :
    (finiteAdeleAlgebraTestIso A P i h e).symm x = rationalTestRestrict A P e.hom x := rfl

@[simp] theorem finiteAdeleAlgebraTestIso_refl (x : Rational A T P) :
    finiteAdeleAlgebraTestIso A P i h (Iso.refl T) x = x :=
  finiteAdeleAlgebraTestRestrict_id A P i h x

/-- The inverse in the definition makes isomorphism transport covariant. -/
theorem finiteAdeleAlgebraTestIso_trans (e : T ≅ T') (f : T' ≅ T'')
    (x : Rational A T P) :
    finiteAdeleAlgebraTestIso A P i h (e.trans f) x =
      finiteAdeleAlgebraTestIso A P i h f (finiteAdeleAlgebraTestIso A P i h e x) :=
  finiteAdeleAlgebraTestRestrict_comp A P i h e.inv f.inv x

variable {h} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Both commuting factors in the away tensor-algebra action preserve restriction. -/
theorem rationalTestRestrict_primeToFiniteAdeleAlgebraAction (a : T' ⟶ T)
    (r : D ⊗[ℚ] Global.PrimeToFiniteAdeles m) (x : RationalAway A T m) :
    rationalTestRestrict A (fun n => Nat.Coprime n m) a (primeToFiniteAdeleAlgebraAction A T hAway i r x) =
      primeToFiniteAdeleAlgebraAction A T' hAway i r (rationalTestRestrict A (fun n => Nat.Coprime n m) a x) := by
  induction r using TensorProduct.inductionOn with
  | tmul d r =>
    simp only [primeToFiniteAdeleAlgebraAction_tmul]
    rw [rationalTestRestrict_endAction,
      GroupScheme.Tate.rationalTestRestrict_primeToFiniteAdeleAction]
  | add r q hr hq => simp_all

/-- Contravariant restriction, linear for the actual away tensor-algebra action. -/
def primeToFiniteAdeleAlgebraTestRestrict (a : T' ⟶ T) :
    let := primeToFiniteAdeleAlgebraModule A T hAway i
    let := primeToFiniteAdeleAlgebraModule A T' hAway i
    RationalAway A T m →ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAway A T' m := by
  let := primeToFiniteAdeleAlgebraModule A T hAway i
  let := primeToFiniteAdeleAlgebraModule A T' hAway i
  exact { (rationalTestRestrict A (fun n => Nat.Coprime n m) a).toAddHom with
    map_smul' := rationalTestRestrict_primeToFiniteAdeleAlgebraAction A i hAway a }

@[simp] theorem primeToFiniteAdeleAlgebraTestRestrict_apply (a : T' ⟶ T)
    (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestRestrict A i hAway a x = rationalTestRestrict A (fun n => Nat.Coprime n m) a x := rfl

@[simp] theorem primeToFiniteAdeleAlgebraTestRestrict_id (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestRestrict A i hAway (𝟙 T) x = x :=
  LinearMap.congr_fun (GroupScheme.Tate.rationalTestRestrict_id A.toGrp (fun n => Nat.Coprime n m)) x

/-- Restriction along a composite acts in the contravariant order. -/
theorem primeToFiniteAdeleAlgebraTestRestrict_comp (a : T' ⟶ T) (b : T'' ⟶ T')
    (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestRestrict A i hAway (b ≫ a) x =
      primeToFiniteAdeleAlgebraTestRestrict A i hAway b
        (primeToFiniteAdeleAlgebraTestRestrict A i hAway a x) :=
  LinearMap.congr_fun (GroupScheme.Tate.rationalTestRestrict_comp A.toGrp (fun n => Nat.Coprime n m) a b) x

/-- Transport along an actual test-scheme isomorphism uses restriction by its inverse. -/
def primeToFiniteAdeleAlgebraTestIso (e : T ≅ T') :
    let := primeToFiniteAdeleAlgebraModule A T hAway i
    let := primeToFiniteAdeleAlgebraModule A T' hAway i
    RationalAway A T m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAway A T' m := by
  let := primeToFiniteAdeleAlgebraModule A T hAway i
  let := primeToFiniteAdeleAlgebraModule A T' hAway i
  exact {
    primeToFiniteAdeleAlgebraTestRestrict A i hAway e.inv with
    invFun := primeToFiniteAdeleAlgebraTestRestrict A i hAway e.hom
    left_inv := fun x => by
      change primeToFiniteAdeleAlgebraTestRestrict A i hAway e.hom
        (primeToFiniteAdeleAlgebraTestRestrict A i hAway e.inv x) = x
      rw [← primeToFiniteAdeleAlgebraTestRestrict_comp, e.hom_inv_id,
        primeToFiniteAdeleAlgebraTestRestrict_id]
    right_inv := fun x => by
      change primeToFiniteAdeleAlgebraTestRestrict A i hAway e.inv
        (primeToFiniteAdeleAlgebraTestRestrict A i hAway e.hom x) = x
      rw [← primeToFiniteAdeleAlgebraTestRestrict_comp, e.inv_hom_id,
        primeToFiniteAdeleAlgebraTestRestrict_id] }

@[simp] theorem primeToFiniteAdeleAlgebraTestIso_apply (e : T ≅ T') (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestIso A i hAway e x = rationalTestRestrict A (fun n => Nat.Coprime n m) e.inv x := rfl

@[simp] theorem primeToFiniteAdeleAlgebraTestIso_symm_apply (e : T ≅ T') (x : RationalAway A T' m) :
    (primeToFiniteAdeleAlgebraTestIso A i hAway e).symm x = rationalTestRestrict A (fun n => Nat.Coprime n m) e.hom x := rfl

@[simp] theorem primeToFiniteAdeleAlgebraTestIso_refl (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestIso A i hAway (Iso.refl T) x = x :=
  primeToFiniteAdeleAlgebraTestRestrict_id A i hAway x

/-- The inverse in the definition makes isomorphism transport covariant. -/
theorem primeToFiniteAdeleAlgebraTestIso_trans (e : T ≅ T') (f : T' ≅ T'')
    (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraTestIso A i hAway (e.trans f) x =
      primeToFiniteAdeleAlgebraTestIso A i hAway f (primeToFiniteAdeleAlgebraTestIso A i hAway e x) :=
  primeToFiniteAdeleAlgebraTestRestrict_comp A i hAway e.inv f.inv x

end Langlands.AbelianScheme.Tate
