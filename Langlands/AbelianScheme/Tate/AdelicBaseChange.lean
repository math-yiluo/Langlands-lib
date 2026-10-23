import Langlands.AbelianScheme.Tate.RationalBaseChange
import Langlands.AbelianScheme.RationalBaseChange

/-! # Actual rational endomorphism and adelic algebra compatibility of base change -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S') (P : ℕ → Prop)
  {A B : AbelianScheme S}

/-- Actual rational Hom pullback commutes with the rational Tate comparison. -/
theorem rationalBaseChange_homMap (f : Hom0 A B)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b B T P
        (rationalHomMap T P (AbelianScheme.rationalBaseChangeHom b f) x) =
      rationalHomMap ((Over.map b).obj T) P f (rationalBaseChange b A T P x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [AbelianScheme.rationalBaseChangeHom_tmul, rationalHomMap_tmul,
      LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => q • y) (rationalBaseChange_map b T P f x)
  | add f g hf hg => simp_all

/-- Invertible rational homomorphisms give the same base-change square. -/
theorem rationalBaseChange_iso (e : Rationalization.of A ≅ Rationalization.of B)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b B T P
        (rationalIso T P (AbelianScheme.rationalBaseChangeIso b e) x) =
      rationalIso ((Over.map b).obj T) P e (rationalBaseChange b A T P x) :=
  rationalBaseChange_homMap b T P e.hom x

variable (A)

/-- The constructed rational endomorphism action commutes with actual pullback. -/
theorem rationalBaseChange_endAction (f : End0 A)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b A T P
        (rationalEndAction ((AbelianScheme.baseChange b).obj A) T P
          (AbelianScheme.rationalBaseChangeEnd b A f) x) =
      rationalEndAction A ((Over.map b).obj T) P f (rationalBaseChange b A T P x) :=
  rationalBaseChange_homMap b T P f x

variable {D : Type*} [Ring D] [Algebra ℚ D]
  (i : D →ₐ[ℚ] End0 A)

/-- Pulling back an actual rational endomorphism-algebra action preserves Tate actions. -/
theorem rationalBaseChange_algebraAction (d : D)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b A T P
        (algebraAction ((AbelianScheme.baseChange b).obj A) T P
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) d x) =
      algebraAction A ((Over.map b).obj T) P i d (rationalBaseChange b A T P x) :=
  rationalBaseChange_endAction b T P A (i d) x

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The same full finite-adelic scalars act compatibly with actual base change. -/
theorem rationalBaseChange_finiteAdeleAction (a : Global.FiniteAdeles ℚ)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b A T P
        (finiteAdeleAction ((AbelianScheme.baseChange b).obj A) T P h a x) =
      finiteAdeleAction A ((Over.map b).obj T) P h a (rationalBaseChange b A T P x) :=
  GroupScheme.Tate.rationalBaseChange_finiteAdeleAction b A.toGrp T P h a x

/-- Base change preserves the constructed endomorphism/finite-adele tensor action. -/
theorem rationalBaseChange_finiteAdeleAlgebraAction
    (a : D ⊗[ℚ] Global.FiniteAdeles ℚ)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b A T P
        (finiteAdeleAlgebraAction ((AbelianScheme.baseChange b).obj A) T P h
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) a x) =
      finiteAdeleAlgebraAction A ((Over.map b).obj T) P h i a
        (rationalBaseChange b A T P x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    simp only [finiteAdeleAlgebraAction_tmul, AlgHom.comp_apply]
    rw [rationalBaseChange_endAction, rationalBaseChange_finiteAdeleAction]
  | add a c ha hc => simp_all

/-- The actual pullback comparison is linear over the full PEL tensor algebra. -/
def finiteAdeleAlgebraBaseChange :
    let := finiteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A) T P h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
    let := finiteAdeleAlgebraModule A ((Over.map b).obj T) P h i
    Rational ((AbelianScheme.baseChange b).obj A) T P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ]
      Rational A ((Over.map b).obj T) P := by
  let := finiteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A) T P h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
  let := finiteAdeleAlgebraModule A ((Over.map b).obj T) P h i
  exact { (rationalBaseChange b A T P).toEquiv with
    map_add' := (rationalBaseChange b A T P).map_add
    map_smul' := rationalBaseChange_finiteAdeleAlgebraAction b T P A i h }

@[simp] theorem finiteAdeleAlgebraBaseChange_apply
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    finiteAdeleAlgebraBaseChange b T P A i h x = rationalBaseChange b A T P x := rfl

@[simp] theorem finiteAdeleAlgebraBaseChange_symm_apply
    (x : Rational A ((Over.map b).obj T) P) :
    (finiteAdeleAlgebraBaseChange b T P A i h).symm x =
      (rationalBaseChange b A T P).symm x := rfl

variable {h} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The same coupled away scalar comparison is used on both sides of base change. -/
theorem rationalBaseChange_primeToFiniteAdeleAction
    (a : Global.PrimeToFiniteAdeles m)
    (x : RationalAway ((AbelianScheme.baseChange b).obj A) T m) :
    rationalBaseChange b A T (fun n => Nat.Coprime n m)
        (primeToFiniteAdeleAction ((AbelianScheme.baseChange b).obj A) T hAway a x) =
      primeToFiniteAdeleAction A ((Over.map b).obj T) hAway a
        (rationalBaseChange b A T (fun n => Nat.Coprime n m) x) :=
  GroupScheme.Tate.rationalBaseChange_primeToFiniteAdeleAction b A.toGrp T hAway a x

/-- Away base change preserves the actual endomorphism/away-adele tensor action. -/
theorem rationalBaseChange_primeToFiniteAdeleAlgebraAction
    (a : D ⊗[ℚ] Global.PrimeToFiniteAdeles m)
    (x : RationalAway ((AbelianScheme.baseChange b).obj A) T m) :
    rationalBaseChange b A T (fun n => Nat.Coprime n m)
        (primeToFiniteAdeleAlgebraAction ((AbelianScheme.baseChange b).obj A) T hAway
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) a x) =
      primeToFiniteAdeleAlgebraAction A ((Over.map b).obj T) hAway i a
        (rationalBaseChange b A T (fun n => Nat.Coprime n m) x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    simp only [primeToFiniteAdeleAlgebraAction_tmul, AlgHom.comp_apply]
    rw [rationalBaseChange_endAction, rationalBaseChange_primeToFiniteAdeleAction]
  | add a c ha hc => simp_all

/-- The actual away pullback comparison is linear over the away PEL tensor algebra. -/
def primeToFiniteAdeleAlgebraBaseChange :
    let := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A) T hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
    let := primeToFiniteAdeleAlgebraModule A ((Over.map b).obj T) hAway i
    RationalAway ((AbelianScheme.baseChange b).obj A) T m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
      RationalAway A ((Over.map b).obj T) m := by
  let := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A) T hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
  let := primeToFiniteAdeleAlgebraModule A ((Over.map b).obj T) hAway i
  exact { (rationalBaseChange b A T (fun n => Nat.Coprime n m)).toEquiv with
    map_add' := (rationalBaseChange b A T (fun n => Nat.Coprime n m)).map_add
    map_smul' := rationalBaseChange_primeToFiniteAdeleAlgebraAction b T A i hAway }

@[simp] theorem primeToFiniteAdeleAlgebraBaseChange_apply
    (x : RationalAway ((AbelianScheme.baseChange b).obj A) T m) :
    primeToFiniteAdeleAlgebraBaseChange b T A i hAway x =
      rationalBaseChange b A T (fun n => Nat.Coprime n m) x := rfl

@[simp] theorem primeToFiniteAdeleAlgebraBaseChange_symm_apply
    (x : RationalAway A ((Over.map b).obj T) m) :
    (primeToFiniteAdeleAlgebraBaseChange b T A i hAway).symm x =
      (rationalBaseChange b A T (fun n => Nat.Coprime n m)).symm x := rfl

/-- Full-to-away restriction commutes with these same underlying tensor-linear maps. -/
theorem finiteAdeleAlgebraBaseChange_restrictAway
    (x : RationalFull ((AbelianScheme.baseChange b).obj A) T) :
    GroupScheme.Tate.rationalRestrictAway A.toGrp ((Over.map b).obj T) m
        (finiteAdeleAlgebraBaseChange b T (fun _ => True) A i h x) =
      primeToFiniteAdeleAlgebraBaseChange b T A i hAway
        (GroupScheme.Tate.rationalRestrictAway
          ((AbelianScheme.baseChange b).obj A).toGrp T m x) :=
  (GroupScheme.Tate.rationalBaseChange_restrictAway b A.toGrp T m x).symm

end Langlands.AbelianScheme.Tate
