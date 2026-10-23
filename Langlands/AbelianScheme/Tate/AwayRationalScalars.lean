import Langlands.AbelianScheme.Tate.RationalScalars
import Langlands.Global.PrimeToRationalProfiniteIntegerComparison

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The away integral witness chosen from the explicit comparison hypothesis. -/
def integralEquiv : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m :=
  hAway.choose

/-- The rational away witness coupled to the same integral witness. -/
def rationalEquiv : (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) ≃ₐ[ℚ] PrimeToFiniteAdeles m :=
  hAway.choose_spec.2.2.2.2.choose

@[simp] theorem rationalEquiv_tmul (q : ℚ) (a : PrimeToProfiniteIntegerRing m) :
    rationalEquiv hAway (q ⊗ₜ[ℤ] a) = algebraMap ℚ (PrimeToFiniteAdeles m) q *
      (integralEquiv hAway a : PrimeToFiniteAdeles m) :=
  hAway.choose_spec.2.2.2.2.choose_spec.1 q a

theorem integralEquiv_restrict (a : ProfiniteIntegerRing) :
    integralEquiv hAway (PrimeToProfiniteIntegerRing.restrict m a) =
      primeToIntegralRestriction m
        (RationalProfiniteIntegerAdeleComparison.integralEquiv h a) :=
  hAway.choose_spec.2.2.2.1 a

/-- The assumed pure-tensor square extends to every rational scalar. -/
theorem rationalEquiv_restrict (a : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
    rationalEquiv hAway (GroupScheme.Tate.rationalScalarRestrictAway m a) =
      primeToFiniteRestriction m (RationalProfiniteIntegerAdeleComparison.rationalEquiv h a) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a => exact hAway.choose_spec.2.2.2.2.choose_spec.2 q a
  | add a b ha hb => simp_all

/-- The inverse comparison square used to transport the full scalar action. -/
theorem rationalEquiv_symm_restrict (a : FiniteAdeles ℚ) :
    (rationalEquiv hAway).symm (primeToFiniteRestriction m a) =
      GroupScheme.Tate.rationalScalarRestrictAway m
        ((RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm a) := by
  apply (rationalEquiv hAway).injective
  rw [AlgEquiv.apply_symm_apply, rationalEquiv_restrict, AlgEquiv.apply_symm_apply]

end Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Actual away rational Tate scalars, transported along the explicit comparison. -/
def primeToFiniteAdeleAction :
    Global.PrimeToFiniteAdeles m →ₐ[ℚ] Module.End ℚ (RationalAway G T m) :=
  (rationalAwayScalarAction G T m).comp
    (Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm.toAlgHom

@[instance_reducible] def primeToFiniteAdeleModule :
    Module (Global.PrimeToFiniteAdeles m) (RationalAway G T m) :=
  Module.compHom _ (primeToFiniteAdeleAction G T hAway).toRingHom

@[simp] theorem primeToFiniteAdeleAction_diagonal (q : ℚ) (x : RationalAway G T m) :
    primeToFiniteAdeleAction G T hAway (algebraMap ℚ (Global.PrimeToFiniteAdeles m) q) x =
      q • x := by
  rw [AlgHom.commutes]
  rfl

theorem primeToFiniteAdeleModule_smul (a : Global.PrimeToFiniteAdeles m)
    (x : RationalAway G T m) :
    let := primeToFiniteAdeleModule G T hAway
    a • x = primeToFiniteAdeleAction G T hAway a x := rfl

theorem primeToFiniteAdeleModule_scalarTower :
    let := primeToFiniteAdeleModule G T hAway
    IsScalarTower ℚ (Global.PrimeToFiniteAdeles m) (RationalAway G T m) := by
  let := primeToFiniteAdeleModule G T hAway
  exact IsScalarTower.of_algebraMap_smul (primeToFiniteAdeleAction_diagonal G T hAway)

/-- Normalization recovers the actual integral away residue action. -/
theorem primeToFiniteAdeleAction_integral_tmul
    (a : Global.PrimeToProfiniteIntegerRing m) (r : ℚ) (x : Away G T m) :
    primeToFiniteAdeleAction G T hAway
      (Global.PrimeToRationalProfiniteIntegerAdeleComparison.integralEquiv hAway a)
      (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] (a • x) := by
  have he := Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul hAway 1 a
  simp only [map_one, one_mul] at he
  change TateScalarExtension.action _ _
    ((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm _) _ = _
  rw [← he, AlgEquiv.symm_apply_apply, TateScalarExtension.action_tmul, one_mul]

/-- Full-to-away Tate restriction respects the corresponding adelic restriction. -/
theorem rationalRestrictAway_finiteAdeleAction (a : Global.FiniteAdeles ℚ)
    (x : RationalFull G T) :
    rationalRestrictAway G T m (finiteAdeleAction G T (fun _ => True) h a x) =
      primeToFiniteAdeleAction G T hAway (Global.primeToFiniteRestriction m a)
        (rationalRestrictAway G T m x) := by
  change rationalRestrictAway G T m
    (rationalScalarAction G T _
      ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm a) x) =
    rationalAwayScalarAction G T m
      ((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm _)
      (rationalRestrictAway G T m x)
  rw [rationalRestrictAway_scalarAction,
    Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_symm_restrict]

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

theorem rationalMap_primeToFiniteAdeleAction (f : G ⟶ H)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway G T m) :
    rationalMap T _ f (primeToFiniteAdeleAction G T hAway a x) =
      primeToFiniteAdeleAction H T hAway a (rationalMap T _ f x) :=
  rationalMap_awayScalarAction T m f _ _

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Prime-to-modulus finite-adelic scalar action on the rational Tate module of an actual abelian scheme. -/
abbrev primeToFiniteAdeleAction : Global.PrimeToFiniteAdeles m →ₐ[ℚ] Module.End ℚ (RationalAway A T m) :=
  GroupScheme.Tate.primeToFiniteAdeleAction A.toGrp T hAway

/-- Its module structure, with an explicit comparison assumption. -/
@[instance_reducible] def primeToFiniteAdeleModule :
    Module (Global.PrimeToFiniteAdeles m) (RationalAway A T m) :=
  GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway

variable {A} {B : AbelianScheme S}

/-- Scalar compatibility extends to the existing rational homomorphism maps. -/
theorem rationalHomMap_primeToFiniteAdeleAction (f : Rationalization.Hom A B)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway A T m) :
    rationalHomMap T (fun n => Nat.Coprime n m) f (primeToFiniteAdeleAction A T hAway a x) =
      primeToFiniteAdeleAction B T hAway a (rationalHomMap T (fun n => Nat.Coprime n m) f x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalHomMap_tmul, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => q • y)
      (GroupScheme.Tate.rationalMap_primeToFiniteAdeleAction T hAway (AbelianScheme.groupHom f) a x)
  | add f g hf hg => simp_all

/-- The actual rational homomorphism map, bundled as prime-to-modulus finite-adelic linear. -/
def primeToFiniteAdeleHomMap (f : Rationalization.Hom A B) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    RationalAway A T m →ₗ[Global.PrimeToFiniteAdeles m] RationalAway B T m := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  exact { (rationalHomMap T (fun n => Nat.Coprime n m) f).toAddHom with
    map_smul' := rationalHomMap_primeToFiniteAdeleAction T hAway f }

@[simp] theorem primeToFiniteAdeleHomMap_apply (f : Rationalization.Hom A B)
    (x : RationalAway A T m) :
    primeToFiniteAdeleHomMap T hAway f x = rationalHomMap T (fun n => Nat.Coprime n m) f x := rfl

@[simp] theorem primeToFiniteAdeleHomMap_identity :
    let := primeToFiniteAdeleModule A T hAway
    primeToFiniteAdeleHomMap T hAway (Rationalization.identity A) = LinearMap.id := by
  let := primeToFiniteAdeleModule A T hAway
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T (fun n => Nat.Coprime n m)) x

theorem primeToFiniteAdeleHomMap_comp {C : AbelianScheme S}
    (f : Rationalization.Hom A B) (g : Rationalization.Hom B C) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    let := primeToFiniteAdeleModule C T hAway
    primeToFiniteAdeleHomMap T hAway (Rationalization.comp A B C f g) =
      (primeToFiniteAdeleHomMap T hAway g).comp (primeToFiniteAdeleHomMap T hAway f) := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  let := primeToFiniteAdeleModule C T hAway
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T (fun n => Nat.Coprime n m) f g) x

theorem primeToFiniteAdeleHomMap_add (f g : Rationalization.Hom A B) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    primeToFiniteAdeleHomMap T hAway (f + g) =
      primeToFiniteAdeleHomMap T hAway f + primeToFiniteAdeleHomMap T hAway g := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun ((rationalHomMap T (fun n => Nat.Coprime n m)).map_add f g) x

variable (A)

/-- The rational endomorphism action commutes with prime-to-modulus finite-adelic scalars. -/
theorem rationalEndAction_primeTo_commute (f : Rationalization.End A) (a : Global.PrimeToFiniteAdeles m) :
    Commute (rationalEndAction A T (fun n => Nat.Coprime n m) f) (primeToFiniteAdeleAction A T hAway a) := by
  apply LinearMap.ext
  intro x
  exact rationalHomMap_primeToFiniteAdeleAction T hAway f a x

/-- The required B tensor_Q A_f away from the modulus action comes from actual rational endomorphisms. -/
def primeToFiniteAdeleAlgebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) →ₐ[ℚ] Module.End ℚ (RationalAway A T m) :=
  Algebra.TensorProduct.lift (algebraAction A T (fun n => Nat.Coprime n m) i) (primeToFiniteAdeleAction A T hAway)
    (fun d a => rationalEndAction_primeTo_commute A T hAway (i d) a)

@[simp] theorem primeToFiniteAdeleAlgebraAction_tmul {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (d : D) (a : Global.PrimeToFiniteAdeles m)
    (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraAction A T hAway i (d ⊗ₜ[ℚ] a) x =
      rationalEndAction A T (fun n => Nat.Coprime n m) (i d) (primeToFiniteAdeleAction A T hAway a x) := rfl

/-- Module structure for the constructed B tensor_Q A_f away from the modulus action. -/
@[instance_reducible] def primeToFiniteAdeleAlgebraModule {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) (RationalAway A T m) :=
  Module.compHom _ (primeToFiniteAdeleAlgebraAction A T hAway i).toRingHom

end Langlands.AbelianScheme.Tate
