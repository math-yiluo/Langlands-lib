import Langlands.AbelianScheme.Tate.TwistRationalScalars
import Langlands.AbelianScheme.Tate.AwayRationalScalars

/-! # Away finite-adelic scalars on actual roots-of-unity twists -/

noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist.Divisibility

universe u v w
variable (R : Type u) [CommRing R]
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Away finite-adelic scalars act through the explicitly assumed comparison. -/
def primeToFiniteAdeleAction :
    Global.PrimeToFiniteAdeles m →ₐ[ℚ] Module.End ℚ (RationalAway R m) :=
  (rationalAwayScalarAction R m).comp
    (Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm.toAlgHom

/-- The module structure uses the same comparison as the action. -/
@[instance_reducible] def primeToFiniteAdeleModule :
    Module (Global.PrimeToFiniteAdeles m) (RationalAway R m) :=
  Module.compHom _ (primeToFiniteAdeleAction R hAway).toRingHom

@[simp] theorem primeToFiniteAdeleAction_diagonal (q : ℚ) (x : RationalAway R m) :
    primeToFiniteAdeleAction R hAway (algebraMap ℚ (Global.PrimeToFiniteAdeles m) q) x =
      q • x := by
  rw [AlgHom.commutes]
  rfl

theorem primeToFiniteAdeleModule_smul (a : Global.PrimeToFiniteAdeles m)
    (x : RationalAway R m) :
    let := primeToFiniteAdeleModule R hAway
    a • x = primeToFiniteAdeleAction R hAway a x := rfl

theorem primeToFiniteAdeleModule_scalarTower :
    let := primeToFiniteAdeleModule R hAway
    IsScalarTower ℚ (Global.PrimeToFiniteAdeles m) (RationalAway R m) := by
  let := primeToFiniteAdeleModule R hAway
  exact IsScalarTower.of_algebraMap_smul (primeToFiniteAdeleAction_diagonal R hAway)

/-- The coupled integral comparison recovers the actual away residue action on roots. -/
theorem primeToFiniteAdeleAction_integral_tmul
    (a : Global.PrimeToProfiniteIntegerRing m) (q : ℚ) (x : Away R m) :
    primeToFiniteAdeleAction R hAway
      (Global.PrimeToRationalProfiniteIntegerAdeleComparison.integralEquiv hAway a)
      (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (a • x) := by
  have he := Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul hAway 1 a
  simp only [map_one, one_mul] at he
  change TateScalarExtension.action _ _
    ((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm _) _ = _
  rw [← he, AlgEquiv.symm_apply_apply, TateScalarExtension.action_tmul, one_mul]

/-- On the away twist, the full action factors through restriction of finite adeles. -/
theorem finiteAdeleAction_eq_away (a : Global.FiniteAdeles ℚ) (x : RationalAway R m) :
    finiteAdeleAction R (fun n => Nat.Coprime n m) h a x =
      primeToFiniteAdeleAction R hAway (Global.primeToFiniteRestriction m a) x := by
  change rationalScalarAction R _
    ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm a) x =
    rationalAwayScalarAction R m
      ((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm _) x
  rw [rationalScalarAction_eq_away,
    Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_symm_restrict]

/-- Restriction of the root limit intertwines the corresponding adelic actions. -/
theorem rationalRestrictAway_finiteAdeleAction (a : Global.FiniteAdeles ℚ)
    (x : RationalFull R) :
    rationalRestrictAway R m (finiteAdeleAction R (fun _ => True) h a x) =
      primeToFiniteAdeleAction R hAway (Global.primeToFiniteRestriction m a)
        (rationalRestrictAway R m x) := by
  change rationalRestrictAway R m
    (rationalScalarAction R _
      ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm a) x) =
    rationalAwayScalarAction R m
      ((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway).symm _)
      (rationalRestrictAway R m x)
  rw [rationalRestrictAway_scalarAction,
    Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_symm_restrict]

variable {R} {S : Type v} {T : Type w} [CommRing S] [CommRing T]

/-- Ring-induced maps preserve the away finite-adelic action. -/
theorem rationalMap_primeToFiniteAdeleAction (f : R →+* S)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway R m) :
    rationalMap _ f (primeToFiniteAdeleAction R hAway a x) =
      primeToFiniteAdeleAction S hAway a (rationalMap _ f x) :=
  rationalMap_awayScalarAction m f _ _

/-- The existing ring-induced map, bundled with its away finite-adelic linearity. -/
def primeToFiniteAdeleMap (f : R →+* S) :
    let := primeToFiniteAdeleModule R hAway
    let := primeToFiniteAdeleModule S hAway
    RationalAway R m →ₗ[Global.PrimeToFiniteAdeles m] RationalAway S m := by
  let := primeToFiniteAdeleModule R hAway
  let := primeToFiniteAdeleModule S hAway
  exact { (rationalMap (fun n => Nat.Coprime n m) f).toAddHom with
    map_smul' := rationalMap_primeToFiniteAdeleAction hAway f }

@[simp] theorem primeToFiniteAdeleMap_apply (f : R →+* S) (x : RationalAway R m) :
    primeToFiniteAdeleMap hAway f x = rationalMap (fun n => Nat.Coprime n m) f x := rfl

@[simp] theorem primeToFiniteAdeleMap_id :
    let := primeToFiniteAdeleModule R hAway
    primeToFiniteAdeleMap hAway (RingHom.id R) = LinearMap.id := by
  let := primeToFiniteAdeleModule R hAway
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalMap_id (fun n => Nat.Coprime n m)) x

theorem primeToFiniteAdeleMap_comp (f : R →+* S) (g : S →+* T) :
    let := primeToFiniteAdeleModule R hAway
    let := primeToFiniteAdeleModule S hAway
    let := primeToFiniteAdeleModule T hAway
    primeToFiniteAdeleMap hAway (g.comp f) =
      (primeToFiniteAdeleMap hAway g).comp (primeToFiniteAdeleMap hAway f) := by
  let := primeToFiniteAdeleModule R hAway
  let := primeToFiniteAdeleModule S hAway
  let := primeToFiniteAdeleModule T hAway
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalMap_comp (fun n => Nat.Coprime n m) f g) x

variable (R)

/-- Natural root automorphisms commute with away finite-adelic scalars. -/
theorem rationalAutomorphismAction_primeToFiniteAdeleAction (f : R ≃+* R)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway R m) :
    rationalAutomorphismAction R (fun n => Nat.Coprime n m) f
        (primeToFiniteAdeleAction R hAway a x) =
      primeToFiniteAdeleAction R hAway a
        (rationalAutomorphismAction R (fun n => Nat.Coprime n m) f x) :=
  rationalAutomorphismAction_awayScalarAction R m f _ _

section Galois
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The existing field-Galois action commutes with away finite-adelic scalars. -/
theorem rationalGaloisAction_primeToFiniteAdeleAction (σ : Gal(L/K))
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway L m) :
    rationalGaloisAction K L (fun n => Nat.Coprime n m) σ
        (primeToFiniteAdeleAction L hAway a x) =
      primeToFiniteAdeleAction L hAway a
        (rationalGaloisAction K L (fun n => Nat.Coprime n m) σ x) :=
  rationalGaloisAction_awayScalarAction K L m σ _ _

end Galois
end Langlands.TateTwist.Divisibility
