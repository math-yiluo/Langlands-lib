import Langlands.AbelianScheme.Tate.IntegralTransport
import Langlands.AbelianScheme.Tate.RationalMonodromy

/-! # Transport on actual rational Tate modules along a geometric path -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- Rational scalar extension of the actual integral path map. -/
def rationalTransportMap (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational A (Over.mk s) P →ₗ[ℚ] Rational A (Over.mk t) P :=
  (integralTransportHom htor A P hu p).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalTransportMap_tmul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : ℚ) (x : Integral A (Over.mk s) P) :
    rationalTransportMap htor A P hu p (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralTransport htor A P hu p x := rfl

@[simp] theorem rationalTransportMap_refl (x : Rational A (Over.mk s) P) :
    rationalTransportMap htor A P hu (Iso.refl (fiberFunctor s hs)) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp
  | add x y hx hy => simp_all

theorem rationalTransportMap_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational A (Over.mk s) P) :
    rationalTransportMap htor A P hu (p ≪≫ q) x =
      rationalTransportMap htor A P hu q (rationalTransportMap htor A P hu p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp [integralTransport_trans]
  | add x y hx hy => simp_all

/-- Rational path transport, with inverse given by the reverse path. -/
def rationalTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational A (Over.mk s) P ≃ₗ[ℚ] Rational A (Over.mk t) P :=
  { rationalTransportMap htor A P hu p with
    invFun := rationalTransportMap htor A P hu p.symm
    left_inv := fun x => by
      change rationalTransportMap htor A P hu p.symm
        (rationalTransportMap htor A P hu p x) = x
      rw [← rationalTransportMap_trans]
      simp
    right_inv := fun x => by
      change rationalTransportMap htor A P hu p
        (rationalTransportMap htor A P hu p.symm x) = x
      rw [← rationalTransportMap_trans]
      simp }

@[simp] theorem rationalTransport_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p x = rationalTransportMap htor A P hu p x := rfl

@[simp] theorem rationalTransport_tmul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : ℚ) (x : Integral A (Over.mk s) P) :
    rationalTransport htor A P hu p (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralTransport htor A P hu p x := rfl

@[simp] theorem rationalTransport_refl (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu (Iso.refl (fiberFunctor s hs)) x = x :=
  rationalTransportMap_refl htor A P hu x

theorem rationalTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu (p ≪≫ q) x =
      rationalTransport htor A P hu q (rationalTransport htor A P hu p x) :=
  rationalTransportMap_trans htor A P hu p q x

theorem rationalTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (rationalTransport htor A P hu p).symm = rationalTransport htor A P hu p.symm := rfl

/-- Loop transport is precisely the previously constructed rational monodromy. -/
theorem rationalTransport_aut (g : FundamentalGroup s hs) :
    rationalTransport htor A P hu g = rationalMonodromy s hs htor A P hu g := rfl

/-- The integral-to-rational map commutes with transport. -/
theorem toRational_transport (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) P) :
    GroupScheme.Tate.toRational A.toGrp (Over.mk t) P (integralTransport htor A P hu p x) =
      rationalTransport htor A P hu p
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) P x) := rfl

/-- Transport intertwines actual geometric monodromy through path conjugation. -/
theorem rationalTransport_monodromy (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p (rationalMonodromy s hs htor A P hu g x) =
      rationalMonodromy t ht htor A P hu (pathConjugation p g)
        (rationalTransport htor A P hu p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralTransport htor A P hu p
      (integralMonodromy s hs htor A P hu g x) =
      q ⊗ₜ[ℤ] integralMonodromy t ht htor A P hu (pathConjugation p g)
        (integralTransport htor A P hu p x)
    rw [integralTransport_monodromy]
  | add x y hx hy => simp_all

/-- Changing the path is exactly target-point geometric monodromy. -/
theorem rationalTransport_change_path (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu q x =
      rationalMonodromy t ht htor A P hu (p.symm ≪≫ q)
        (rationalTransport htor A P hu p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change a ⊗ₜ[ℤ] integralTransport htor A P hu q x =
      a ⊗ₜ[ℤ] integralMonodromy t ht htor A P hu (p.symm ≪≫ q)
        (integralTransport htor A P hu p x)
    rw [integralTransport_change_path]
  | add x y hx hy => simp_all

/-- Transport preserves the rationalized full residue action. -/
theorem rationalTransport_scalarAction (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p
        (GroupScheme.Tate.rationalScalarAction A.toGrp (Over.mk s) P a x) =
      GroupScheme.Tate.rationalScalarAction A.toGrp (Over.mk t) P a
        (rationalTransport htor A P hu p x) :=
  TateScalarExtension.map_action (integralTransportLinearEquiv htor A P hu p).toLinearMap a x

variable {A} {B : AbelianScheme S}

/-- Naturality in an actual abelian-scheme homomorphism. -/
theorem rationalTransport_map (f : A ⟶ B)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor B P hu p (rationalMap (Over.mk s) P f x) =
      rationalMap (Over.mk t) P f (rationalTransport htor A P hu p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralTransport htor B P hu p (map (Over.mk s) P f x) =
      q ⊗ₜ[ℤ] map (Over.mk t) P f (integralTransport htor A P hu p x)
    rw [integralTransport_map]
  | add x y hx hy => simp_all

/-- Naturality extends to the existing rationalized homomorphism group. -/
theorem rationalTransport_homMap (f : Rationalization.Hom A B)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor B P hu p (rationalHomMap (Over.mk s) P f x) =
      rationalHomMap (Over.mk t) P f (rationalTransport htor A P hu p x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalHomMap_tmul, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => q • y) (rationalTransport_map htor P hu f p x)
  | add f f' hf hf' => simp_all

/-- Naturality for invertible rational homomorphisms. -/
theorem rationalTransport_iso (e : Rationalization.of A ≅ Rationalization.of B)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor B P hu p (rationalIso (Over.mk s) P e x) =
      rationalIso (Over.mk t) P e (rationalTransport htor A P hu p x) :=
  rationalTransport_homMap htor P hu e.hom p x

variable (A)

/-- Compatibility with the actual rational endomorphism actions at both points. -/
theorem rationalTransport_endAction (f : Rationalization.End A)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p (rationalEndAction A (Over.mk s) P f x) =
      rationalEndAction A (Over.mk t) P f (rationalTransport htor A P hu p x) :=
  rationalTransport_homMap htor P hu f p x

/-- Compatibility with any algebra acting through actual rational endomorphisms. -/
theorem rationalTransport_algebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (d : D)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p (algebraAction A (Over.mk s) P i d x) =
      algebraAction A (Over.mk t) P i d (rationalTransport htor A P hu p x) :=
  rationalTransport_endAction htor A P hu (i d) p x

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Actual path transport preserves the finite-adelic scalar action. -/
theorem rationalTransport_finiteAdeleAction (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.FiniteAdeles ℚ) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p (finiteAdeleAction A (Over.mk s) P h a x) =
      finiteAdeleAction A (Over.mk t) P h a (rationalTransport htor A P hu p x) :=
  rationalTransport_scalarAction htor A P hu p _ x

/-- The same geometric transport bundled over the constructed finite-adelic module. -/
def finiteAdeleTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := finiteAdeleModule A (Over.mk s) P h
    let := finiteAdeleModule A (Over.mk t) P h
    Rational A (Over.mk s) P ≃ₗ[Global.FiniteAdeles ℚ] Rational A (Over.mk t) P := by
  let := finiteAdeleModule A (Over.mk s) P h
  let := finiteAdeleModule A (Over.mk t) P h
  exact { (rationalTransport htor A P hu p).toEquiv with
    map_add' := (rationalTransport htor A P hu p).map_add
    map_smul' := rationalTransport_finiteAdeleAction htor A P hu h p }

@[simp] theorem finiteAdeleTransport_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) P) :
    finiteAdeleTransport htor A P hu h p x =
      rationalTransport htor A P hu p x := rfl

/-- Path transport preserves the actual endomorphism/finite-adele tensor algebra action. -/
theorem rationalTransport_finiteAdeleAlgebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (a : D ⊗[ℚ] Global.FiniteAdeles ℚ)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalTransport htor A P hu p (finiteAdeleAlgebraAction A (Over.mk s) P h i a x) =
      finiteAdeleAlgebraAction A (Over.mk t) P h i a
        (rationalTransport htor A P hu p x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [finiteAdeleAlgebraAction_tmul, finiteAdeleAlgebraAction_tmul,
      rationalTransport_endAction, rationalTransport_finiteAdeleAction]
  | add a b ha hb => simp_all

/-- Path transport is linear over the tensor algebra used by PEL level structures. -/
def finiteAdeleAlgebraTransport {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := finiteAdeleAlgebraModule A (Over.mk s) P h i
    let := finiteAdeleAlgebraModule A (Over.mk t) P h i
    Rational A (Over.mk s) P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational A (Over.mk t) P := by
  let := finiteAdeleAlgebraModule A (Over.mk s) P h i
  let := finiteAdeleAlgebraModule A (Over.mk t) P h i
  exact { (rationalTransport htor A P hu p).toEquiv with
    map_add' := (rationalTransport htor A P hu p).map_add
    map_smul' := fun a x => rationalTransport_finiteAdeleAlgebraAction
      htor A P hu h i a p x }

@[simp] theorem finiteAdeleAlgebraTransport_apply {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) P) :
    finiteAdeleAlgebraTransport htor A P hu h i p x =
      rationalTransport htor A P hu p x := rfl

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- Full rational path transport. -/
abbrev rationalFullTransport
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    RationalFull A (Over.mk s) ≃ₗ[ℚ] RationalFull A (Over.mk t) :=
  rationalTransport htor A (fun _ => True) hu p

/-- Away rational path transport, for precisely the retained torsion orders. -/
abbrev rationalAwayTransport (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    RationalAway A (Over.mk s) m ≃ₗ[ℚ] RationalAway A (Over.mk t) m :=
  rationalTransport htor A (fun n => Nat.Coprime n m) hu p

/-- The existing rational full-to-away restriction commutes with path transport. -/
theorem rationalRestrictAway_transport (m : ℕ)
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalFull A (Over.mk s)) :
    GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk t) m
        (rationalFullTransport htor A hu p x) =
      rationalAwayTransport htor A m
        (fun n => hu ⟨n.val, n.property.1, trivial⟩) p
        (GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk s) m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

variable (m : ℕ)
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- Away geometric path transport preserves rationalized away residue scalars. -/
theorem rationalAwayTransport_scalarAction (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : RationalAway A (Over.mk s) m) :
    rationalAwayTransport htor A m hu p
        (GroupScheme.Tate.rationalAwayScalarAction A.toGrp (Over.mk s) m a x) =
      GroupScheme.Tate.rationalAwayScalarAction A.toGrp (Over.mk t) m a
        (rationalAwayTransport htor A m hu p x) :=
  TateScalarExtension.map_action
    (awayTransportLinearEquiv htor A m hu p).toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Away geometric path transport preserves the constructed away finite-adelic action. -/
theorem rationalAwayTransport_primeToFiniteAdeleAction (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway A (Over.mk s) m) :
    rationalAwayTransport htor A m hu p
        (primeToFiniteAdeleAction A (Over.mk s) hAway a x) =
      primeToFiniteAdeleAction A (Over.mk t) hAway a
        (rationalAwayTransport htor A m hu p x) :=
  rationalAwayTransport_scalarAction htor A m hu p _ x

/-- The same away path transport bundled over the away finite-adeles. -/
def primeToFiniteAdeleTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := primeToFiniteAdeleModule A (Over.mk s) hAway
    let := primeToFiniteAdeleModule A (Over.mk t) hAway
    RationalAway A (Over.mk s) m ≃ₗ[Global.PrimeToFiniteAdeles m]
      RationalAway A (Over.mk t) m := by
  let := primeToFiniteAdeleModule A (Over.mk s) hAway
  let := primeToFiniteAdeleModule A (Over.mk t) hAway
  exact { (rationalAwayTransport htor A m hu p).toEquiv with
    map_add' := (rationalAwayTransport htor A m hu p).map_add
    map_smul' := rationalAwayTransport_primeToFiniteAdeleAction htor A m hu hAway p }

@[simp] theorem primeToFiniteAdeleTransport_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : RationalAway A (Over.mk s) m) :
    primeToFiniteAdeleTransport htor A m hu hAway p x =
      rationalAwayTransport htor A m hu p x := rfl

/-- Away path transport preserves the tensor action of actual endomorphisms and away adeles. -/
theorem rationalAwayTransport_primeToFiniteAdeleAlgebraAction
    {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (a : D ⊗[ℚ] Global.PrimeToFiniteAdeles m)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalAway A (Over.mk s) m) :
    rationalAwayTransport htor A m hu p
        (primeToFiniteAdeleAlgebraAction A (Over.mk s) hAway i a x) =
      primeToFiniteAdeleAlgebraAction A (Over.mk t) hAway i a
        (rationalAwayTransport htor A m hu p x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [primeToFiniteAdeleAlgebraAction_tmul, primeToFiniteAdeleAlgebraAction_tmul,
      rationalTransport_endAction, rationalAwayTransport_primeToFiniteAdeleAction]
  | add a b ha hb => simp_all

/-- Away path transport as an equivalence over the PEL tensor algebra. -/
def primeToFiniteAdeleAlgebraTransport {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
    let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
    RationalAway A (Over.mk s) m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
      RationalAway A (Over.mk t) m := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  exact { (rationalAwayTransport htor A m hu p).toEquiv with
    map_add' := (rationalAwayTransport htor A m hu p).map_add
    map_smul' := fun a x => rationalAwayTransport_primeToFiniteAdeleAlgebraAction
      htor A m hu hAway i a p x }

@[simp] theorem primeToFiniteAdeleAlgebraTransport_apply
    {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : RationalAway A (Over.mk s) m) :
    primeToFiniteAdeleAlgebraTransport htor A m hu hAway i p x =
      rationalAwayTransport htor A m hu p x := rfl

end Langlands.AbelianScheme.Tate
