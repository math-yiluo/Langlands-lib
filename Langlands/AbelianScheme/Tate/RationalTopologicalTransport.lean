import Langlands.AbelianScheme.Tate.RationalTopology
import Langlands.AbelianScheme.Tate.RationalBaseChange
import Langlands.AbelianScheme.Tate.RationalTransport

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

attribute [local instance] rationalTopology

section BaseChange
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)
  (T : Over S') (P : ℕ → Prop)

/-- The existing rational base-change comparison is continuous. -/
theorem continuous_rationalBaseChange :
    Continuous (rationalBaseChange b A T P) :=
  Langlands.Topology.Rationalization.continuous_baseChange
    (GroupScheme.Tate.integralBaseChange b A.toGrp T P).toAddMonoidHom
    (GroupScheme.Tate.continuous_integralBaseChange b A.toGrp T P)

/-- Continuity of the inverse actual base-change comparison. -/
theorem continuous_rationalBaseChange_symm :
    Continuous (rationalBaseChange b A T P).symm :=
  Langlands.Topology.Rationalization.continuous_baseChange
    (GroupScheme.Tate.integralBaseChange b A.toGrp T P).symm.toAddMonoidHom
    (GroupScheme.Tate.continuous_integralBaseChange_symm b A.toGrp T P)

/-- Actual rational base change bundled with continuity in both directions. -/
def rationalBaseChangeContinuousLinearEquiv :
    Rational ((AbelianScheme.baseChange b).obj A) T P ≃L[ℚ]
      Rational A ((Over.map b).obj T) P where
  __ := rationalBaseChange b A T P
  continuous_toFun := continuous_rationalBaseChange b A T P
  continuous_invFun := continuous_rationalBaseChange_symm b A T P

@[simp] theorem rationalBaseChangeContinuousLinearEquiv_toLinearEquiv :
    (rationalBaseChangeContinuousLinearEquiv b A T P).toLinearEquiv =
      rationalBaseChange b A T P := rfl

end BaseChange

section Path
variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (p : fiberFunctor s hs ≅ fiberFunctor t ht)

/-- The existing path map is continuous after rationalization. -/
theorem continuous_rationalTransport :
    Continuous (rationalTransport htor A P hu p) :=
  Langlands.Topology.Rationalization.continuous_baseChange
    (integralTransportHom htor A P hu p)
    (continuous_integralTransport htor A P hu p)

/-- Actual rational path transport as a continuous linear equivalence. -/
def rationalTransportContinuousLinearEquiv :
    Rational A (Over.mk s) P ≃L[ℚ] Rational A (Over.mk t) P where
  __ := rationalTransport htor A P hu p
  continuous_toFun := continuous_rationalTransport htor A P hu p
  continuous_invFun := continuous_rationalTransport htor A P hu p.symm

@[simp] theorem rationalTransportContinuousLinearEquiv_toLinearEquiv :
    (rationalTransportContinuousLinearEquiv htor A P hu p).toLinearEquiv =
      rationalTransport htor A P hu p := rfl

end Path

section Hom
variable {S : Scheme.{u}} {A B : AbelianScheme S} (T : Over S) (P : ℕ → Prop)

/-- Rational homomorphisms are continuous when the target rational Tate group has
continuous addition. Full and away targets satisfy this without an extra hypothesis. -/
theorem continuous_rationalHomMap [IsTopologicalAddGroup (Rational B T P)]
    (f : Rationalization.Hom A B) : Continuous (rationalHomMap T P f) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    change Continuous (fun x => q • rationalMap T P f x)
    exact (continuous_rational_smul B T P q).comp (continuous_rationalMap T P f)
  | add f g hf hg =>
    apply (hf.add hg).congr
    intro x
    simp only [Pi.add_apply, _root_.map_add, LinearMap.add_apply]

/-- Continuity for every rational homomorphism on full Tate modules. -/
theorem continuous_rationalFullHomMap (f : Rationalization.Hom A B) :
    Continuous (rationalHomMap T (fun _ => True) f) := by
  let := rationalFull_topologicalAddGroup B T
  exact continuous_rationalHomMap T (fun _ => True) f

/-- Continuity for every rational homomorphism on away Tate modules. -/
theorem continuous_rationalAwayHomMap (m : ℕ) (f : Rationalization.Hom A B) :
    Continuous (rationalHomMap T (fun n => Nat.Coprime n m) f) := by
  let := rationalAway_topologicalAddGroup B T m
  exact continuous_rationalHomMap T (fun n => Nat.Coprime n m) f

/-- An isomorphism in the rationalized category gives a continuous equivalence
whenever the two selected rational Tate groups have continuous addition. -/
def rationalIsoContinuousLinearEquiv
    [IsTopologicalAddGroup (Rational A T P)] [IsTopologicalAddGroup (Rational B T P)]
    (e : Rationalization.of A ≅ Rationalization.of B) :
    Rational A T P ≃L[ℚ] Rational B T P where
  __ := rationalIso T P e
  continuous_toFun := continuous_rationalHomMap T P e.hom
  continuous_invFun := continuous_rationalHomMap T P e.inv

@[simp] theorem rationalIsoContinuousLinearEquiv_toLinearEquiv
    [IsTopologicalAddGroup (Rational A T P)] [IsTopologicalAddGroup (Rational B T P)]
    (e : Rationalization.of A ≅ Rationalization.of B) :
    (rationalIsoContinuousLinearEquiv T P e).toLinearEquiv = rationalIso T P e := rfl

/-- Invertible rational homomorphisms act by homeomorphisms on full Tate modules. -/
def rationalFullIsoContinuousLinearEquiv (e : Rationalization.of A ≅ Rationalization.of B) :
    RationalFull A T ≃L[ℚ] RationalFull B T := by
  let := rationalFull_topologicalAddGroup A T
  let := rationalFull_topologicalAddGroup B T
  exact rationalIsoContinuousLinearEquiv T (fun _ => True) e

/-- Invertible rational homomorphisms act by homeomorphisms on away Tate modules. -/
def rationalAwayIsoContinuousLinearEquiv (m : ℕ)
    (e : Rationalization.of A ≅ Rationalization.of B) :
    RationalAway A T m ≃L[ℚ] RationalAway B T m := by
  let := rationalAway_topologicalAddGroup A T m
  let := rationalAway_topologicalAddGroup B T m
  exact rationalIsoContinuousLinearEquiv T (fun n => Nat.Coprime n m) e

@[simp] theorem rationalFullIsoContinuousLinearEquiv_toLinearEquiv
    (e : Rationalization.of A ≅ Rationalization.of B) :
    (rationalFullIsoContinuousLinearEquiv T e).toLinearEquiv =
      rationalIso T (fun _ => True) e := rfl

@[simp] theorem rationalAwayIsoContinuousLinearEquiv_toLinearEquiv (m : ℕ)
    (e : Rationalization.of A ≅ Rationalization.of B) :
    (rationalAwayIsoContinuousLinearEquiv T m e).toLinearEquiv =
      rationalIso T (fun n => Nat.Coprime n m) e := rfl

end Hom
end Langlands.AbelianScheme.Tate
