import Langlands.AbelianScheme.Tate.PrimeBaseChange
import Langlands.AbelianScheme.Tate.PrimeTransport
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AbelianScheme.GeometricEndomorphismTraceComparisonStatement
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Geometric point and field base change of the actual prime Tate trace -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.FiniteEtale

/-- Trace of the actual rational prime Tate action at any test object. -/
def primeEndomorphismTraceAt {S : Scheme.{u}} (A : AbelianScheme S)
    (T : Over S) (p : ℕ) [Fact p.Prime] : End0 A →ₗ[ℚ] ℚ_[p] :=
  ((LinearMap.trace ℚ_[p] (Tate.PrimeAdic.Rational A T p)).restrictScalars ℚ).comp
    (Tate.PrimeAdic.rationalEndAction T p A).toLinearMap

namespace Tate.PrimeAdic

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u})
  (A : AbelianScheme S) (p : ℕ) [Fact p.Prime]
  (hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(S, ⊤)))

/-- Actual rational homomorphisms intertwine the prime geometric path equivalence. -/
theorem rationalTransport_homMap
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (f : End0 A)
    (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu e (rationalHomMap (Over.mk s) p f x) =
      rationalHomMap (Over.mk t) p f (rationalTransport htor A p hu e x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [rationalHomMap_tmul, LinearMap.smul_apply]
      rw [map_rat_smul, rationalTransport_map]
  | add f g hf hg =>
      simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

include htor hu in
/-- Actual prime Tate traces agree at endpoints of a geometric path. -/
theorem primeEndomorphismTraceAt_path
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (f : End0 A) :
    primeEndomorphismTraceAt A (Over.mk s) p f =
      primeEndomorphismTraceAt A (Over.mk t) p f := by
  let E := rationalTransport htor A p hu e
  have he : E.conj (rationalHomMap (Over.mk s) p f) =
      rationalHomMap (Over.mk t) p f := by
    apply LinearMap.ext
    intro x
    change E (rationalHomMap (Over.mk s) p f (E.symm x)) = _
    rw [rationalTransport_homMap, E.apply_symm_apply]
  exact (LinearMap.trace_conj' _ E).symm.trans
    (congrArg (LinearMap.trace ℚ_[p] _) he)

end Tate.PrimeAdic

/-- The actual prime Tate trace is independent of the geometric point on a
connected locally noetherian base at an invertible prime. -/
theorem primeEndomorphismTraceAt_geometric {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] (A : AbelianScheme S)
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : Γ(S, ⊤))) (f : End0 A) :
    primeEndomorphismTraceAt A (Over.mk s) p f =
      primeEndomorphismTraceAt A (Over.mk t) p f := by
  obtain ⟨e⟩ := geometricPathExists s t (geometricFiberFinite s) (geometricFiberFinite t)
  exact Tate.PrimeAdic.primeEndomorphismTraceAt_path torsionFiniteEtale A p
    (fun n => by simpa only [Nat.cast_pow] using hp.pow n) e f

/-- The prime trace on the actual pullback at the mapped test object. -/
theorem primeEndomorphismTraceAt_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    (A : AbelianScheme S) (T : Over S') (p : ℕ) [Fact p.Prime] (f : End0 A) :
    primeEndomorphismTraceAt ((baseChange b).obj A) T p (rationalBaseChangeHom b f) =
      primeEndomorphismTraceAt A ((Over.map b).obj T) p f :=
  Tate.PrimeAdic.trace_rationalHomMap_baseChange b A T p f

/-- Prime Tate trace is invariant under extension between algebraically closed
fields at every prime different from the source characteristic. -/
theorem primeEndomorphismTrace_baseChange
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ Spec (.of k)) (A : AbelianScheme (Spec (.of k)))
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) (f : End0 A) :
    primeEndomorphismTrace ((baseChange b).obj A) p (rationalBaseChangeHom b f) =
      primeEndomorphismTrace A p f := by
  have hunit : IsUnit (p : Γ(Spec (.of k), ⊤)) := by
    simpa using (isUnit_iff_ne_zero.mpr hp).map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact (primeEndomorphismTraceAt_baseChange b A (Over.mk (𝟙 _)) p f).trans
    (primeEndomorphismTraceAt_geometric A ((𝟙 _) ≫ b) (𝟙 _) p hunit f)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Conditional on the separately owned rational trace comparison, the fixed
geometric trace is invariant under extension between geometric fields. -/
theorem geometricEndomorphismTrace_baseChange_of_comparison
    (hcomparison : GeometricEndomorphismTraceComparisonStatement.{u})
    {k K : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [Field K] [IsAlgClosed K] [CharZero K]
    (b : Spec (.of K) ⟶ Spec (.of k)) (A : AbelianScheme (Spec (.of k)))
    (f : End0 A) :
    geometricEndomorphismTrace ((baseChange b).obj A) (rationalBaseChangeHom b f) =
      geometricEndomorphismTrace A f := by
  apply (algebraMap ℚ ℚ_[2]).injective
  rw [(hcomparison K ((baseChange b).obj A) 2).2.2,
    (hcomparison k A 2).2.2]
  exact primeEndomorphismTrace_baseChange b A 2 (by norm_num) f

end Langlands.AbelianScheme
