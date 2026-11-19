import Langlands.Automorphic.CuspidalL2.Basics
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Analytic comparison of infinite Hilbert coefficients -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.ArchimedeanGL
universe u
variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- All genuine enveloping values on the standard compact subgroup determine
an actual joint-finite smooth function on every group component. -/
theorem jointFinite_eq_of_compact_enveloping_values
    (s t : SmoothFunctions F n) (hs : IsJointFinite F n s) (ht : IsJointFinite F n t)
    (hK : ∀ (a : EnvelopingAlgebra F n) (k : Langlands.Global.standardInfiniteCompact F n),
      (envelopingAction F n a s).val k.val = (envelopingAction F n a t).val k.val) : s = t := by
  have hd : IsJointFinite F n (s - t) := (jointFiniteFunctions F n).sub_mem hs ht
  have han := jointFiniteAnalyticity F n (s - t) hd
  apply Subtype.ext
  funext g
  obtain ⟨k, hgk⟩ := compactComponentCoverage F n g
  have hzero (a : EnvelopingAlgebra F n) :
      (envelopingAction F n a (s - t)).val k.val = 0 := by
    have h := congrArg (fun f : SmoothFunctions F n => f.val k.val)
      ((envelopingAction F n a).map_sub s t)
    exact h.trans (sub_eq_zero.mpr (hK a k))
  have hjet := envelopingZeroJet F n (s - t) k.val hzero
  have hg := analyticMatrixJetUniqueness F n (s - t) k.val han hjet g hgk
  exact sub_eq_zero.mp hg

universe uV uW
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Differential covariance and compact scalar values extend a comparison of
coefficient maps to the whole actual infinite group. -/
theorem coefficientMaps_eq_of_compact_values
    (S : V →ₗ[ℂ] SmoothFunctions F n) (T : W →ₗ[ℂ] SmoothFunctions F n)
    (D : EnvelopingAlgebra F n → V → V) (Q : EnvelopingAlgebra F n → W → W)
    (e : V →ₗ[ℂ] W)
    (hS : ∀ a v, S (D a v) = envelopingAction F n a (S v))
    (hT : ∀ a w, T (Q a w) = envelopingAction F n a (T w))
    (he : ∀ a v, e (D a v) = Q a (e v))
    (hs : ∀ v, IsJointFinite F n (S v)) (ht : ∀ w, IsJointFinite F n (T w))
    (hK : ∀ v (k : Langlands.Global.standardInfiniteCompact F n),
      (S v).val k.val = (T (e v)).val k.val) (v : V) : S v = T (e v) := by
  apply jointFinite_eq_of_compact_enveloping_values F n _ _ (hs v) (ht (e v))
  intro a k
  exact (congrArg (fun f : SmoothFunctions F n => f.val k.val) (hS a v).symm).trans
    ((hK (D a v) k).trans
      ((congrArg (fun w : W => (T w).val k.val) (he a v)).trans
        (congrArg (fun f : SmoothFunctions F n => f.val k.val) (hT a (e v)))))

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.HilbertCoefficientComparison

open Langlands.Global
universe u uG uV uW uE uH uTest
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual Hilbert orbit coefficients of dense source vectors retain
smooth joint-finite lifts with the prescribed enveloping action. -/
def JointFiniteCoefficientLifts (U : G →* (E →L[ℂ] E))
    (ι : InfiniteAdelicGL F n → G) (j : V → E) (D : ArchimedeanGL.EnvelopingAlgebra F n → V → V) :
    Prop :=
  ∀ w : E, ∃ C : V →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n,
    (∀ v g, (C v).val g = Inner.inner ℂ w (U (ι g) (j v))) ∧
    (∀ a v, C (D a v) = ArchimedeanGL.envelopingAction F n a (C v)) ∧
    ∀ v, ArchimedeanGL.IsJointFinite F n (C v)

/-- Identify the smooth lifts using their actual scalar values. -/
theorem jointFiniteCoefficientLifts_of_values (U : G →* (E →L[ℂ] E))
    (ι : InfiniteAdelicGL F n → G) (j : V → E) (D : ArchimedeanGL.EnvelopingAlgebra F n → V → V)
    {B : Type uTest} (J : E → B) (c : B → V → InfiniteAdelicGL F n → ℂ)
    (hvalue : ∀ w v g, Inner.inner ℂ w (U (ι g) (j v)) = c (J w) v g)
    (hlift : ∀ w : B, ∃ C : V →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n,
      (∀ v g, (C v).val g = c w v g) ∧
      (∀ a v, C (D a v) = ArchimedeanGL.envelopingAction F n a (C v)) ∧
      ∀ v, ArchimedeanGL.IsJointFinite F n (C v)) :
    JointFiniteCoefficientLifts U ι j D := by
  intro w
  obtain ⟨C, hC, hD, hfinite⟩ := hlift (J w)
  exact ⟨C, fun v g => (hC v g).trans (hvalue w v g).symm, hD, hfinite⟩

variable [CompleteSpace E] [CompleteSpace H]

/-- The compact and differential covariance of the original map identify
the completed infinite actions through their actual Hilbert coefficients. -/
theorem intertwines_infinite_of_coefficients
    (U : G →* (E →L[ℂ] E)) (U' : G →* (H →L[ℂ] H))
    (ι : InfiniteAdelicGL F n → G) (j : V → E) (j' : W → H) (hj : DenseRange j)
    (D : ArchimedeanGL.EnvelopingAlgebra F n → V → V)
    (D' : ArchimedeanGL.EnvelopingAlgebra F n → W → W)
    (hC : JointFiniteCoefficientLifts U ι j D) (hC' : JointFiniteCoefficientLifts U' ι j' D')
    (L : E →L[ℂ] H) (e : V →ₗ[ℂ] W) (hL : ∀ v, L (j v) = j' (e v))
    (he : ∀ a v, e (D a v) = D' a (e v))
    (hK : ∀ (k : standardInfiniteCompact F n) v,
      L (U (ι k.val) (j v)) = U' (ι k.val) (L (j v)))
    (g : InfiniteAdelicGL F n) (x : E) :
    L (U (ι g) x) = U' (ι g) (L x) := by
  refine hj.induction_on x
    (isClosed_eq (L.continuous.comp (U (ι g)).continuous)
      ((U' (ι g)).continuous.comp L.continuous)) ?_
  intro v
  apply ext_inner_left ℂ
  intro w
  obtain ⟨C, hval, hD, hfinite⟩ := hC (L.adjoint w)
  obtain ⟨C', hval', hD', hfinite'⟩ := hC' w
  have hcompact (z : V) (k : standardInfiniteCompact F n) :
      (C z).val k.val = (C' (e z)).val k.val := by
    calc
      (C z).val k.val = Inner.inner ℂ (L.adjoint w) (U (ι k.val) (j z)) := hval z k.val
      _ = Inner.inner ℂ w (L (U (ι k.val) (j z))) := L.adjoint_inner_left _ w
      _ = Inner.inner ℂ w (U' (ι k.val) (L (j z))) := congrArg (Inner.inner ℂ w) (hK k z)
      _ = Inner.inner ℂ w (U' (ι k.val) (j' (e z))) :=
        congrArg (fun y => Inner.inner ℂ w (U' (ι k.val) y)) (hL z)
      _ = (C' (e z)).val k.val := (hval' (e z) k.val).symm
  have hCg := ArchimedeanGL.coefficientMaps_eq_of_compact_values F n
    C C' D D' e hD hD' he hfinite hfinite' hcompact v
  have hval_g := congrArg (fun f : ArchimedeanGL.SmoothFunctions F n => f.val g) hCg
  exact (L.adjoint_inner_left _ w).symm.trans ((hval v g).symm.trans
    (hval_g.trans ((hval' (e v) g).trans
      (congrArg (fun y => Inner.inner ℂ w (U' (ι g) y)) (hL v)).symm)))

/-- Covariance of a bounded map for the whole adelic group. -/
def AdelicIntertwines (U : AdelicGL F n →* (E →L[ℂ] E))
    (U' : AdelicGL F n →* (H →L[ℂ] H)) (L : E →L[ℂ] H) : Prop :=
  ∀ g x, L (U g x) = U' g (L x)

/-- The two adelic factors identify the full action once the finite action
and the analytic infinite coefficients have been compared. -/
theorem adelicIntertwines_of_coefficients
    (U : AdelicGL F n →* (E →L[ℂ] E)) (U' : AdelicGL F n →* (H →L[ℂ] H))
    (j : V → E) (j' : W → H) (hj : DenseRange j)
    (D : ArchimedeanGL.EnvelopingAlgebra F n → V → V)
    (D' : ArchimedeanGL.EnvelopingAlgebra F n → W → W)
    (hC : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (hC' : JointFiniteCoefficientLifts U' (AdelicGL.ofInfinite F n) j' D')
    (L : E →L[ℂ] H) (e : V →ₗ[ℂ] W) (hL : ∀ v, L (j v) = j' (e v))
    (he : ∀ a v, e (D a v) = D' a (e v))
    (hK : ∀ (k : standardInfiniteCompact F n) v,
      L (U (AdelicGL.ofInfinite F n k.val) (j v)) =
        U' (AdelicGL.ofInfinite F n k.val) (L (j v)))
    (hF : ∀ (d : FiniteAdelicGL F n) v,
      L (U (AdelicGL.ofFinite F n d) (j v)) = U' (AdelicGL.ofFinite F n d) (L (j v))) :
    AdelicIntertwines U U' L := by
  have hinf := intertwines_infinite_of_coefficients U U' (AdelicGL.ofInfinite F n)
    j j' hj D D' hC hC' L e hL he hK
  have hfin (d : FiniteAdelicGL F n) (x : E) :
      L (U (AdelicGL.ofFinite F n d) x) = U' (AdelicGL.ofFinite F n d) (L x) :=
    hj.induction_on x
      (isClosed_eq (L.continuous.comp (U (AdelicGL.ofFinite F n d)).continuous)
        ((U' (AdelicGL.ofFinite F n d)).continuous.comp L.continuous)) (hF d)
  intro g x
  rw [AdelicGL.eq_ofInfinite_mul_ofFinite F n g, map_mul, map_mul]
  exact (hinf (AdelicGL.infinite F n g) _).trans
    (congrArg (U' (AdelicGL.ofInfinite F n (AdelicGL.infinite F n g)))
      (hfin (AdelicGL.finite F n g) x))

end Langlands.Automorphic.HilbertCoefficientComparison
