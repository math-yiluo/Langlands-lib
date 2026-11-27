import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Langlands.Representation.Plancherel.StandardIntertwiningNaturality

/-! # Pointwise and compact-chart comparisons for linear operators -/

noncomputable section

namespace Langlands.Plancherel

open UnramifiedOperatorFamily
open scoped NNReal

universe u uI uV uW

section Polynomial

variable {G : Type u} [Group G] [TopologicalSpace G] {I : Type uI}
  {ν : I → (G →* ℝ≥0ˣ)}
  {V W E Q : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E]
  {r : unramifiedCharacters ν → V → Q → E}
  (ev : Q → W →ₗ[ℂ] E)
  (hext : ∀ {f g}, (∀ k, ev k f = ev k g) → f = g)

include hext in
/-- A uniform Laurent multiplier on all evaluations gives the same multiplier on the
whole linear operator. -/
theorem isPolynomialOperatorOn_of_pointwise_regular_smul
    {L : unramifiedCharacters ν → V →ₗ[ℂ] W} (z₀ : unramifiedCharacters ν)
    (b : unramifiedRegularFunctions ν)
    (hL : ∀ z v k, ev k (L z v) = r z v k)
    (hr : ∀ z v k, r z v k = b.val z • r z₀ v k) :
    IsPolynomialOperatorOn Set.univ (fun z => L z.val) := by
  have h (z) : L z = b.val z • L z₀ := by
    apply LinearMap.ext
    intro v
    apply hext
    intro k
    change ev k (L z v) = ev k (b.val z • L z₀ v)
    rw [map_smul, hL, hr, hL]
  have hfun : (fun z : ↥(Set.univ : Set (unramifiedCharacters ν)) => L z.val) =
      (fun z => b.val z.val • L z₀) := funext fun z => h z.val
  rw [hfun]
  exact (isPolynomialOperatorOn_const (L z₀)).regular_smul b

omit [AddCommGroup V] [Module ℂ V] in
/-- A scalar identity for a family of values is unchanged by reparametrization. -/
theorem pointwise_regular_smul_of_reparam {X Y : Type*} (q : X → Y)
    (g : Y → V → Q → E) (f : X → V → Q → E) (b : X → ℂ) (c : Y → ℂ)
    (x₀ : X) (y₀ : Y) (h₀ : q x₀ = y₀)
    (hf : ∀ x v k, f x v k = g (q x) v k) (hb : ∀ x, b x = c (q x))
    (hg : ∀ y v k, g y v k = c y • g y₀ v k) (x : X) (v : V) (k : Q) :
    f x v k = b x • f x₀ v k := by
  rw [hf, hf, hb, h₀]
  exact hg (q x) v k

end Polynomial

section Charts

variable {O P X Y S T U V : Type*}
  [AddCommGroup O] [Module ℂ O] [AddCommGroup P] [Module ℂ P]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

/-- An evaluation identity for an equivalence gives the reverse identity for its inverse. -/
theorem eval_linearEquiv_symm {Z : Type*} (e : X ≃ₗ[ℂ] Y) (p : X → Z) (q : Y → Z)
    (h : ∀ x, q (e x) = p x) (y : Y) : p (e.symm y) = q y :=
  (h (e.symm y)).symm.trans (congrArg q (e.apply_symm_apply y))

/-- Insert equivalent middle spaces and their compact charts around a commuting square. -/
theorem compactOperatorOfSquare
    (a : O →ₗ[ℂ] X) (b : Y →ₗ[ℂ] P) (J : X →ₗ[ℂ] Y) (J' : S →ₗ[ℂ] T)
    (e : X ≃ₗ[ℂ] S) (f : Y ≃ₗ[ℂ] T) (e' : S ≃ₗ[ℂ] U) (f' : T ≃ₗ[ℂ] V)
    (h : ∀ v, J' (e v) = f (J v)) :
    b ∘ₗ J ∘ₗ a = (b ∘ₗ f.symm.toLinearMap ∘ₗ f'.symm.toLinearMap) ∘ₗ
      (f'.toLinearMap ∘ₗ J' ∘ₗ e'.symm.toLinearMap) ∘ₗ
      (e'.toLinearMap ∘ₗ e.toLinearMap ∘ₗ a) := by
  apply LinearMap.ext
  intro v
  change b (J (a v)) = b (f.symm (f'.symm (f' (J' (e'.symm (e' (e (a v))))))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h, LinearEquiv.symm_apply_apply]

end Charts

namespace StandardIntertwining

open Aubert.General Induction

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {A : SmoothRep.{0, u, uV} ℂ M} {B : SmoothRep.{0, u, uW} ℂ M}

/-- The coefficient change on positive Levi-normalized induction. Its forward and inverse
maps are the actual maps in the naturality of the standard integral. -/
def inducedLeviLinearEquiv (e : A.representation.Equiv B.representation) :
    (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A ≃ₗ[ℂ]
      (DynamicNormalization.leviTwistedInductionFunctor h hU).obj B where
  __ := (inducedMap h hU e.toIntertwiningMap).toLinearMap
  invFun := inducedMap h hU e.symm.toIntertwiningMap
  left_inv _ := Subtype.ext (Subtype.ext (funext (fun _ => e.symm_apply_apply _)))
  right_inv _ := Subtype.ext (Subtype.ext (funext (fun _ => e.apply_symm_apply _)))

end StandardIntertwining

end Langlands.Plancherel
