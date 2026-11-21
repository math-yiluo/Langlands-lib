import Langlands.Automorphic.AlgebraOperatorSubquotient
import Langlands.Global.EisensteinProjectedDetection

/-! # Detecting an irreducible specialization by holomorphic lifts in cyclic submodules -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.EisensteinJet

section Detection

variable {R J Z V X : Type*} [Ring R]
  [AddCommGroup J] [Module R J] [AddCommGroup Z] [Module R Z] [Module ℂ Z]
  [AddCommGroup V] [Module ℂ V]

/-- A lift inside a cyclic submodule whose section is detected by the scalar Taylor tests. -/
structure HolomorphicCyclicLift (E : ℂ → V →ₗ[ℂ] (X → ℂ)) (z : ℂ)
    (c : ℕ → J →ₗ[R] Z) (observe : Z →ₗ[ℂ] (X → ℂ)) (x : J) where
  lift : J
  mem_cyclic : lift ∈ Submodule.span R {x}
  sectionCurve : ℂ → V
  coordinates_analytic : ∀ l : V →ₗ[ℂ] ℂ, AnalyticAt ℂ (fun t => l (sectionCurve t)) z
  value_ne_zero : sectionCurve z ≠ 0
  evaluate_coefficient : ∀ k p, observe (c k lift) p =
    iteratedDeriv k (fun t => E t (sectionCurve t) p) z / (k.factorial : ℂ)

/-- One fixed target vector suffices for the cyclic lift test.
The lift itself can be chosen anew in each cyclic submodule. -/
theorem exists_subquotient_of_holomorphic_cyclic_lifts [FiniteDimensional ℂ V]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [IsSimpleModule R Q]
    (U : Set ℂ) (hU : IsPreconnected U) (z t₁ : ℂ) (hz : z ∈ U) (ht₁ : t₁ ∈ U)
    (E : ℂ → V →ₗ[ℂ] (X → ℂ)) (hE : ∀ v p, AnalyticOnNhd ℂ (fun t => E t v p) U)
    (hinj : Function.Injective (E t₁)) (q : J →ₗ[R] Q) (hq : Function.Surjective q)
    (c : ℕ → J →ₗ[R] Z) (observe : Z →ₗ[ℂ] (X → ℂ))
    (y : Q)
    (hlift : ∀ x, q x = y → Nonempty (HolomorphicCyclicLift E z c observe x)) :
    ∃ S : Submodule R Z, ∃ u : S →ₗ[R] Q, Function.Surjective u := by
  obtain ⟨d, hd⟩ := exists_derivativeDetectionOrder U hU z t₁ hz ht₁ E hE hinj
  let orders := Finset.range d
  let K := jointCoefficientKernel orders c
  have hqtop : Function.Surjective (q.comp (⊤ : Submodule R J).subtype) := by
    intro a
    obtain ⟨x, rfl⟩ := hq a
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  refine exists_subquotient_of_coefficients orders c q ⊤ hqtop (fun x _ hx => ?_)
  by_contra hxq
  obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective R hxq y
  have hby : q (b • x) = y := (q.map_smul b x).trans hb
  obtain ⟨w⟩ := hlift (b • x) hby
  have hxK : x ∈ K := (mem_jointCoefficientKernel orders c x).mpr hx
  have hspan : Submodule.span R {b • x} ≤ K :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (K.smul_mem b hxK))
  have hzero := (mem_jointCoefficientKernel orders c w.lift).mp (hspan w.mem_cyclic)
  apply w.value_ne_zero
  apply hd w.sectionCurve w.coordinates_analytic
  intro p k
  have hk := w.evaluate_coefficient k p
  rw [hzero k (Finset.mem_range.mpr k.isLt), map_zero, Pi.zero_apply] at hk
  exact (div_eq_zero_iff.mp hk.symm).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end Detection

open Langlands.Automorphic

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "Operators" => FreeOperatorAlgebra F (r + 1)
local notation "Stable" => StableAutomorphicFunctions F (r + 1)

local instance detectionRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance detectionContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance detectionSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance detectionStableAddCommGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance detectionStableComplexModule : Module ℂ Stable := Submodule.module _

/-- A Taylor coefficient family with holomorphic cyclic lifts realizes its
simple specialization as an actual automorphic quotient with the prescribed finite action. -/
theorem exists_automorphic_subquotient_of_holomorphic_cyclic_lifts
    {J V W X : Type*} [AddCommGroup J] [Module Operators J]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (a : Operators →ₐ[ℂ] Module.End ℂ W) (ha : Representation.IsIrreducible a.toMonoidHom)
    (fin : Representation ℂ (FiniteAdelicGL F (r + 1)) W)
    (hfin : ∀ g, a (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) = fin g)
    (U : Set ℂ) (hU : IsPreconnected U) (z t₁ : ℂ) (hz : z ∈ U) (ht₁ : t₁ ∈ U)
    (E : ℂ → V →ₗ[ℂ] (X → ℂ)) (hE : ∀ v p, AnalyticOnNhd ℂ (fun t => E t v p) U)
    (hinj : Function.Injective (E t₁)) (observe : Stable →ₗ[ℂ] (X → ℂ)) :
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
    letI := moduleOfAlgebraAction a
    ∀ (q : J →ₗ[Operators] W) (_hq : Function.Surjective q) (c : ℕ → J →ₗ[Operators] Stable)
      (y : W), (∀ x, q x = y → Nonempty (HolomorphicCyclicLift E z c observe x)) →
      ∃ Q : IrreducibleOperatorSubquotient F r, Nonempty (Q.subquotient.finiteRepresentation.Equiv fin) := by
  let := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
  let := moduleOfAlgebraAction a
  let := (isSimpleModule_iff_irreducible_algebraAction a).mpr ha
  intro q hq c y hlift
  obtain ⟨S, p, hp⟩ := exists_subquotient_of_holomorphic_cyclic_lifts U hU z t₁ hz ht₁
    E hE hinj q hq c observe y hlift
  exact exists_irreducibleOperatorSubquotient_of_freeModule F r a ha fin hfin S p hp

end Langlands.Global.EisensteinJet
