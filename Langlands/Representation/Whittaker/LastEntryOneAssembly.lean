import Langlands.Representation.Whittaker.LastEntryOneAsymptoticStatement
import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.Representation.RankinSelberg.RootCoordinateProof
import Langlands.Representation.RankinSelberg.FiniteFunctionClosureProof

/-!
# Coordinates and scalar assembly for the last-entry-one expansion

Coordinate and scalar-functional bookkeeping used by the closed proof in
`LastEntryOneAsymptoticProof`. The assembly helper takes a root expansion as input.
-/

noncomputable section

namespace Langlands.WhittakerLastEntryOne

open scoped BigOperators

universe uF uV uA

/-- The exact finite-function predicate of the target. -/
def IsFiniteFunction {A : Type uA} [Monoid A] [TopologicalSpace A]
    (f : A → ℂ) : Prop :=
  Continuous f ∧ FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range fun b : A => fun a => f (b * a)))

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

/-- The target's actual diagonal homomorphism. -/
def torus : (Fin (n + 1) → Kˣ) →* GeneralLinear (n + 1) K :=
  (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) K).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

/-- Consecutive quotients with values in the units. -/
def rootHom : (Fin (n + 1) → Kˣ) →* (Fin n → Kˣ) where
  toFun a i := a i.castSucc / a i.succ
  map_one' := by ext i; simp
  map_mul' a b := by
    funext i
    change (a i.castSucc * b i.castSucc) / (a i.succ * b i.succ) =
      (a i.castSucc / a i.succ) * (b i.castSucc / b i.succ)
    exact mul_div_mul_comm _ _ _ _

/-- Field-valued simple roots, as in the target. -/
def roots (a : Fin (n + 1) → Kˣ) (i : Fin n) : K :=
  (rootHom a i : K)

/-- Cumulative products with final diagonal entry one. -/
def rootLift (x : Fin n → Kˣ) (i : Fin (n + 1)) : Kˣ :=
  ∏ j ∈ Finset.univ.filter (i ≤ ·), Fin.lastCases 1 x j

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_rootHom : Continuous (rootHom (K := K) (n := n)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i.castSucc).div' (continuous_apply i.succ)

theorem finiteFunction_pullback {f : (Fin n → Kˣ) → ℂ}
    (hf : IsFiniteFunction f) :
    IsFiniteFunction (fun a => f (rootHom a)) :=
  (RankinSelberg.finiteFunctionClosure
    (Fin n → Kˣ) (Fin (n + 1) → Kˣ)).2.1 rootHom continuous_rootHom f hf

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)

include T

/-- The existing full coordinate theorem recovers every root of this section. -/
theorem rootHom_rootLift (x : Fin n → F.Carrierˣ) :
    rootHom (rootLift x) = x := by
  have h := (RankinSelberg.rootCoordinateChange F T n).2.2.1
    (Fin.lastCases 1 x)
  funext i
  have hi := congrArg (fun a => a i.castSucc) h
  simpa only [rootHom, MonoidHom.coe_mk, OneHom.coe_mk,
    rootLift, Fin.lastCases_castSucc] using hi

/-- The cumulative-product section has last entry one, also when `n = 0`. -/
theorem rootLift_last (x : Fin n → F.Carrierˣ) :
    rootLift x (Fin.last n) = 1 := by
  have h := ((RankinSelberg.rootCoordinateChange F T n).2.2.2.2.2.2
    (Fin.lastCases 1 x)).2.1
  simpa only [rootLift, Fin.lastCases_last] using h

/-- Every last-entry-one diagonal is recovered from its simple roots. -/
theorem rootLift_rootHom (a : Fin (n + 1) → F.Carrierˣ)
    (ha : a (Fin.last n) = 1) :
    rootLift (rootHom a) = a := by
  have h := (RankinSelberg.rootCoordinateChange F T n).2.2.2.1 a
  change (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·),
    Fin.lastCases 1 (fun k => a k.castSucc / a k.succ) j) = a
  simpa only [ha] using h

/-- Pullback has no collisions because the root map has a section. -/
theorem pullback_injective :
    Function.Injective (fun f : (Fin n → F.Carrierˣ) → ℂ =>
      fun a : Fin (n + 1) → F.Carrierˣ => f (rootHom a)) := by
  intro f g h
  funext x
  have hx := congrFun h (rootLift x)
  simpa only [rootHom_rootLift F T n] using hx

/-- A uniform root-coordinate expansion for one spanning functional gives
the target's finite set on the full torus, uniformly for all functionals. -/
theorem assemble
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (eligible : Module.Dual ℂ V → Prop) (ℓ₀ : Module.Dual ℂ V)
    (hspan : ∀ ℓ, eligible ℓ → ∃ c : ℂ, ℓ = c • ℓ₀) :
    letI := T.topology
    ∀ (X : Finset ((Fin n → F.Carrierˣ) → ℂ)),
      (∀ χ ∈ X, IsFiniteFunction χ) →
      (∀ v : V, ∃ φ : ((Fin n → F.Carrierˣ) → ℂ) →
          HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
        ∀ x, ℓ₀ (ρ (torus (rootLift x)) v) =
          ∑ χ ∈ X, φ χ (fun i => (x i : F.Carrier)) * χ x) →
      ∃ Y : Finset ((Fin (n + 1) → F.Carrierˣ) → ℂ),
        (∀ χ ∈ Y, IsFiniteFunction χ) ∧
        ∀ ℓ, eligible ℓ → ∀ v : V,
          ∃ Φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) →
              HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
            ∀ a, a (Fin.last n) = 1 →
              ℓ (ρ (torus a) v) = ∑ χ ∈ Y, Φ χ (roots a) * χ a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro X hX hroot
  classical
  let pull : ((Fin n → F.Carrierˣ) → ℂ) →
      ((Fin (n + 1) → F.Carrierˣ) → ℂ) := fun χ a => χ (rootHom a)
  have hpull : Function.Injective pull := pullback_injective F T n
  have hleft (χ : (Fin n → F.Carrierˣ) → ℂ) :
      (fun x => pull χ (rootLift x)) = χ := by
    funext x
    exact congrArg χ (rootHom_rootLift F T n x)
  refine ⟨X.image pull, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hχ
    exact finiteFunction_pullback (hX ξ hξ)
  · intro ℓ hℓ v
    obtain ⟨c, rfl⟩ := hspan ℓ hℓ
    obtain ⟨φ, hφ⟩ := hroot v
    refine ⟨fun χ => c • φ (fun x => χ (rootLift x)), ?_⟩
    intro a ha
    change c * ℓ₀ (ρ (torus a) v) = _
    have heq := hφ (rootHom a)
    rw [rootLift_rootHom F T n a ha] at heq
    rw [heq, Finset.mul_sum]
    rw [Finset.sum_image (fun χ _ ξ _ h => hpull h)]
    apply Finset.sum_congr rfl
    intro χ hχ
    dsimp only
    rw [hleft]
    change c * (φ χ (roots a) * χ (rootHom a)) =
      (c * φ χ (roots a)) * χ (rootHom a)
    exact (mul_assoc _ _ _).symm

end Padic

/-- The parent target's conjunction form of covariance supplies the bundled
functional required by the elementary support estimate. -/
theorem mem_glFunctionals_of_raw
    {K : Type uF} [CommRing K] [TopologicalSpace K] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ψ ≠ 1)
    (hu : ∀ x, ‖ψ x‖ = 1) (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ g : GeneralLinear (n + 1) K,
      ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) :
    ℓ ∈ Whittaker.glFunctionals
      (HarmonicAnalysis.UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) n ρ := by
  apply (Whittaker.mem_glFunctionals_iff_entrywise _ ρ ℓ).mpr
  intro g hlow hdiag v
  exact hℓ g ⟨hlow, hdiag⟩ v

end Langlands.WhittakerLastEntryOne
