import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof

/-!
# Homogeneity and the unit of the mirabolic derivative adjunction

Zelevinsky 1980, Proposition 5.1, (1) ⇔ (3), for the actual order-indexed derivative
`mirabolicDerivativeOfOrder N l` on `P_(N+1)` and its published right adjoint
`Y = mirabolicDerivativeOfOrderRightAdjoint N l`:

* the derivative functors carry injective intertwiners to injective intertwiners;
* the kernel of the unit `τ → Y(τ^(l))`, the source's `Ker A`, has zero order-`l`
  derivative;
* if every nonzero invariant subspace of `τ` has a nonzero order-`l` derivative, in
  particular if `τ` is homogeneous of level `l`, the unit `τ → Y(τ^(l))` is injective;
* if `π` admits an injective intertwiner into some `Y θ` and has level at most `l`, then `π`
  is homogeneous, and of level `l` when nonzero;
* for `τ` of level `l > 0`: `τ` is homogeneous if and only if the unit is injective.

Exactness enters only through the published theorem `Mirabolic.minusExactness`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uA uV uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Derivatives preserve injections -/

/-- The order-`l` derivative carries injective intertwiners to injective intertwiners. -/
theorem mirabolicDerivativeOfOrder_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f)) := by
  let := T.topology
  intro A B f hf
  exact LevelCalculus.map_injective_of_exact
    (LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder T ψ
      (Mirabolic.minusExactness.{uF, uV} F T) N l hl) f hf

/-- Level is monotone along injective intertwiners. -/
theorem level_mono_of_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) → level T ψ A ≤ level T ψ B :=
  fun f hf => LevelCalculus.level_le_of_injective T ψ (Mirabolic.minusExactness.{uF, uV} F T) f hf

/-! ## Zelevinsky 5.1 (1) ⇒ (3): injectivity of the unit -/

/-- The kernel of the unit `A → Y(A^(l))`, as a smooth subrepresentation of `A`: the
source's `Ker A`. -/
def mirabolicDerivativeOfOrderUnitKer (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) →
      SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) :=
  letI := T.topology
  fun A => SmoothRep.subrepresentation A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker

/-- The kernel of the unit `A → Y(A^(l))` has zero order-`l` derivative. -/
theorem subsingleton_mirabolicDerivativeOfOrder_unit_ker (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ N l hl).obj
        (mirabolicDerivativeOfOrderUnitKer T ψ N l hl A)) := by
  let := T.topology
  intro A
  change Subsingleton ((mirabolicDerivativeOfOrder T ψ N l hl).obj
    (SmoothRep.subrepresentation A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker))
  have hcomp : (mirabolicDerivativeOfOrderUnit T ψ N l hl A).comp
      (SmoothRep.hom (SmoothRep.subtype A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker)) =
        0 := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact x.2
  have h0 := mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp T ψ N l hl _ hcomp
  have hinj := mirabolicDerivativeOfOrder_map_injective T ψ N l hl
    (SmoothRep.subtype A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker)
    (SmoothRep.subtype_injective A _)
  refine ⟨fun x y => hinj ?_⟩
  rw [h0]
  rfl

/-- If every nonzero invariant subspace of `A` has a nonzero order-`l` derivative, the unit
`A → Y(A^(l))` is injective. -/
theorem mirabolicDerivativeOfOrderUnit_injective_of_forall (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ U : Subrepresentation A.representation, U ≠ ⊥ →
        HasNonzeroDerivative T ψ (SmoothRep.subrepresentation A U) l) →
      Function.Injective (mirabolicDerivativeOfOrderUnit T ψ N l hl A) := by
  let := T.topology
  intro A h
  have hK : (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker = ⊥ := by
    by_contra hne
    obtain ⟨_, hn⟩ := h _ hne
    exact (not_nontrivial_iff_subsingleton.mpr
      (subsingleton_mirabolicDerivativeOfOrder_unit_ker T ψ N l hl A)) hn
  intro x y hxy
  have hmem : x - y ∈ (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker := by
    change mirabolicDerivativeOfOrderUnit T ψ N l hl A (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [hK] at hmem
  exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem)

/-- Zelevinsky 1980, 5.1 (1) ⇒ (3): for `A` homogeneous of level `l`, the unit
`A → Y(A^(l))` is injective. -/
theorem mirabolicDerivativeOfOrderUnit_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      IsHomogeneous T ψ A → level T ψ A = l →
        Function.Injective (mirabolicDerivativeOfOrderUnit T ψ N l hl A) := by
  let := T.topology
  intro A hA hlev
  apply mirabolicDerivativeOfOrderUnit_injective_of_forall T ψ N l hl A
  intro U hU
  have h := hA U hU
  have hne : level T ψ (SmoothRep.subrepresentation A U) ≠ 0 := by
    rw [h, hlev]
    exact hl.1.ne'
  have hd := LevelCalculus.hasNonzeroDerivative_level T ψ _ hne
  rwa [h, hlev] at hd

/-- In a homogeneous representation of level `l > 0`, the source of every injective
intertwiner from a nonzero representation has a nonzero order-`l` derivative and no nonzero
derivative of higher order. -/
theorem hasNonzeroDerivative_of_isHomogeneous (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N l : ℕ} (hl : 0 < l) :
    letI := T.topology
    ∀ {W X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)}, IsHomogeneous T ψ X →
      level T ψ X = l → ∀ (f : W ⟶ X), Function.Injective (SmoothRep.hom f) → Nontrivial W →
        HasNonzeroDerivative T ψ W l ∧ ∀ j, l < j → ¬ HasNonzeroDerivative T ψ W j := by
  let := T.topology
  intro W X hX hlev f hf hW
  have hW' : level T ψ W = l :=
    (LevelCalculus.level_eq_of_isHomogeneous T ψ hX f hf hW).trans hlev
  refine ⟨?_, fun j hj hd => ?_⟩
  · have hd := LevelCalculus.hasNonzeroDerivative_level T ψ W (by omega)
    rwa [hW'] at hd
  · have := le_level_of_hasNonzeroDerivative T ψ W hd
    omega

/-! ## Zelevinsky 5.1 (3) ⇒ (1): homogeneity from an embedding into `Y` -/

/-- If `A` embeds into some `Y θ`, the source of every injective intertwiner from a nonzero
representation into `A` has a nonzero order-`l` derivative. No exactness is used. -/
theorem hasNonzeroDerivative_of_injective_rightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Function.Injective Φ →
        ∀ {W : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier)} (f : W ⟶ A),
          Function.Injective (SmoothRep.hom f) → Nontrivial W →
            HasNonzeroDerivative T ψ W l := by
  let := T.topology
  intro A θ Φ hΦ W f hf hW
  apply hasNonzeroDerivative_of_ne_zero T ψ N l hl W θ (Φ.comp (SmoothRep.hom f))
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  apply hf
  apply hΦ
  rw [map_zero, map_zero]
  exact congrArg (fun g => g x) h0

/-- If `A` embeds into some `Y θ` and is nonzero, its level is at least `l`. No exactness is
used. -/
theorem le_level_of_injective_rightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Function.Injective Φ → Nontrivial A → l ≤ level T ψ A := by
  let := T.topology
  intro A θ Φ hΦ hA
  exact le_level_of_hasNonzeroDerivative T ψ A
    (hasNonzeroDerivative_of_injective_rightAdjoint T ψ N l hl A θ Φ hΦ (𝟙 A)
      (fun _ _ h => h) hA)

/-- Zelevinsky 1980, 5.1 (3) ⇒ (1): if `A` embeds into some `Y θ` and has level at most `l`,
then `A` is homogeneous. -/
theorem isHomogeneous_of_injective_rightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Function.Injective Φ → level T ψ A ≤ l → IsHomogeneous T ψ A := by
  let := T.topology
  intro A θ Φ hΦ hA
  apply LevelCalculus.isHomogeneous_of_forall_injective T ψ A l
  intro W f hf hW
  apply le_antisymm
  · exact (level_mono_of_injective T ψ f hf).trans hA
  · exact le_level_of_hasNonzeroDerivative T ψ W
      (hasNonzeroDerivative_of_injective_rightAdjoint T ψ N l hl A θ Φ hΦ f hf hW)

/-- Under the hypotheses of `isHomogeneous_of_injective_rightAdjoint`, a nonzero `A` has
level exactly `l`. -/
theorem level_eq_of_injective_rightAdjoint (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier))
      (Φ : A.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ N l hl).obj θ).representation),
      Function.Injective Φ → level T ψ A ≤ l → Nontrivial A → level T ψ A = l := by
  intro A θ Φ hΦ hA hn
  exact le_antisymm hA (le_level_of_injective_rightAdjoint T ψ N l hl A θ Φ hΦ hn)

/-! ## Zelevinsky 5.1 (1) ⇔ (3) -/

/-- Zelevinsky 1980, 5.1 (1) ⇔ (3): a representation `A` of level `l > 0` is homogeneous if
and only if the unit `A → Y(A^(l))` is injective. -/
theorem isHomogeneous_iff_unit_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A = l →
      (IsHomogeneous T ψ A ↔ Function.Injective (mirabolicDerivativeOfOrderUnit T ψ N l hl A)) := by
  intro A hlev
  exact ⟨fun hA => mirabolicDerivativeOfOrderUnit_injective T ψ N l hl A hA hlev,
    fun hη => isHomogeneous_of_injective_rightAdjoint T ψ N l hl A _ _ hη hlev.le⟩

end Langlands.Derivative
