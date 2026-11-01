import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct
import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
import Langlands.Representation.Derivative.LevelCalculus
import Mathlib.RingTheory.Flat.Basic

/-!
# Nonzero derivatives of subrepresentations of left mixed products

Zelevinsky (1980), §5.3, first half: let `τ` be a representation of `P_(r+1)` with an
injection `τ ↪ (Φ̂⁺)^(l-1) Ψ⁺(θ)` for a representation `θ` of `GL_(r+1-l)`. Then every nonzero
subrepresentation `W` of the left mixed product `ρ × τ` has a nonzero derivative of order `l`.

The proof follows Zelevinsky: `W ↪ ρ × τ ↪ ρ' × (Φ̂⁺)^(l-1) Ψ⁺(θ)`, where `ρ'` is `ρ` on a
lifted carrier. Peeling one `Φ̂⁺` at a time with the embedding
`ρ' × Φ̂⁺(σ) ↪ Φ̂⁺(ρ' × σ)` and the adjunction `Φ⁻ ⊣ Φ̂⁺` gives a nonzero intertwiner
`(Φ⁻)^(l-1) W → ρ' × Ψ⁺(θ)`. The radical `V` acts trivially on `ρ' × Ψ⁺(θ)`, so the
coinvariants `Ψ⁻ (Φ⁻)^(l-1) W = W^(l)` are nonzero.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis

universe uA uB uV₁ uV₂ uV uF uG uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## The radical acts trivially on `ρ × σ` when it does on `σ` -/

section Radical

variable (T : F.TopologicalData) {k n : ℕ}

/-- `χ_L(1, p) = 1` for the case (II) image of a radical element of `P_(k+n+1)`. -/
theorem leftLeviCharacter_leftRadical_eq_one (u : radical (k + n) F.Carrier) :
    (T.leftLeviCharacter k n (leftProjection (leftRadical u)) : ℂ) = 1 := by
  have hν : T.determinantNorm (n + 1) (leftProjection (leftRadical u)).2.val = 1 :=
    T.determinantNorm_radical' (⟨_, leftProjection_leftRadical_snd_mem u⟩ : radical n F.Carrier)
  rw [T.leftLeviCharacter_apply, leftProjection_leftRadical_fst, map_one, hν]
  simp

/-- If `V_(n+1)` acts trivially on `B`, then `V_(k+n+1)` acts trivially on `A × B`. -/
theorem leftMixedProduct_radical_eq_self
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
    (hX : letI := T.topology
      ∀ (u : radical n F.Carrier) (v : X.2), X.2.representation (u : mirabolic n F.Carrier) v = v)
    (u : radical (k + n) F.Carrier)
    (f : letI := T.topology; (T.leftMixedProductFunctor k n).obj X) :
    letI := T.topology
    ((T.leftMixedProductFunctor k n).obj X).representation (u : mirabolic (k + n) F.Carrier) f =
      f := by
  let _ := T.topology
  apply T.leftMixedEval_injective X
  funext x
  rw [T.leftMixedProductFunctor_action]
  let w : radical (k + n) F.Carrier :=
    ⟨x * u * x⁻¹, (radical_normal (n := k + n) (F := F.Carrier)).conj_mem _ u.property x⟩
  have hw : x * (u : mirabolic (k + n) F.Carrier) =
      ((leftRadical w : leftSubgroup k n F.Carrier) : mirabolic (k + n) F.Carrier) * x := by
    change x * (u : mirabolic (k + n) F.Carrier) = x * u * x⁻¹ * x
    group
  have hp : X.2.representation (leftProjection (leftRadical w)).2 = 1 :=
    LinearMap.ext fun v => hX ⟨_, leftProjection_leftRadical_snd_mem w⟩ v
  rw [hw, T.leftMixedEval_covariant, leftLeviCharacter_leftRadical_eq_one]
  simp only [one_smul, leftInducingRepresentation_apply, leftProjection_leftRadical_fst, map_one,
    hp, TensorProduct.map_one, Module.End.one_apply]

end Radical

/-! ## Detecting `Ψ⁻` by a map into a representation with trivial radical action -/

section Psi

variable (T : F.TopologicalData) {m : ℕ}

/-- A nonzero intertwiner `A → B`, where `V_(m+1)` acts trivially on `B`, forces `Ψ⁻(A) ≠ 0`:
the intertwiner factors through the coinvariants. -/
theorem nontrivial_psiMinus_of_ne_zero
    (A : letI := T.topology; SmoothRep.{0, uF, uA} ℂ (mirabolic m F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uB} ℂ (mirabolic m F.Carrier))
    (hB : letI := T.topology
      ∀ (u : radical m F.Carrier) (v : B), B.representation (u : mirabolic m F.Carrier) v = v)
    (Φ : letI := T.topology; A.representation.IntertwiningMap B.representation)
    (hΦ : Φ ≠ 0) :
    letI := T.topology
    Nontrivial ((psiMinus T m).obj A) := by
  let _ := T.topology
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hΦ
  have hl : ∀ (u : radical m F.Carrier) (v : A),
      Φ.toLinearMap (A.representation (u : mirabolic m F.Carrier) v) =
        (((1 : radical m F.Carrier →* ℂˣ) u : ℂˣ) : ℂ) • Φ.toLinearMap v := by
    intro u v
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact (Representation.IntertwiningMap.isIntertwining _ _ Φ _ v).trans (hB u (Φ v))
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h0 : psiMinusQuotient T m A v = 0 := @Subsingleton.elim _ h _ _
  rw [← Jacquet.Localization.lift_mk A.representation (radical m F.Carrier) 1 Φ.toLinearMap hl v]
  change Jacquet.Localization.lift A.representation (radical m F.Carrier) 1 Φ.toLinearMap hl
    (psiMinusQuotient T m A v) = 0
  rw [h0, map_zero]

end Psi

/-! ## Peeling `Φ̂⁺` off a left mixed product -/

section Iterate

/- Unfolding `phiHatPlus` while unifying `(Φ̂⁺)^(j+1)` with `Φ̂⁺ ∘ (Φ̂⁺)^j` exhausts the heartbeat
budget; these comparisons only need `phiHatPlusIterate` and `Functor.comp` unfolded. -/
attribute [local irreducible] phiHatPlus

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {k : ℕ}

/-- The base case `j = 0`: a nonzero intertwiner `A → B` with `B = ρ × Y` forces `Ψ⁻ A ≠ 0`.

The target is a separate object `B` with an object equation `hB`: the callers' targets differ
from `ρ × Y` only up to definitional unfolding, and converting intertwiner types between such
objects is expensive, while the object equation is checked cheaply by `rfl`. -/
theorem nontrivial_mirabolicDerivative_of_leftPhiHatIterate_zero
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)) (m N : ℕ)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic m F.Carrier))
    (hY : letI := T.topology
      ∀ (u : radical m F.Carrier) (v : Y), Y.representation (u : mirabolic m F.Carrier) v = v)
    (A : letI := T.topology; SmoothRep.{0, uF, uA} ℂ (mirabolic (k + m) F.Carrier))
    (h : k + m = N + 0)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + m) F.Carrier))
    (hB : letI := T.topology; B = (T.leftMixedProductFunctor k m).obj (ρ, Y))
    (Φ : letI := T.topology; A.representation.IntertwiningMap B.representation)
    (hΦ : Φ ≠ 0) :
    letI := T.topology
    Nontrivial ((mirabolicDerivative T ψ N 0).obj ((mirabolicRankCast T h).obj A)) := by
  let _ := T.topology
  subst hB
  obtain rfl : N = k + m := by omega
  have := nontrivial_psiMinus_of_ne_zero T A ((T.leftMixedProductFunctor k m).obj (ρ, Y))
    (leftMixedProduct_radical_eq_self T (ρ, Y) hY) Φ hΦ
  exact this

/-- The inductive step: compose with `ρ × Φ̂⁺(Z) ↪ Φ̂⁺(ρ × Z)` and pass through the adjunction
`Φ⁻ ⊣ Φ̂⁺`. -/
theorem nontrivial_mirabolicDerivative_of_leftPhiHatIterate_succ
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)) (j n : ℕ)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (ih : letI := T.topology
      ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (k + (n + j)) F.Carrier))
        (h : k + (n + j) = k + n + j)
        (B : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + (n + j)) F.Carrier)),
        B = (T.leftMixedProductFunctor k (n + j)).obj
          (ρ, (phiHatPlusIterate.{uV} T ψ n j).obj X) →
        ∀ Φ : A.representation.IntertwiningMap B.representation, Φ ≠ 0 →
          Nontrivial ((mirabolicDerivative T ψ (k + n) j).obj ((mirabolicRankCast T h).obj A)))
    (A : letI := T.topology; SmoothRep.{0, uF, uA} ℂ (mirabolic (k + (n + (j + 1))) F.Carrier))
    (h : k + (n + (j + 1)) = k + n + (j + 1))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + (n + (j + 1))) F.Carrier))
    (hB : letI := T.topology
      B = (T.leftMixedProductFunctor k (n + (j + 1))).obj
        (ρ, (phiHatPlusIterate.{uV} T ψ n (j + 1)).obj X))
    (Φ : letI := T.topology; A.representation.IntertwiningMap B.representation)
    (hΦ : Φ ≠ 0) :
    letI := T.topology
    Nontrivial ((mirabolicDerivative T ψ (k + n) (j + 1)).obj ((mirabolicRankCast T h).obj A)) := by
  let _ := T.topology
  let Z := (phiHatPlusIterate.{uV} T ψ n j).obj X
  have hB' : B = leftPhiHatSource.{uV, uF} T ψ ρ Z := hB
  clear hB
  subst hB'
  let E := leftPhiHatEmbedding.{uV, uF} T ψ ρ Z
  have hΦ₁ : E.comp Φ ≠ 0 := by
    intro h0
    apply hΦ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply leftPhiHatEmbedding_injective.{uV, uF} T ψ ρ Z
    change E (Φ v) = E 0
    rw [map_zero]
    exact congrArg (fun φ => φ v) h0
  have hΦ₂ : phiHatPlusAdjunction T ψ (k + (n + j)) A
      ((T.leftMixedProductFunctor k (n + j)).obj (ρ, Z)) (E.comp Φ) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).mpr hΦ₁
  have h' : k + (n + j) = k + n + j := by omega
  have key := ih ((phiMinus T ψ (k + (n + j))).obj A) h'
    ((T.leftMixedProductFunctor k (n + j)).obj (ρ, Z)) rfl _ hΦ₂
  rw [LevelCalculus.mirabolicDerivative_succ_cast_obj (M := k + (n + j)) T ψ h h' A]
  exact key

/-- Let `V_(n+1)` act trivially on `X`. A nonzero intertwiner `A → B`, where
`B = ρ × (Φ̂⁺)^j X`, forces the derivative `Ψ⁻ (Φ⁻)^j A` to be nonzero. -/
theorem nontrivial_mirabolicDerivative_of_leftPhiHatIterate
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)) :
    letI := T.topology
    ∀ (j n : ℕ) (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)),
      (∀ (u : radical n F.Carrier) (v : X), X.representation (u : mirabolic n F.Carrier) v = v) →
      ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (k + (n + j)) F.Carrier))
        (h : k + (n + j) = k + n + j)
        (B : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + (n + j)) F.Carrier)),
        B = (T.leftMixedProductFunctor k (n + j)).obj
          (ρ, (phiHatPlusIterate.{uV} T ψ n j).obj X) →
        ∀ Φ : A.representation.IntertwiningMap B.representation, Φ ≠ 0 →
          Nontrivial ((mirabolicDerivative T ψ (k + n) j).obj ((mirabolicRankCast T h).obj A)) := by
  let _ := T.topology
  intro j
  induction j with
  | zero =>
    intro n X hX A h B hB Φ hΦ
    exact nontrivial_mirabolicDerivative_of_leftPhiHatIterate_zero T ψ ρ (n + 0) (k + n)
      ((phiHatPlusIterate.{uV} T ψ n 0).obj X) (fun u v => hX u v) A h B hB Φ hΦ
  | succ j ih =>
    intro n X hX A h B hB Φ hΦ
    exact nontrivial_mirabolicDerivative_of_leftPhiHatIterate_succ T ψ ρ j n X (ih n X hX) A h B hB
      Φ hΦ

/-- The same with the target transported along a rank equality `n + j = r`. -/
theorem nontrivial_mirabolicDerivative_of_leftPhiHatIterate_cast
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    {n j r : ℕ} (e : n + j = r)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (hX : letI := T.topology
      ∀ (u : radical n F.Carrier) (v : X), X.representation (u : mirabolic n F.Carrier) v = v)
    (A : letI := T.topology; SmoothRep.{0, uF, uA} ℂ (mirabolic (k + r) F.Carrier))
    (h : k + r = k + n + j)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier))
    (hB : letI := T.topology
      B = (T.leftMixedProductFunctor k r).obj
        (ρ, (mirabolicRankCast T e).obj ((phiHatPlusIterate.{uV} T ψ n j).obj X)))
    (Φ : letI := T.topology; A.representation.IntertwiningMap B.representation)
    (hΦ : Φ ≠ 0) :
    letI := T.topology
    Nontrivial ((mirabolicDerivative T ψ (k + n) j).obj ((mirabolicRankCast T h).obj A)) := by
  subst e
  exact nontrivial_mirabolicDerivative_of_leftPhiHatIterate T ψ ρ j n X hX A h B hB Φ hΦ

end Iterate

/-! ## Left mixed products of intertwiners across carrier universes -/

section Map

variable (T : F.TopologicalData) {k r : ℕ}

/-- The left mixed product of two intertwiners, whose factors may have different carrier
universes: `f ↦ (x ↦ (α ⊗ β)(f(x)))`. -/
def leftMixedProductMap
    {ρ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (GeneralLinear k F.Carrier)}
    {τ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (mirabolic r F.Carrier)}
    {ρ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (GeneralLinear k F.Carrier)}
    {τ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (mirabolic r F.Carrier)}
    (α : letI := T.topology; ρ₁.representation.IntertwiningMap ρ₂.representation)
    (β : letI := T.topology; τ₁.representation.IntertwiningMap τ₂.representation) :
    letI := T.topology
    ((T.leftMixedProductFunctor k r).obj (ρ₁, τ₁)).representation.IntertwiningMap
      ((T.leftMixedProductFunctor k r).obj (ρ₂, τ₂)).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.compactInducedMap (leftSubgroup k r F.Carrier)
    (twistIntertwining (T.leftCharacter k r).toMonoidHom
      (MixedProductTensor.pullbackMap leftProjection (MixedProductTensor.externalMap α β)))

/-- The product map acts on values by `α ⊗ β`. -/
theorem leftMixedEval_leftMixedProductMap
    {ρ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (GeneralLinear k F.Carrier)}
    {τ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (mirabolic r F.Carrier)}
    {ρ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (GeneralLinear k F.Carrier)}
    {τ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (mirabolic r F.Carrier)}
    (α : letI := T.topology; ρ₁.representation.IntertwiningMap ρ₂.representation)
    (β : letI := T.topology; τ₁.representation.IntertwiningMap τ₂.representation)
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj (ρ₁, τ₁))
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval (ρ₂, τ₂) (leftMixedProductMap T α β f) x =
      TensorProduct.map α.toLinearMap β.toLinearMap (T.leftMixedEval (ρ₁, τ₁) f x) :=
  rfl

/-- Over `ℂ`, the product of two injective intertwiners is injective. -/
theorem leftMixedProductMap_injective
    {ρ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (GeneralLinear k F.Carrier)}
    {τ₁ : letI := T.topology; SmoothRep.{0, uF, uV₁} ℂ (mirabolic r F.Carrier)}
    {ρ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (GeneralLinear k F.Carrier)}
    {τ₂ : letI := T.topology; SmoothRep.{0, uF, uV₂} ℂ (mirabolic r F.Carrier)}
    (α : letI := T.topology; ρ₁.representation.IntertwiningMap ρ₂.representation)
    (β : letI := T.topology; τ₁.representation.IntertwiningMap τ₂.representation)
    (hα : letI := T.topology; Function.Injective α)
    (hβ : letI := T.topology; Function.Injective β) :
    letI := T.topology
    Function.Injective (leftMixedProductMap T α β) := by
  let _ := T.topology
  intro f g hfg
  apply T.leftMixedEval_injective (ρ₁, τ₁)
  funext x
  apply TensorProduct.map_injective_of_flat_flat α.toLinearMap β.toLinearMap hα hβ
  rw [← leftMixedEval_leftMixedProductMap, ← leftMixedEval_leftMixedProductMap, hfg]

end Map

/-! ## Nonzero subrepresentations under injective intertwiners -/

section Subtype

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An injective intertwiner restricts to a nonzero intertwiner on a nonzero subrepresentation. -/
theorem comp_subtype_ne_zero {A : SmoothRep.{0, uG, uA} ℂ G}
    (U : Subrepresentation A.representation) (hU : U ≠ ⊥)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (M : A.representation.IntertwiningMap σ) (hM : Function.Injective M) :
    M.comp (SmoothRep.hom (SmoothRep.subtype A U)) ≠ 0 := by
  have := LevelCalculus.subrepresentation_nontrivial U hU
  obtain ⟨w, hw⟩ := exists_ne (0 : SmoothRep.subrepresentation A U)
  intro h0
  apply hw
  apply SmoothRep.subtype_injective A U
  apply hM
  rw [map_zero, map_zero]
  exact congrArg (fun φ => φ w) h0

end Subtype

/-! ## Zelevinsky 5.3: nonzero order-`l` derivatives of subrepresentations -/

section Lower

attribute [local irreducible] phiHatPlus

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {k : ℕ}

/-- `V_(n+1)` acts trivially on the lifted `Ψ⁺(θ)`. -/
theorem liftObj_psiPlus_radical {n : ℕ}
    (θ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (u : radical n F.Carrier)
    (v : letI := T.topology; MixedProductTensor.liftObj.{uF, uV, uF} ((psiPlus T n).obj θ)) :
    letI := T.topology
    (MixedProductTensor.liftObj.{uF, uV, uF} ((psiPlus T n).obj θ)).representation
      (u : mirabolic n F.Carrier) v = v :=
  congrArg ULift.up (psiPlus_radical T n θ u v.down)

/-- Ze80 §5.3: if `τ` embeds into `(Φ̂⁺)^(l-1) Ψ⁺(θ)`, then every nonzero subrepresentation of
`ρ × τ` has a nonzero derivative of order `l`.

The implicit lifted factor `ρ₂ := ρ'` is passed explicitly: inferring it from the type of `α`
would unify `?ρ₂.representation` with `lift ρ.representation`, which is expensive. -/
theorem hasNonzeroDerivative_leftMixed_subrepresentation
    {r l : ℕ} (hl : 0 < l ∧ l ≤ r + 1)
    (ρ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (τ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (θ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r + 1 - l) F.Carrier))
    (β : letI := T.topology
      τ.representation.IntertwiningMap
        ((mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ r l hl).obj θ).representation)
    (hβ : letI := T.topology; Function.Injective β)
    (U : letI := T.topology
      Subrepresentation ((T.leftMixedProductFunctor k r).obj (ρ, τ)).representation)
    (hU : U ≠ ⊥) :
    letI := T.topology
    HasNonzeroDerivative T ψ
      (SmoothRep.subrepresentation ((T.leftMixedProductFunctor k r).obj (ρ, τ)) U) l := by
  let _ := T.topology
  let π := (T.leftMixedProductFunctor k r).obj (ρ, τ)
  let α := (MixedProductTensor.liftEquiv.{uF, uV, uF} ρ.representation).toIntertwiningMap
  have hα : Function.Injective α := fun a b hab => congrArg ULift.down hab
  let M := leftMixedProductMap T (ρ₂ := MixedProductTensor.liftObj.{uF, uV, uF} ρ) α β
  have hM : Function.Injective M :=
    leftMixedProductMap_injective T (ρ₂ := MixedProductTensor.liftObj.{uF, uV, uF} ρ) α β hα hβ
  let Φ := M.comp (SmoothRep.hom (SmoothRep.subtype π U))
  have hΦ : Φ ≠ 0 := comp_subtype_ne_zero U hU M hM
  have hcore := nontrivial_mirabolicDerivative_of_leftPhiHatIterate_cast T ψ
    (MixedProductTensor.liftObj.{uF, uV, uF} ρ) (mirabolic_rank_eq_of_order hl).symm
    (MixedProductTensor.liftObj.{uF, uV, uF} ((psiPlus T (r + 1 - l)).obj θ))
    (liftObj_psiPlus_radical T θ) (SmoothRep.subrepresentation π U)
    (show k + r = k + (r + 1 - l) + (l - 1) by omega)
    ((T.leftMixedProductFunctor k r).obj (MixedProductTensor.liftObj.{uF, uV, uF} ρ,
      (mirabolicDerivativeOfOrderRightAdjoint.{uV} T ψ r l hl).obj θ)) rfl Φ hΦ
  refine ⟨⟨hl.1, by omega⟩, ?_⟩
  exact (LevelCalculus.nontrivial_mirabolicDerivative_cast_congr T ψ (by omega) rfl _ _ _).mp hcore

end Lower

end Langlands.Derivative.Mirabolic
