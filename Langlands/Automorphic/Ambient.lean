import Langlands.Global.AdelicGL
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Ambient adelic function representations

The carrier consists of actual complex-valued functions on the adelic matrix
group. These are ambient spaces, before the archimedean analytic conditions
and cuspidality defining automorphic forms.
-/

noncomputable section

universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual rational-left-invariant function space, using Mathlib coinduction. -/
abbrev RationalInvariantFunctions :=
  Representation.coindV (AdelicGL.rational K n)
    (Representation.trivial ℂ (RationalGL K n) ℂ)

/-- Right translation on rational-left-invariant functions. -/
def rationalRightAction :
    Representation ℂ (AdelicGL K n) (RationalInvariantFunctions K n) :=
  Representation.coind (AdelicGL.rational K n)
    (Representation.trivial ℂ (RationalGL K n) ℂ)

@[simp]
theorem rationalRightAction_apply (g x : AdelicGL K n)
    (f : RationalInvariantFunctions K n) :
    (rationalRightAction K n g f).val x = f.val (x * g) := rfl

theorem rational_invariance (f : RationalInvariantFunctions K n)
    (γ : RationalGL K n) (x : AdelicGL K n) :
    f.val (AdelicGL.rational K n γ * x) = f.val x := f.property γ x

/-- Continuity is preserved by the actual right-translation representation. -/
def continuousSubrepresentation : Subrepresentation (rationalRightAction K n) where
  toSubmodule := (continuousSubmodule (AdelicGL K n) ℂ ℂ).comap
    (RationalInvariantFunctions K n).subtype
  apply_mem_toSubmodule g f hf := by
    change Continuous (fun x => f.val (x * g))
    exact hf.comp (continuous_id.mul continuous_const)

/-- Continuous rational-left-invariant functions, with their inherited linear structure. -/
abbrev ContinuousRationalFunctions := (continuousSubrepresentation K n).toSubmodule

/-- The right action on the continuous ambient function space. -/
def continuousRightAction :
    Representation ℂ (AdelicGL K n) (ContinuousRationalFunctions K n) :=
  (continuousSubrepresentation K n).toRepresentation

namespace ContinuousRationalFunctions

/-- Evaluation in the actual underlying function. -/
def evaluate (f : ContinuousRationalFunctions K n) (x : AdelicGL K n) : ℂ :=
  f.val.val x

theorem continuous_evaluate (f : ContinuousRationalFunctions K n) :
    Continuous (evaluate K n f) := f.property

@[simp]
theorem evaluate_rightAction (g x : AdelicGL K n) (f : ContinuousRationalFunctions K n) :
    evaluate K n (continuousRightAction K n g f) x = evaluate K n f (x * g) := rfl

theorem evaluate_rational (f : ContinuousRationalFunctions K n)
    (γ : RationalGL K n) (x : AdelicGL K n) :
    evaluate K n f (AdelicGL.rational K n γ * x) = evaluate K n f x :=
  rational_invariance K n f.val γ x

/-- The faithful realization in continuous functions on the adelic group. -/
def toContinuousMap : ContinuousRationalFunctions K n →ₗ[ℂ] C(AdelicGL K n, ℂ) where
  toFun f := ⟨evaluate K n f, continuous_evaluate K n f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toContinuousMap_injective : Function.Injective (toContinuousMap K n) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun c : C(AdelicGL K n, ℂ) => (c : AdelicGL K n → ℂ)) h

/-- The subspace topology from compact-open continuous functions. -/
instance instTopologicalSpace : TopologicalSpace (ContinuousRationalFunctions K n) :=
  TopologicalSpace.induced (toContinuousMap K n) inferInstance

theorem isEmbedding_toContinuousMap :
    Topology.IsEmbedding (toContinuousMap K n) :=
  ⟨Topology.IsInducing.induced _, toContinuousMap_injective K n⟩

/-- Each fixed right translation is continuous for the chosen compact-open topology. -/
theorem continuous_rightAction (g : AdelicGL K n) :
    Continuous (continuousRightAction K n g) := by
  rw [continuous_induced_rng]
  let r : C(AdelicGL K n, AdelicGL K n) :=
    ⟨fun x => x * g, continuous_id.mul continuous_const⟩
  have h : Continuous (fun f : C(AdelicGL K n, ℂ) => f.comp r) :=
    ContinuousMap.continuous_precomp r
  exact h.comp (show Continuous (toContinuousMap K n) from continuous_induced_dom)

end ContinuousRationalFunctions

open ContinuousRationalFunctions

/-- The actual scalar-idele character pulled back from an idele-class character. -/
def centralIdeleCharacter
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    IdeleGroup (𝓞 K) K →ₜ* ℂˣ where
  toMonoidHom := χ.toMonoidHom.comp
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
  continuous_toFun := χ.continuous.comp QuotientGroup.continuous_mk

@[simp]
theorem centralIdeleCharacter_principal
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (a : Kˣ) :
    centralIdeleCharacter K χ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
  change χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
    (IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1
  have h : QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
      (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  rw [h, map_one]

/-- The subrepresentation with the specified idele-class central character. -/
def centralCharacterSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    Subrepresentation (continuousRightAction K n) where
  toSubmodule :=
    { carrier := {f | ∀ (z : IdeleGroup (𝓞 K) K) (x : AdelicGL K n),
        evaluate K n f (AdelicGL.scalar K n z * x) =
          (centralIdeleCharacter K χ z : ℂ) * evaluate K n f x}
      zero_mem' := by simp [evaluate]
      add_mem' := by
        intro f g hf hg z x
        change evaluate K n f _ + evaluate K n g _ = _
        rw [hf, hg]
        exact (mul_add _ _ _).symm
      smul_mem' := by
        intro c f hf z x
        change c * evaluate K n f _ = _ * (c * evaluate K n f x)
        rw [hf]
        ac_rfl }
  apply_mem_toSubmodule g f hf := by
    intro z x
    change evaluate K n f ((AdelicGL.scalar K n z * x) * g) =
      (centralIdeleCharacter K χ z : ℂ) * evaluate K n f (x * g)
    simpa only [mul_assoc] using hf z (x * g)

/-- An ambient central-character space, not yet the automorphic-form subspace. -/
abbrev CentralCharacterFunctions
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  (centralCharacterSubrepresentation K n χ).toSubmodule

/-- Right translation on the specified-central-character ambient space. -/
def centralCharacterRightAction (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    Representation ℂ (AdelicGL K n) (CentralCharacterFunctions K n χ) :=
  (centralCharacterSubrepresentation K n χ).toRepresentation

theorem scalar_rightAction (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (z : IdeleGroup (𝓞 K) K) (f : CentralCharacterFunctions K n χ) :
    centralCharacterRightAction K n χ (AdelicGL.scalar K n z) f =
      (centralIdeleCharacter K χ z : ℂ) • f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate K n f.val (x * AdelicGL.scalar K n z) =
    (centralIdeleCharacter K χ z : ℂ) * evaluate K n f.val x
  rw [← (AdelicGL.scalar_commute K n z x).eq]
  exact f.property z x

/-- Right-invariance under an explicitly supplied finite adelic level subgroup. -/
def levelSubmodule (L : Subgroup (FiniteAdelicGL K n)) :
    Submodule ℂ (ContinuousRationalFunctions K n) where
  carrier := {f | ∀ l : L, continuousRightAction K n (AdelicGL.ofFinite K n l) f = f}
  zero_mem' := by simp
  add_mem' hf hg l := by simp [map_add, hf l, hg l]
  smul_mem' c f hf l := by simp [map_smul, hf l]

/-- Finite level means invariance under some actual compact open subgroup. -/
def HasFiniteLevel (f : ContinuousRationalFunctions K n) : Prop :=
  ∃ L : Subgroup (FiniteAdelicGL K n),
    IsOpen (L : Set (FiniteAdelicGL K n)) ∧
    IsCompact (L : Set (FiniteAdelicGL K n)) ∧ f ∈ levelSubmodule K n L

/-- Span of the orbit under a specified subgroup of the infinite adelic group. -/
def infiniteOrbitSpan (U : Subgroup (InfiniteAdelicGL K n))
    (f : ContinuousRationalFunctions K n) :
    Submodule ℂ (ContinuousRationalFunctions K n) :=
  Submodule.span ℂ (Set.range fun u : U =>
    continuousRightAction K n (AdelicGL.ofInfinite K n u) f)

/-- Finiteness of the actual right orbit span; maximal compactness is not assumed. -/
def IsInfiniteFinite (U : Subgroup (InfiniteAdelicGL K n))
    (f : ContinuousRationalFunctions K n) : Prop :=
  Module.Finite ℂ (infiniteOrbitSpan K n U f)

end Langlands.Automorphic
