import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.RepresentationTheory.Intertwining

/-!
# Invariant positive Hermitian forms

An algebraic complex representation is unitarizable when it admits a positive
definite invariant Hermitian form. No norm or topology on its carrier is assumed.
-/

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A positive definite Hermitian form preserved by the actual action. -/
structure InvariantPositiveForm (ρ : Representation ℂ G V)
    extends toInnerProductCore : InnerProductSpace.Core ℂ V where
  /-- Every action operator preserves the form. -/
  invariant (g : G) (v w : V) : inner (ρ g v) (ρ g w) = inner v w

/-- Existence of an invariant positive definite Hermitian form, without a chosen
norm, topology, completion, or finite-dimensionality assumption on the carrier. -/
def IsUnitarizable (ρ : Representation ℂ G V) : Prop :=
  Nonempty (InvariantPositiveForm ρ)

namespace InvariantPositiveForm

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Pull an invariant form back along an injective intertwiner. Injectivity is
exactly what makes the pulled-back positive semidefinite form definite. -/
def comap (b : InvariantPositiveForm σ) (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : InvariantPositiveForm ρ where
  inner v w := b.inner (f v) (f w)
  conj_inner_symm v w := b.conj_inner_symm (f v) (f w)
  re_inner_nonneg v := b.re_inner_nonneg (f v)
  add_left v w x := by
    rw [map_add, b.add_left]
  smul_left v w c := by
    change b.inner (f (c • v)) (f w) = _
    rw [map_smul, b.smul_left]
  definite v hv := hf <| by simpa using b.definite (f v) hv
  invariant g v w := by
    rw [f.isIntertwining, f.isIntertwining, b.invariant]

@[simp]
theorem comap_inner (b : InvariantPositiveForm σ) (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (v w : V) :
    (b.comap f hf).inner v w = b.inner (f v) (f w) := rfl

/-- Transfer a form through an actual equivariant linear equivalence. -/
def ofEquiv (b : InvariantPositiveForm σ) (e : ρ.Equiv σ) :
    InvariantPositiveForm ρ :=
  b.comap e.toIntertwiningMap e.toLinearEquiv.injective

end InvariantPositiveForm

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An invariant subrepresentation of a unitarizable representation is
unitarizable, expressed using any injective intertwiner. -/
theorem IsUnitarizable.of_injective (hσ : IsUnitarizable σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) : IsUnitarizable ρ := by
  obtain ⟨b⟩ := hσ
  exact ⟨b.comap f hf⟩

/-- Unitarizability is invariant under an actual equivalence of representations. -/
theorem isUnitarizable_iff_of_equiv (e : ρ.Equiv σ) :
    IsUnitarizable ρ ↔ IsUnitarizable σ := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.ofEquiv e.symm⟩
  · rintro ⟨b⟩
    exact ⟨b.ofEquiv e⟩

end Langlands
