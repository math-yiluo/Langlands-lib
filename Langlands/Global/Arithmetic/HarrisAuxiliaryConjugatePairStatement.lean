import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Harris Proposition 4.8: the auxiliary conjugate pair

Three derived inputs of the exact-stabilizer branches (singleton and prime
orbit) of Harris (1998), Proposition 4.8, at the auxiliary conjugate pair
`v`, `conjPlace E v` of a CM field `E`:

* a conjugate self-dual cuspidal realization has a unitary central character;
* a conjugate self-dual cuspidal class supercuspidal at a finite place `v` is
  supercuspidal at the conjugate place `conjPlace E v`;
* a finite place of `E` above a rational prime `p` that splits in an imaginary
  quadratic subfield `K₀ ⊆ E` differs from its complex conjugate.

These are derived consequences of Harris's setup, not quotations; only the
statements are made here.
-/

universe u uV

set_option autoImplicit false

open NumberField Langlands.Automorphic

namespace Langlands.Global.Harris

/-- A conjugate self-dual cuspidal realization `π ≅ π^∨ ∘ c` of `GL_{r+1}` over
a CM field has a unitary central character. -/
def ConjugateSelfDualUnitaryCentralCharacterStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S : CuspidalOperatorRealization E r),
    S.isoClass.IsConjugateSelfDual →
    ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S

/-- A conjugate self-dual cuspidal class over a CM field that has a
supercuspidal component at a finite place `v` has a supercuspidal component at
the complex-conjugate place `conjPlace E v`. -/
def ConjugateSelfDualSupercuspidalConjPlaceStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
    c.IsConjugateSelfDual →
    c.HasSupercuspidalComponent.{u, uV} v →
    c.HasSupercuspidalComponent.{u, uV} (conjPlace E v)

/-- If the rational prime `p` splits in an imaginary quadratic subfield `K₀` of
the CM field `E`, then every finite place `v` of `E` above `p` differs from its
complex conjugate `conjPlace E v`. -/
def SplitPlaceNeConjPlaceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type u) [Field E] [NumberField E] [IsCMField E]
    (K₀ : IntermediateField ℚ E) (v : FinitePlace E),
    IsSplitImaginaryQuadratic p K₀ → (p : 𝓞 E) ∈ v.asIdeal → v ≠ conjPlace E v

end Langlands.Global.Harris
