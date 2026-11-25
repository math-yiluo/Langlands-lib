module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TotallySplit

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

universe u

/-! ## Setup

Stacks 00EO ("Zariski-local properties of modules and algebras") packages eight
statements. They are formalised here in the canonical Mathlib form: the localised
module / ring / algebra at `f i` is the canonical `LocalizedModule (Submonoid.powers (f i)) M`
/ `Localization.Away (f i)` / `Localization.Away (algebraMap R S (f i))`, and the
induced map on a localisation of `M` is `LocalizedModule.map (Submonoid.powers (f i))`.
The hypothesis `Ideal.span (Set.range f) = ⊤` is exactly the Stacks condition
`(f₁, …, fₙ) = R`.
-/

/-- **Stacks 00EO (2).** If each canonical localisation `M_{f i}` is finite over
`R_{f i}` and the `f i` generate the unit ideal, then `M` is a finite `R`-module. -/
@[stacks 00EO "(2)"]
theorem Module.Finite.of_localizationSpan_range
    {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Module.Finite (Localization.Away (f i))
                            (LocalizedModule (Submonoid.powers (f i)) M)) :
    Module.Finite R M :=
  Module.Finite.of_localizationSpan (Set.range f) hf (Set.forall_subtype_range_iff.mpr h)

/-!
### Stacks 00EP

Stacks 00EP — if `g₁, …, gₙ` generate the unit ideal of `S` and each `S_{gᵢ}` is of finite
type (resp. finite presentation) over `R`, then so is `S` — is Mathlib's
`Algebra.FiniteType.of_span_eq_top_target` and
`Algebra.FinitePresentation.of_span_eq_top_target`.
-/

end
