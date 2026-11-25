module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

universe uR uS uM uT

/-!
# Descent of finiteness properties

A finiteness property of a module or an algebra can often be checked after a base change and
deduced over the base ring. This file collects such descent statements for two kinds of base
change: along a faithfully flat ring map, and along a localization of the base ring or a
quotient of one.

Let `S` be faithfully flat over `R`. A module whose base change to `S` is of finite presentation,
finite projective or countably generated is again so over `R`, an `R`-algebra whose base change
is of finite type is again so over `R`, and being Noetherian and being reduced descend from `S`
to `R`. What drives the module statements is that a faithfully flat base change reflects
surjectivity, so a generating family or a family of relations found over `S` may be replaced by
one found over `R`.

Let `S ⊆ R` be a multiplicative subset. A finite `S⁻¹R`-module of the form `S⁻¹M` already comes
from `R`: finiteness of `S⁻¹M` is witnessed by the images of finitely many `x₁, …, xₙ ∈ M`, and
for the resulting `ψ : Rⁿ → M` the quotient `M' = Rⁿ ⧸ K` maps to `M` with `S⁻¹M' ≅ S⁻¹M` as soon
as `K ≤ Ker ψ` is `S`-saturated in `Ker ψ`. Taking `K = Ker ψ` makes `M'` finite; taking for `K`
the relations obtained by clearing denominators in a finite generating family of the relations
over `S⁻¹R` — available when `S⁻¹M` is finitely presented — makes `M'` of finite presentation.
The same argument run over a quotient `R'` of `S⁻¹R` writes a finite `R'`-module as a base change
`R' ⊗[R] M`.

Finally, a map `f : S →ₐ[R] S'` of `R`-algebras with `S` of finite type and `S'` of finite
presentation and flat is an isomorphism as soon as it is one modulo an ideal `I ⊆ R` all of whose
elements are nilpotent. Surjectivity of the reduction makes `f` surjective, and Nakayama applied
to `J = Ker f` makes it injective: `J` is finitely generated, injectivity of the reduction gives
`J ≤ IS`, flatness of `S'` upgrades this to `J ≤ IS · J`, and `IS` consists of nilpotents, hence
lies in the Jacobson radical of `S`.

## Main definitions

* `Module.CountablyGenerated`: a module is spanned by an at most countable set of its elements.

## Main results

* `Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat`: finite presentation of a module
  descends along a faithfully flat base change.
* `Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat`: projectivity of a finite
  module descends along a faithfully flat base change.
* `countablyGenerated_of_faithfullyFlat_baseChange`: countable generation descends along a
  faithfully flat base change.
* `descent_noetherian`, `RingHom.FaithfullyFlat.isReduced`: a ring faithfully flat over which
  there is a Noetherian, resp. reduced, ring is itself Noetherian, resp. reduced.
* `Algebra.FiniteType.iff_finiteType_tensorProduct`: an algebra is of finite type if and only if
  its faithfully flat base change is.
* `Module.exists_finite_isLocalizedModule_comp`: a module whose localization at `S` is a finite
  `S⁻¹R`-module receives a map from a finite `R`-module inducing an isomorphism of localizations,
  from a finitely presented one when `S⁻¹M` is finitely presented.
* `Module.exists_finite_isLocalizedModule_comp_atPrime`: the same at `S = p.primeCompl`.
* `Module.exists_finite_isBaseChange_of_surjective_algebraMap`: a finite module over a quotient
  `R'` of `S⁻¹R` is the base change of a finite `R`-module, of a finitely presented one when it
  is finitely presented.
* `AlgHom.bijective_of_bijective_quotientMapₐ_of_le_nilradical`: an algebra map that is an
  isomorphism modulo an ideal of nilpotents is an isomorphism.

## Implementation notes

Base changes and localizations are taken abstractly rather than through a model: a base change of
`M` to `S` is an `S`-module `N` with an `R`-linear `f : M →ₗ[R] N` such that `IsBaseChange S f`,
and a localization of `M` at `S` is an `R`-algebra `Rₛ` with `IsLocalization S Rₛ` together with
`f : M →ₗ[R] Mₛ` satisfying `IsLocalizedModule S f`. The concrete `M ⊗_R S`, `S⁻¹R` and `S⁻¹M`
instantiate this with `S ⊗[R] M` and `f = TensorProduct.mk R S M 1`, resp. `Localization S` and
`LocalizedModule S M` with `f = LocalizedModule.mkLinearMap S M`. Following Mathlib, the base
ring is written on the left of the tensor product where the sources write `M ⊗_R S`; the two
agree by `TensorProduct.comm`.

For the same reason the isomorphism a source asserts is pinned to the map inducing it, rather
than quantified over a choice of model: `IsBaseChange R' g` names the map `R' ⊗_R M → M'`,
`r' ⊗ x ↦ r' • g x`, and `IsLocalizedModule S (f ∘ₗ φ)` says that `Mₛ`, viewed through
`M' → M → Mₛ`, is a localization of `M'` at `S`. For a chosen localization `f' : M' →ₗ[R] M'ₛ`
the latter is equivalent, by `IsLocalizedModule.map_comp` and
`IsLocalizedModule.comp_iff_of_bijective_left`, to bijectivity of the induced
`IsLocalizedModule.map S f' f φ : S⁻¹M' → S⁻¹M`, from which `IsLocalizedModule.linearEquiv`
produces the isomorphism `S⁻¹M' ≅ S⁻¹M` the source asserts.

In 05GJ, 05N5 and 05N6 the two items are one statement about one module, the finitely presented
case appearing as an implication conjunct; this is equivalent to their conjunction, since a
finitely presented module is finite. The module produced lives in the universe of `R`, both
constructions being quotients of `Rⁿ`, and no injectivity is claimed: in the finitely presented
case `K` is in general strictly smaller than the module of relations. Rings are `CommRing`s and
modules `AddCommGroup`s because a quotient by a submodule is what the constructions produce.

Only two features of the ring map `R → S⁻¹(R/I)` of 05N5 are used: every element of `S` becomes
invertible, and the ring is generated by the image of `R` together with those inverses. That says
exactly that it is a quotient of `S⁻¹R`, so that is the hypothesis made, with the ideal `I`
playing no further role; the source's own case is `R' = Rₛ ⧸ I.map (algebraMap R Rₛ)` with
`hsurj := Ideal.Quotient.mk_surjective`. Lemma 05GJ is the case `S = p.primeCompl` of 05N6 and
nothing more, `IsLocalization.AtPrime Rₚ p` being an abbreviation for
`IsLocalization p.primeCompl Rₚ`.

That an ideal consists of nilpotents is spelled `I ≤ nilradical R`, the spelling that composes
with the radical and Jacobson API. The reduction `S/IS → S'/IS'` is `Ideal.quotientMapₐ` applied
to `f`, with its side condition `IS ≤ (IS').comap f` discharged inline so that the statement
carries no hypothesis a user must supply, and the conclusion is `Function.Bijective f` rather than
an `S ≃ₐ[R] S'`, the equivalence being `AlgEquiv.ofBijective f`. The source localises at each
prime of `S` in order to put the ideal that Nakayama consumes inside a Jacobson radical; here
`I ≤ nilradical R` puts `IS` inside the nilradical of `S` already, so no prime and no
localisation occur below.

The hypotheses are sharp. Flatness in 07RE cannot be dropped: over `R = k[ε]/(ε²)` with `I = (ε)`
the quotient map `R[x] → R[x]/(εx)` is bijective modulo `ε` and of finite presentation, and is
not injective, its target `R ⊕ ⨁_{n ≥ 1} R/(ε)` not being flat. Nor can finiteness of `S⁻¹M` in
05N6: for `S = 1` the conclusion says that `M` itself is finite. The finiteness hypothesis of
`Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat` is used by the argument but is not
needed for the truth of the conclusion — Theorem 05A9 removes it by a Kaplansky dévissage — so
the name records it, leaving the unqualified name for 05A9.

## References

* [StacksProject 00QP](https://stacks.math.columbia.edu/tag/00QP)
* [StacksProject 00QQ](https://stacks.math.columbia.edu/tag/00QQ)
* [StacksProject 033E](https://stacks.math.columbia.edu/tag/033E)
* [StacksProject 033F](https://stacks.math.columbia.edu/tag/033F)
* [StacksProject 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [StacksProject 058S](https://stacks.math.columbia.edu/tag/058S)
* [StacksProject 05GJ](https://stacks.math.columbia.edu/tag/05GJ)
* [StacksProject 05N5](https://stacks.math.columbia.edu/tag/05N5)
* [StacksProject 05N6](https://stacks.math.columbia.edu/tag/05N6)
* [StacksProject 07RE](https://stacks.math.columbia.edu/tag/07RE)
* [StacksProject 0GVD](https://stacks.math.columbia.edu/tag/0GVD)
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module

/-- Let `R → S` be faithfully flat, let `l : P → M` be a surjection of `R`-modules with `P` finite
over `R`, and assume the base change `S ⊗[R] M` is a finitely presented `S`-module. Then
`ker l` is a finitely generated `R`-module. -/
private theorem fg_ker_of_faithfullyFlat {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation S (S ⊗[R] M)] (l : P →ₗ[R] M) (hl : Function.Surjective l) :
    (LinearMap.ker l).FG := by
  rw [← Module.Finite.iff_fg]
  have : Module.Finite S (S ⊗[R] (LinearMap.ker l)) := by
    rw [Module.Finite.equiv_iff (LinearMap.tensorKerEquiv S S l), Module.Finite.iff_fg]
    exact Module.FinitePresentation.fg_ker _
      ((Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S l).mpr hl)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- **Stacks 03C4** (part 2). Let `R → S` be a faithfully flat ring map, let `M` be an `R`-module
and let `f : M →ₗ[R] N` exhibit the `S`-module `N` as the base change of `M` along `R → S`. If `N`
is a finitely presented `S`-module, then `M` is a finitely presented `R`-module. -/
@[stacks 03C4 "Part (2). Part (1) is `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`
and part (3) is `Module.Flat.of_flat_tensorProduct`, both in Mathlib."]
theorem FinitePresentation.of_isBaseChange_of_faithfullyFlat {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (h : IsBaseChange S f) [Module.FinitePresentation S N] :
    Module.FinitePresentation R M := by
  have : Module.FinitePresentation S (S ⊗[R] M) :=
    (LinearEquiv.finitePresentation_iff h.equiv).mpr ‹_›
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hsurj := (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hs
  exact Module.finitePresentation_of_free_of_surjective _ hsurj
    (fg_ker_of_faithfullyFlat S _ hsurj)

end Module

/- Stacks 00QQ, both directions, are Mathlib's: `Algebra.FinitePresentation.baseChange` is the
ascending direction (which needs no flatness) and
`Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` is the
descending one. Both are stated at the algebra level; the source's ring map `R → S` is
`algebraMap R S`, and `RingHom.finitePresentation_algebraMap` passes between the two spellings.
At the ring-map level the same pair is `RingHom.finitePresentation_isStableUnderBaseChange` and
`RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`. -/

namespace Module

section Localization

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (Rₛ : Type v) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M : Type w} [AddCommGroup M] [Module R M]
  {Mₛ : Type t} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
  (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

variable {F : Type*} [AddCommGroup F] [Module R F]
  {Fₛ : Type*} [AddCommGroup Fₛ] [Module R Fₛ] [Module Rₛ Fₛ] [IsScalarTower R Rₛ Fₛ]

end Localization

section BaseChange

variable {R : Type u} [CommRing R] (S : Submonoid R) (Rₛ : Type v) [CommRing Rₛ]
  [Algebra R Rₛ] [IsLocalization S Rₛ] {R' : Type w} [CommRing R'] [Algebra R R']
  [Algebra Rₛ R'] [IsScalarTower R Rₛ R'] {M : Type*} [AddCommGroup M] [Module R M]

include S Rₛ

variable {F : Type*} [AddCommGroup F] [Module R F]
  {F' : Type*} [AddCommGroup F'] [Module R F'] [Module R' F'] [IsScalarTower R R' F']
  {ι : F →ₗ[R] F'} {M' : Type t} [AddCommGroup M'] [Module R M'] [Module R' M']
  [IsScalarTower R R' M']

end BaseChange

end Module

section AlgebraMaps

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {S' : Type*} [CommRing S']
  [Algebra R S] [Algebra R S']

end AlgebraMaps

end
