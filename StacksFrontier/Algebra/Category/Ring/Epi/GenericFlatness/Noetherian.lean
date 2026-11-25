module


import StacksCore.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.FinitePresentation.FreeAway
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Generic flatness

A finite type algebra over a domain becomes free, and finitely presented, after inverting a single
nonzero element of the domain. This file proves the six lemmas of Stacks section 051Q which make
that precise, in increasing order of strength, together with the two local-global properties of the
locus where it happens.

For a ring map `R → S` and an `S`-module `M`, Equation 051U singles out those `f : R` for which,
after inverting `f`, the algebra `S_f` is of finite presentation over `R_f`, the module `M_f` is of
finite presentation over `S_f`, and both `S_f` and `M_f` are free over `R_f`; that condition is the
predicate `Algebra.IsFinitePresentationFreeAway`. Equation 051V collects the standard opens `D(f)`
of such `f` into the *generic freeness locus*
```
U(R → S, M) = ⋃ {D(f) | Algebra.IsFinitePresentationFreeAway R S M f} ⊆ Spec R.
```

Three lemmas produce elements of that locus, under successively weaker hypotheses on the base: over
a Noetherian domain for a finite module over a finite type algebra (051R), over an arbitrary domain
for a finitely presented module over a finitely presented algebra (051S), and over an arbitrary
domain for a finite module over a finite type algebra, the finite presentation then being part of
the conclusion rather than of the hypotheses (051T). Two more describe the locus itself: it is
stable under extensions of the module (051W), and it is local on the base (051X), whence density of
the locus may be checked on a dense open (051Y).

## Main results

* `Module.exists_ne_zero_free_localizedModule_away`: generic freeness over a Noetherian domain
  (051R).
* `Module.FinitePresentation.exists_ne_zero_free_localizedModule_away`: generic freeness for a
  finitely presented module over a finitely presented algebra over a domain (051S).
* `Algebra.exists_ne_zero_isFinitePresentationFreeAway`: generic freeness together with generic
  finite presentation over a domain, i.e. the locus is nonempty (051T).
* `Algebra.IsFinitePresentationFreeAway.of_dvd`: the condition 051U is inherited by every multiple
  of an element satisfying it, so two good elements can be replaced by the single good element
  `g₁ * g₂`.
* `Algebra.isFinitePresentationFreeAway_of_finitePresentation_of_free`: every element of the base
  satisfies 051U as soon as the algebra and the module are already of finite presentation and free.
* `Algebra.iUnion_basicOpen_isFinitePresentationFreeAway_inter_subset_of_shortExact`: for a short
  exact sequence `0 → M₁ → M₂ → M₃ → 0`, one has
  `U(R → S, M₁) ∩ U(R → S, M₃) ⊆ U(R → S, M₂)` (051W).
* `Algebra.image_comap_iUnion_basicOpen_isFinitePresentationFreeAway`: under the identification
  `Spec(R_f) = D(f)`, one has `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)` (051X).
* `Algebra.dense_iUnion_basicOpen_isFinitePresentationFreeAway_of_localizationAway`: if the `D(f)`,
  `f ∈ s`, have dense union and each `U(R_f → S_f, M_f)` is dense in `Spec(R_f)`, then
  `U(R → S, M)` is dense (051Y).

## Implementation notes

**The route to 051R is not the source's.** The source argues by induction on `dim (K ⊗_R S)`, `K`
the fraction field of `R`, using a prime filtration of `M` over the Noetherian ring `S` and a
factorization `R ⊂ R[y_1, …, y_d] ⊂ S` with the second extension finite. The proof here instead
uses the division algorithm for the degree-lexicographic monomial order, which settles the key case
outright. Writing `S` as a quotient of `A = R[y_1, …, y_d]` and filtering a finite `A`-module by
cyclic submodules reduces the statement to `M = A ⧸ I`; for that case, Dickson's lemma gives
finitely many `p_1, …, p_k ∈ I` whose leading exponents `μ_i` divide the leading exponent of every
nonzero element of `I`, and after inverting the product `f` of their leading coefficients, division
with remainder by the `p_i` exhibits `B[y] ⧸ I B[y]` as free on the monomials `y^ν` with `ν`
divisible by no `μ_i` (Macaulay's basis theorem, `free_quotient_of_degrees` below).

*Consequently `IsNoetherianRing R` is not used in the proof of 051R.* Nothing in the route above
needs it: the staircase of leading exponents of an arbitrary ideal of `A` is finitely generated by
Dickson's lemma rather than by Noetherianity, and the filtration of a module with `n` generators by
cyclic submodules has `n` steps. The hypothesis is kept because it is the source's, and because
051R is the Noetherian member of the family; the private lemmas it is proved from assume only
`IsDomain R`.

**Generic freeness is proved in the base-change model.** The private lemmas leading to 051R
conclude that `B ⊗[R] M` is free over *every* localization `B` of `R` in which a suitable `f`
becomes invertible. That form is what makes the induction work, since two successive choices of `f`
are combined by multiplying them and `B` is then a localization at neither alone;
`IsLocalizedModule.isBaseChange` converts it to the stated conclusion.

**The localizations in 051R, 051S and 051X are abstract.** Those three conclusions are asserted for
every model of the localizations involved — for 051R and 051S, every `R`-algebra `Rf` with
`IsLocalization.Away f Rf` and every `R`-linear `g : M → Mf` with
`IsLocalizedModule (Submonoid.powers f) g`. Any two such models being isomorphic over `R`, this is
equivalent to the single concrete assertion about `Localization.Away f` and
`LocalizedModule.Away f M`, which is the shape of the Mathlib sibling
`Module.FinitePresentation.exists_free_localizedModule_powers`; the quantified form is what a user
localizing along a standard open of `Spec R` applies without transporting along a chosen
construction. In 051T, 051W and 051Y the models are instead the canonical ones fixed by
`Algebra.IsFinitePresentationFreeAway`, and `Algebra.isFinitePresentationFreeAway_iff` moves those
conclusions to any other models; in 051Y taking abstract models would mean three families of types
indexed by `s` together with some fifteen families of instances, none of them mathematics.

**The `R`-module structure on `M`** in 051R and 051S is the one induced by `R → S`, recorded as
`[Module R M]` with `[IsScalarTower R S M]`, since the source's `M_f` is the localization of `M` as
an `R`-module. No finiteness of `M` over `R` is available: `M` is finite over `S` only, and `M_f`
will in general have infinite rank over `R_f` — already for `S = R[x]`, `M = S` — so the conclusion
is `Module.Free` alone. In 051T, 051W, 051X and 051Y no `R`-module structure on `M` occurs at all,
the `R_f`-action on `M_f` being the restriction of its `S_f`-action.

**The locus `U(R → S, M)` is written out** as the union of standard opens it is, since the library
has no definition for the construction 051V. Membership of a prime then unfolds to "some `f` outside
it satisfies 051U", which is how the source's proofs read. Openness of the locus, asserted by the
source alongside Equation 051V, is `isOpen_iUnion`. Mathlib's `Module.freeLocus R M` is the
pointwise analogue for one module over one ring and neither contains nor is contained in this
locus.

**Short exact sequences are given as two maps** with injectivity, surjectivity and
`Function.Exact`, rather than as a `CategoryTheory.ShortComplex.ShortExact` in `ModuleCat S`: the
conclusions are statements about the three types and their localizations, and passing through
`ModuleCat` would force them into a common universe and make every consumer package a submodule and
a quotient into a short complex. For the same reason the extension lemma used is
`free_of_shortExact` below rather than `ModuleCat.free_shortExact`.

## References

* [StacksProject 051Q](https://stacks.math.columbia.edu/tag/051Q)
* [StacksProject 051R](https://stacks.math.columbia.edu/tag/051R)
* [StacksProject 051S](https://stacks.math.columbia.edu/tag/051S)
* [StacksProject 051T](https://stacks.math.columbia.edu/tag/051T)
* [StacksProject 051W](https://stacks.math.columbia.edu/tag/051W)
* [StacksProject 051X](https://stacks.math.columbia.edu/tag/051X)
* [StacksProject 051Y](https://stacks.math.columbia.edu/tag/051Y)

## Tags

generic freeness, generic flatness, finite presentation, free module, localization, dense open
-/

/-!
## This file

The first of the four parts of `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness`, whose
overview of Stacks section 051Q is the module docstring above. This part contains the shared lemmas
on extensions of free modules and flat base change, and generic freeness over a Noetherian domain,
`Module.exists_ne_zero_free_localizedModule_away` (051R). Stacks 051S is in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.FinitePresentation`, 051T in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.GenericFinitePresentation`, and the
generic freeness locus (051W, 051X, 051Y) in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Locus`.
-/

@[expose] public section

universe u v w

/-- **An extension of free modules is free.** If `0 → N₁ → N₂ → N₃ → 0` is a short exact sequence
of `A`-modules with `N₁` and `N₃` free, then `N₂` is free: `N₃` is free, hence projective, so the
sequence splits and `N₂ ≃ N₁ × N₃`. This is `ModuleCat.free_shortExact` for three modules in three
different universes. -/
private theorem free_of_shortExact {A N₁ N₂ N₃ : Type*} [Ring A] [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] {i : N₁ →ₗ[A] N₂}
    {q : N₂ →ₗ[A] N₃} (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : Function.Exact i q) [Module.Free A N₁] [Module.Free A N₃] : Module.Free A N₂ := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.mpr hq)
  exact Module.Free.of_equiv (lequivProdOfRightSplitExact hi (LinearMap.exact_iff.mp hiq).symm hs)

/-- Base change along a flat algebra preserves injectivity. This is
`Module.Flat.lTensor_preserves_injective_linearMap` for `LinearMap.baseChange`. -/
private theorem baseChange_injective {S : Type*} [CommSemiring S] (T : Type*) [Semiring T]
    [Algebra S T] [Module.Flat S T] {M N : Type*} [AddCommMonoid M] [Module S M] [AddCommMonoid N]
    [Module S N] {f : M →ₗ[S] N} (hf : Function.Injective f) :
    Function.Injective (f.baseChange T) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Base change along a flat algebra preserves exactness. This is `Module.Flat.lTensor_exact` for
`LinearMap.baseChange`. -/
private theorem baseChange_exact {S : Type*} [CommRing S] (T : Type*) [Ring T] [Algebra S T]
    [Module.Flat S T] {M N P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P] {f : M →ₗ[S] N} {g : N →ₗ[S] P} (h : Function.Exact f g) :
    Function.Exact (f.baseChange T) (g.baseChange T) := by
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_exact T h

/-! ### Generic freeness over a Noetherian domain (051R) -/

section
open MvPolynomial MonomialOrder TensorProduct

section Localization

attribute [local instance] MvPolynomial.algebraMvPolynomial

end Localization

end

namespace Module

end Module

end
