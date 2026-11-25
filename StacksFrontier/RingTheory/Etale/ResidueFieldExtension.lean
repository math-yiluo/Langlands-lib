module

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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

universe u v

/-!
# Realizing a finite separable residue field extension by an étale algebra

Let `R` be a ring, `p` a prime of `R` and `κ(p)` its residue field, and let `L/κ(p)` be a finite
separable field extension. This file proves Stacks 00UD: there are an étale ring map `R → R'` and
a prime `p'` of `R'` lying over `p` together with an isomorphism `κ(p') ≃+* L` carrying the
canonical map `κ(p) → κ(p')` to `κ(p) → L`.

The witness is the source's. By the primitive element theorem `L = κ(p)⟮α⟯`; let `f̄ = minpoly α`.
Because `κ(p)` is the fraction field of `R ⧸ p`, a single `c` clears the denominators of all the
coefficients of `f̄` at once, and rescaling the root by `c` — that is, passing from `f̄` to
`Polynomial.scaleRoots f̄ c`, whose `i`-th coefficient is `c ^ (n - i)` times that of `f̄` — makes
every coefficient come from `R`. So `f̄.scaleRoots c` lifts to a monic `f ∈ R[X]`, and `β = cα`
is a root of `f` at which `f'` is invertible, since `f̄` is separable and `c` is a unit. The pair
`(f, f')` is a `StandardEtalePair R`, whose standard étale algebra `R' = R[x, 1/f']/(f)` is étale;
`x ↦ β` is an `R`-algebra map `R' → L`, and `p'` is its kernel. Finally `κ(p') → L` is the
extension of the injection `R' ⧸ p' ↪ L` to fraction fields, and it is onto because its image is
a subfield of `L` containing `κ(p)` and `β`, hence contains `κ(p)⟮β⟯ = L`.

## Main results

* `Stacks.Etale.ResidueFieldRealization.solution`: Stacks 00UD.

## Implementation notes

The source says "after replacing `α` by `cα` for some `c ∈ R`, `c ∉ p`, we may assume all the
coefficients of `f̄` are in the image of `R → κ(p)`" and omits the verification. The verification
is `exists_isUnit_and_scaleRoots_mem_lifts` together with
`scaleRoots_aeval_derivative_mul`: the first produces the common denominator from
`IsLocalization.exist_integer_multiples` for the fraction field `κ(p)` of `R ⧸ p`, using that
`c ^ (n - i) * f̄.coeff i = c ^ (n - i - 1) * (c * f̄.coeff i)` for `i < n` while the leading
coefficient is untouched; the second is the identity
`(f̄.scaleRoots c)'(cx) = c ^ (n - 1) * f̄'(x)`, which is what turns separability of `f̄` at `α`
into invertibility of the derivative at `β`. Note that `c` is produced as a unit of `κ(p)`, not as
an element of `R ∖ p`; the two are interchangeable here (`κ(p)` is the fraction field of `R ⧸ p`),
and the unit form is what both uses need.

`scaleRoots_aeval_derivative_mul` is the derivative companion of Mathlib's
`Polynomial.scaleRoots_aeval_smul` and `Polynomial.scaleRoots_eval_mul`, and belongs beside them
in `Mathlib.RingTheory.Polynomial.ScaleRoots`; it is proved here.

## References

* [StacksProject 00UD](https://stacks.math.columbia.edu/tag/00UD), Lemma 10.143.7.
-/

namespace Stacks.Etale.ResidueFieldRealization

open Polynomial

end Stacks.Etale.ResidueFieldRealization

/-!
# Realizing a finite separable residue field extension by an étale algebra

Let `R` be a ring, let `p` be a prime of `R` and write `κ(p)` for its residue field. Every finite
separable field extension `L/κ(p)` is already the residue field extension of an étale `R`-algebra:
there are an étale ring map `R → R'` and a prime `p'` of `R'` lying over `p` together with an
isomorphism `κ(p') ≃ L` of extensions of `κ(p)`, that is, an isomorphism carrying the canonical
map `κ(p) → κ(p')` to the given map `κ(p) → L`.

The source produces `R'` by the theorem of the primitive element: writing `L = κ(p)[α]` with
minimal polynomial `f̄ ∈ κ(p)[x]`, one lifts `f̄` to a monic `f ∈ R[x]` (after rescaling `α` by
some `c ∉ p`, so that the coefficients of `f̄` lie in the image of `R`) and takes
`R' = R[x, 1/f'] / (f)`, a *standard* étale algebra; separability of `L/κ(p)` makes `f̄'(α)`
invertible, so `x ↦ α` defines an `R`-algebra map `R' → L`, and `p'` is its kernel.

## Main results

* `Algebra.exists_etale_liesOver_residueFieldRingEquiv`: Stacks 00UD.

## Implementation notes

*Only étaleness of `R'` is asserted, as in the source's statement.* The source's proof exhibits a
standard étale `R'` (a principal localization of `R[x]/(f)` for a monic `f`), which is strictly
more information, but the statement of the tag records only `Algebra.Etale R R'`, and that is what
its consumers (Lemmas 00UK, 04GJ, 00U2 and More on Morphisms Lemma 04D1) use. The refinement
"étale is locally standard étale" is the content of the neighbouring Proposition 00UE, so
strengthening the conclusion here would duplicate that tag rather than this one.

*The isomorphism of extensions is pinned by an equation, not by a `κ(p)`-algebra structure.* The
source writes "the field extension `κ(p')/κ(p)` is isomorphic to `κ(p) ⊂ L`". Here `κ(p')` is
canonically a `κ(p)`-algebra through `Ideal.ResidueField.map p p' (algebraMap R R')`, the map
induced on residue fields by `R → R'`, and the conclusion says that some ring isomorphism
`e : κ(p') ≃+* L` satisfies `e ∘ (κ(p) → κ(p')) = (κ(p) → L)`. This is exactly `κ(p)`-semilinearity
of `e` for the canonical structures, and it avoids assuming the `Algebra κ(p) κ(p')` instance,
which Mathlib supplies only in the presence of further localization-compatibility instances
(`Localization.AtPrime.IsLiesOverAlgebra`). It is also strictly more informative than asking for an
`R`-algebra isomorphism `κ(p') ≃ₐ[R] L`, which by itself does not name the map from `κ(p)`; the two
happen to be equivalent, because `κ(p)` is a localization of the image of `R`, so any ring map out
of `κ(p')` agreeing with the structure maps on `R` agrees with them on `κ(p)`.

*The prime is exhibited through `Ideal.LiesOver`.* "`p'` lies over `p`" is `p'.LiesOver p`, i.e.
`p = p'.comap (algebraMap R R')`, which is Mathlib's spelling and the one the sibling lemma
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` uses; `p'.over_def p` is the equation
consumed by `Ideal.ResidueField.map`.

*Universes.* `R'` is produced in the universe of `R`, as in the Mathlib sibling: the witness
`R[x, 1/f']/(f)` is built from `R`. The target `L` is left in an arbitrary universe, since a ring
isomorphism may cross universes and no smallness hypothesis on `L` is needed.

Faithfulness to [StacksProject 00UD]:

1. No hypothesis is idle. `Module.Finite κ(p) L` and `Algebra.IsSeparable κ(p) L` are both
   necessary for the conclusion, hence used: for an étale `R → R'` and a prime `p'` over `p`, the
   extension `κ(p')/κ(p)` is automatically finite (étale maps are essentially of finite type and
   quasi-finite) and separable (`Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt`), so dropping
   either hypothesis makes the statement false. `Field L` enters the conclusion through `κ(p')`
   being a field.
2. The scalars and the base are the source's. The extension is over `p.ResidueField = κ(p)` itself,
   not over `R`, `R/p` or a localization of `R`; `R'` is an algebra over `R` itself, and the map
   `κ(p) → κ(p')` is the one induced by `algebraMap R R'`.
3. Nothing that the source names is left merely to exist. The comparison map `κ(p) → κ(p')` is
   pinned as `Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)`, and the isomorphism
   is required to intertwine it with the given `algebraMap κ(p) L`; only `R'`, `p'` and `e`
   themselves, which the source also only asserts to exist, are existentially quantified.
4. The instantiation is not degenerate. For `R = ℤ`, `p = 0`, so `κ(p) = ℚ`, and `L = ℚ[i]`, the
   witness is `R' = ℤ[x, 1/2x]/(x² + 1)` with `p' = 0`: this is étale over `ℤ` and its residue
   field is `ℚ[i] = L`, a proper extension of `κ(p)`. So the statement is not the tautology
   `L = κ(p)`, `R' = R`, `p' = p`, which is all that the case `L = κ(p)` asks for.

## References

* [StacksProject 00UD](https://stacks.math.columbia.edu/tag/00UD)
* [StacksProject 00UB](https://stacks.math.columbia.edu/tag/00UB)
* [StacksProject 00UC](https://stacks.math.columbia.edu/tag/00UC)
* [StacksProject 00UE](https://stacks.math.columbia.edu/tag/00UE)

## Tags

étale ring map, standard étale, residue field, separable extension, prime lying over
-/

@[expose] public section

namespace Algebra

end Algebra

end

/-!
# Étale at a prime: the fibre ideal is maximal and the residue field extension is finite separable

Proof of Stacks 00U4, the statement
`Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField`: for a ring map
`R → S` and a prime `q` of `S` lying over `p` in `R`, étale at `q`, the ideal `p S_q` is the
maximal ideal of `S_q` and `κ(q)` is a finite separable extension of `κ(p)`.

The étale hypothesis enters only through unramifiedness at `q`, so the statement is proved in that
form — `IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField` below, which is
the content of Stacks 00UW — and Stacks 00U4 is its specialisation. Over a local base the
mathematics is Mathlib's: `S_q` formally unramified over `R` restricts along `R → R_p` to a formally
unramified `R_p`-algebra, `R_p → S_q` is a local homomorphism of local rings, and `S_q` is
essentially of finite type over `R_p` because it is so over `R`; for such an algebra
`m_{R_p} S_q = m_{S_q}` and `κ(q)/κ(p)` is finite separable. Transporting the first equality along
`R → R_p` — which is `map_algebraMap_eq_map_maximalIdeal` below, because `m_{R_p}` is generated by
`p` — gives `p S_q = m_{S_q}`.

## Main results

* `Stacks.Etale.SeparableResidueAtPrime.solution`: the statement of Stacks 00U4.

## Implementation notes

The source's route replaces `S` by an `S_g` with `R → S_g` étale and then base changes to
`κ(p)`. Passing instead to the local ring `S_q` reaches the same local statement without choosing
`g`: the hypothesis `Algebra.IsEtaleAt R q` is about `S_q` already, and it is what the
localization step of the source is for. This is also why no finiteness on `S` is needed, only
`Algebra.EssFiniteType R (Localization.AtPrime q)`; that hypothesis is spent once, in
`Algebra.EssFiniteType.of_comp`, to see that `S_q` is essentially of finite type over `R_p`.

Mathlib's `Algebra.isUnramifiedAt_iff_map_eq` is the unramified statement as an equivalence, but
under the hypothesis `Algebra.EssFiniteType R S` — essential finiteness of `S` itself — which the
source's local hypothesis does not supply. Its proof uses that hypothesis only through
`Algebra.EssFiniteType R (Localization.AtPrime q)`, so
`IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField` is one direction of it
with the finiteness weakened accordingly; the local-base lemmas it rests on
(`Algebra.FormallyUnramified.map_maximalIdeal` and the two residue field instances of
`Mathlib/RingTheory/Unramified/LocalRing.lean`) hold as stated.

`map_algebraMap_eq_map_maximalIdeal` is the ideal-theoretic bookkeeping of that comparison and
needs no unramifiedness: for any prime `q` lying over `p`, the ideal of `S_q` generated by the
image of `p` is the one generated by the image of `m_{R_p}`. It is the analogue for the prime
below of `Localization.AtPrime.map_eq_maximalIdeal`, from which it follows by transitivity of
scalars; inside Mathlib's proof of `Algebra.isUnramifiedAt_iff_map_eq` it appears only as an
unnamed goal left by `congr!`.

## References

* [StacksProject 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [StacksProject 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [StacksProject 00UW](https://stacks.math.columbia.edu/tag/00UW)
-/

@[expose] public section

namespace Stacks.Etale.SeparableResidueAtPrime

open IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]

/-- **The ideal of `A` generated by the image of a prime `p` of `R` is the ideal generated by the
image of the maximal ideal of `R_p`,** for any `R`-algebra `A` through which `R → R_p` factors.
The analogue for the prime below of `Localization.AtPrime.map_eq_maximalIdeal`; the case
`A = S_q` for a prime `q` of `S` lying over `p` is the one used here. -/
public lemma map_algebraMap_eq_map_maximalIdeal {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : Type*) [CommRing A] [Algebra R A] [Algebra (Localization.AtPrime p) A]
    [IsScalarTower R (Localization.AtPrime p) A] :
    p.map (algebraMap R A) =
      (maximalIdeal (Localization.AtPrime p)).map (algebraMap (Localization.AtPrime p) A) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end Stacks.Etale.SeparableResidueAtPrime

end

/-!
# Étale at a prime: the residue field extension is finite separable

Let `R → S` be a ring map and let `q` be a prime of `S` lying over a prime `p` of `R`. If `R → S`
is étale at `q`, then the local ring `S_q` is as close to `R_p` as it can be: the ideal `p S_q`
generated by the image of `p` is already the maximal ideal of `S_q` — which is `q S_q` — so the
fibre ring `S_q / p S_q` is the residue field `κ(q)`, and that field is a *finite separable*
extension of `κ(p)`.

Both conclusions are local at `q` and both flow from unramifiedness. Being étale at `q` means
`S_q` is formally étale over `R`, hence formally unramified over `R`, hence formally unramified
over `R_p`; for a formally unramified local algebra over a local ring, essentially of finite type,
the maximal ideal of the base generates the maximal ideal and the residue field extension is
separable (`Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`), and the residue field extension
is finite because such an algebra is free (`Algebra.FormallyUnramified.finite_of_free`). Since
`m_{R_p} = p R_p` (`Localization.AtPrime.map_eq_maximalIdeal`), the first conclusion reads
`p S_q = m_{S_q}` back over `R`.

## Main results

* `Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField`: if `R → S` is
  étale at a prime `q` lying over `p`, and `S_q` is essentially of finite type over `R`, then
  `p S_q` is the maximal ideal of `S_q` and `κ(q)` is a finite separable extension of `κ(p)`.

## Implementation notes

The source's hypothesis is that `R → S` be étale at `q`, that is, that there be a `g ∉ q` with
`R → S_g` étale. Assumed here instead are the two consequences the mathematics uses: `S_q` is
formally étale over `R` (`Algebra.IsEtaleAt`, Mathlib's notion of being étale at a prime) and
`S_q` is essentially of finite type over `R`. This is strictly weaker — no global finiteness on
`S` is imposed, matching the source's hypothesis being local at `q` — and it costs a caller
nothing: `Algebra.EssFiniteType R (Localization.AtPrime q)` is an instance whenever `S` is of
finite type, or merely essentially of finite type, over `R`. The two hypotheses are equivalent to
the source's when `R → S` is of finite presentation, by `Algebra.exists_etale_of_isEtaleAt` and
`Algebra.basicOpen_subset_etaleLocus_iff_etale`.

Item (1) of the source is the chain `p S_q = q S_q = m_{S_q}`; recorded here is the equality with
`m_{S_q}`, because `q S_q = m_{S_q}` holds for every prime and is
`Localization.AtPrime.map_eq_maximalIdeal`. The two forms are therefore equivalent, and the one
chosen is the one that composes.

The proof uses only that `R → S` is *unramified* at `q`, which is the strictly weaker hypothesis
of the source's Lemma 00UW — a separate tag, whose statement is otherwise word for word this one,
and whose Mathlib form is `Algebra.isUnramifiedAt_iff_map_eq` (under the stronger finiteness
hypothesis `Algebra.EssFiniteType R S`). The étale hypothesis is kept here because it is what
this tag claims; nothing is lost, since `Algebra.FormallyUnramified` is an instance consequence of
`Algebra.FormallyEtale`, so a caller holding `Algebra.IsEtaleAt R q` may use either lemma.

Residue fields are Mathlib's `Ideal.ResidueField`, the residue field of `Localization.AtPrime`;
"finite separable" is `Module.Finite` together with `Algebra.IsSeparable`. The instances
`[Algebra (Localization.AtPrime p) (Localization.AtPrime q)]` and
`[IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]` are Mathlib's way of naming
the canonical local homomorphism `R_p → S_q` induced by `q.LiesOver p`; they are what give
`κ(p) → κ(q)`, and `Localization.AtPrime.algebraOfLiesOver` supplies them.

Faithfulness. (1) Every hypothesis is used: `q.LiesOver p` is what makes `p` the prime under `q`,
`Algebra.IsEtaleAt R q` gives formal unramifiedness of `S_q`, and essential finiteness of `S_q` is
needed for both conclusions — over a field `k` of positive characteristic the separable closure
`k ⊂ k^{sep}` is formally étale with `p S_q = 0 = m_{S_q}` and `κ(q)/κ(p) = k^{sep}/k` separable
but infinite. (2) The scalars and base are the source's: `p S_q` is the ideal generated in `S_q`
by the image of `p` under `R → S_q`, not by the image of `m_{R_p}`, and the residue field
extension is `κ(q)` over `κ(p)`, not over `S/q` or `R/p`. (3) The source's canonical maps are
pinned, not merely asserted to exist: `p S_q` is `Ideal.map (algebraMap R (Localization.AtPrime q))
p`, and `κ(p) → κ(q)` is the algebra map coming from this scalar tower.
(4) The instantiation is not degenerate: for `R = ℤ`, `S = ℤ[i]` and `p = q = (3)` — the prime `3`
is inert in `ℤ[i]` and unramified — the hypotheses hold, `p S_q = q S_q = m_{S_q}` is a nonzero
maximal ideal, and `κ(q)/κ(p)` is `𝔽_9/𝔽_3`, separable of degree `2`.

## References

* [StacksProject 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [StacksProject 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [StacksProject 00UW](https://stacks.math.columbia.edu/tag/00UW)
-/

@[expose] public section

end

/-!
# Unramified at a prime: the fibre ideal is maximal, the residue field extension finite separable

Stacks 00UW, with the source's hypothesis: `R → S` is *unramified at `q`* in the sense of Stacks
Definition 00UT(3), that is, some `g ∈ S`, `g ∉ q`, has `R → S_g` unramified
(`Algebra.Unramified R (Localization.Away g)`: of finite type with `Ω_{S_g/R} = 0`). No finiteness
is asked of `S` itself.

## Main results

* `Algebra.map_eq_maximalIdeal_and_finite_isSeparable_of_unramified_away`: the statement of
  Stacks 00UW.

## Implementation notes

The hypothesis is turned into the two facts the local argument above uses. First, `S_q` is
formally unramified over `R` (`Algebra.IsUnramifiedAt R q`): `q` lies in the basic open `D(g)`,
which is contained in the unramified locus because `S_g` is formally unramified
(`Algebra.basicOpen_subset_unramifiedLocus_iff`). Second, `S_q` is essentially of finite type
over `R`: it is a localization of `S_g` (`IsLocalization.isLocalization_of_submonoid_le`, since
`g ∉ q`), and `S_g` is of finite type over `R`. Mathlib's `Algebra.IsUnramifiedAt R q` is thus
implied by the source's notion; conversely, for `S` of finite type over `R`, it gives back a
`g ∉ q` with `R → S_g` unramified (`Algebra.exists_unramified_of_isUnramifiedAt`).

Item (1) is recorded as both of its equalities, `p S_q = q S_q` and `q S_q = m_{S_q}`, with
`p S_q` the ideal generated by the image of `p` under the canonical map `R → S_q` and `q S_q` the
one generated by the image of `q` under `S → S_q`.
-/

@[expose] public section

end
