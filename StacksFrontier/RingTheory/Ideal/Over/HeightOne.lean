module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.KrullAkizuki.IntermediateRingNoetherian
import StacksFrontier.RingTheory.Artinian.Basic
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# Generically finite maps are quasi-finite in codimension one

Let `A ⊆ B` be an extension of domains with `A` Noetherian, let `B` be of finite type over `A`,
and assume `B` is algebraic over `A`; for `B` of finite type over `A` the latter is exactly the
condition that the induced extension of fraction fields `Frac(A) ⊆ Frac(B)` be finite, i.e. that
`A → B` be *generically finite*. This file states Stacks 02MA: over a prime `p` of `A` of height
one there are at most finitely many primes of `B`, and every one of them has height one.

Geometrically: a dominant generically finite morphism of finite type between integral schemes,
with Noetherian target, is quasi-finite in codimension one, and codimension one is preserved. The
two failure modes it excludes are both codimension two phenomena on the target: over the height
two prime `(x, y)` the blowup chart `k[x, y] ⊆ k[x, y/x]` has a whole affine line, one chart of
the exceptional `ℙ¹`; and a fibre of positive dimension, such as the one of `k[x] ⊆ k[x, y]` over
`(x)`, occurs only when the extension is not generically finite.

The conclusion is a bound above only: the fibre over `p` may well be empty, as it is for
`ℤ ⊆ ℤ[1/2]` over `p = (2)`, since `B` is not assumed integral over `A`.

## Main results

* `Ideal.primesOver_finite_and_forall_height_eq_one`: for `A ⊆ B` an extension of domains with `A`
  Noetherian, `B` algebraic and of finite type over `A`, and `p` a prime of `A` of height one, the
  set of primes of `B` lying over `p` is finite and each of its members has height one.

## Implementation notes

Hypothesis (2) of the source, that the induced extension of fraction fields be finite, is stated
as `Algebra.IsAlgebraic A B`. The two agree under hypotheses (1) and (4): writing
`K = Frac(A) ⊆ L = Frac(B)`, an element of `B` algebraic over `A` is algebraic over `K`, so if
`B = A[b₁, …, b_n]` is algebraic over `A` then `L = K(b₁, …, b_n)` is finite over `K`; conversely
`L/K` finite makes every element of `B ⊆ L` algebraic over `K`, hence over `A` after clearing
denominators. `IsFractionRing.isAlgebraic_iff'` and `IsFractionRing.isAlgebraic_iff` are the
transfers, and `trdeg_eq_zero_iff` turns this hypothesis into the vanishing of `Algebra.trdeg A B`
that the dimension formula, Stacks 02IJ, consumes in the proof. The gain over the literal form is
that no fraction fields, and hence no auxiliary types and scalar towers, appear in the signature;
the price is that the equivalence above is a step of the proof rather than of the statement.

The inclusion `A ⊆ B` is `FaithfulSMul A B`, injectivity of `algebraMap A B`
(`FaithfulSMul.algebraMap_injective`), which is Mathlib's spelling of a ring extension.
`IsDomain A` is not assumed: it follows from `IsDomain B` by
`Function.Injective.isDomain (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)`, so
hypothesis (1) is carried in full by `IsDomain B` together with `FaithfulSMul A B`.

The primes of `B` lying over `p` are `Ideal.primesOver p B`, whose membership unfolds to
`q.IsPrime` together with `Ideal.LiesOver q p`, i.e. `p = q.comap (algebraMap A B)`: the source's
`p = q ∩ A` for the given map `A → B`. Heights are `Ideal.height`, valued in `ℕ∞`; on a prime `q`
it is the supremum of the lengths of strictly descending chains of primes of `B` ending at `q`,
`PrimeSpectrum.height_eq_orderHeight` reading `q.height = Order.height (⟨q, _⟩ : PrimeSpectrum B)`,
so the conclusion `q.height = 1` says `dim B_q = 1`. No finiteness of any height is assumed, and
the hypothesis `p.height = 1` is an equality in `ℕ∞`.

Only the source's two assertions are stated. The proof passes through the stronger local fact that
`κ(p) ⊆ κ(q)` is finite for `q` over `p`, that is, that `A → B` is quasi-finite at each such `q`
(`Algebra.QuasiFiniteAt`); that refinement belongs to a lemma of its own, not to this tag.

Faithfulness. (1) No hypothesis is dead. `p.height = 1` is live: for `A = k[x, y] ⊆ B = k[x, y/x]`
and `p = (x, y)` of height two, every `(x, f(y/x))` with `f` irreducible lies over `p`, so the
fibre is infinite. `Algebra.IsAlgebraic A B` is live: for `A = k[x] ⊆ B = k[x, y]` and `p = (x)`
of height one the primes `(x, f(y))` lie over `p`, and they are infinite in number and of height
two. `FaithfulSMul A B` is live: for `A = ℤ`, `B = 𝔽₅` and `p = (5)` the only prime over `p` is
`(0)`, of height zero. `IsDomain B` is live: for `A = ℤ ⊆ B = ℤ × 𝔽₅` and `p = (5)` the prime
`ℤ × 0` lies over `p` and is a minimal prime of `B`, so of height zero. `Algebra.FiniteType A B`
is live: for `A = ℤ` and `B` the ring of all algebraic integers, `B` is an algebraic domain
extension of `ℤ` in which `(5)` has infinitely many primes above it, one over each prime above `5`
in each layer of a tower of number fields in which that number grows without bound.
`IsNoetherianRing A` enters twice, through the dimension formula Stacks 02IJ and through the
Noetherianity of the fibre `B ⊗_A κ(p)`, whose spectrum is finite because it is a Noetherian space
all of whose points are closed; no claim is made that it cannot be removed. (2) The scalars and
the base are the source's: `p` is an ideal of `A`, the primes and their heights are computed in
`B`, and the algebra structure is the given `A → B`; no localisation, base change or fraction
field occurs in the statement. (3) The map is pinned rather than merely assumed to exist: lying
over is `comap` along `algebraMap A B`, and the conclusion pins the value `1` of each height, not
merely finiteness of it. (4) The instantiation is not degenerate: for `A = ℤ ⊆ B = ℤ[i]` and
`p = (5) = (2 + i)(2 - i)` there are exactly two primes over `p`, both of height one.

## References

* [StackProject 02MA](https://stacks.math.columbia.edu/tag/02MA)

## Tags

height one prime, generically finite, quasi-finite, lying over
-/

section

namespace Stacks.PrimesOver.CodimensionOneFibre

end Stacks.PrimesOver.CodimensionOneFibre

@[expose] public section

end

end

/-!
# Primes over a maximal ideal of a one-dimensional Noetherian domain

Proof of Stacks 031F. Let `R` be a Noetherian domain of Krull dimension at most one with
fraction field `K`, let `L/K` be a finite extension, and let `S` be a domain with fraction
field `L` which is an `R`-algebra compatibly with `K ⊆ L`. For a maximal ideal `m` of `R` the
fibre ring `S/mS` is a finite-dimensional `κ(m)`-vector space; consequently every prime of `S`
lying over `m` is maximal, there are finitely many of them, and each residue field extension
`κ(n)/κ(m)` is finite.

The mechanism is the finite length of `S/xS` for a nonzero `x ∈ m`: as an `R`-module `S` is a
submodule of the finite-dimensional `K`-vector space `L`, so the length bound of Stacks 00PE
applies; `S/mS` is a quotient of `S/xS`, hence a finite `R`-module, hence a finite module over
the field `κ(m)`. A finite-dimensional algebra over a field is Artinian (Stacks 00J6), and an
Artinian domain is a field, which turns the finiteness of `κ(n)/κ(m)` into the maximality of `n`;
the finiteness of the fibre is the finiteness of `Spec` of an Artinian ring.

## Main results

* `Stacks.PrimesOver.KrullAkizuki.solution`: the statement of Stacks 031F.

## Implementation notes

The whole content is the fibre lemma `module_finite_quotient_map`: if `m` is a maximal ideal of
`R` and the `R`-algebra `S` embeds `R`-linearly in a finite-dimensional `K`-vector space `V`, then
`S/mS` is a finite `R`-module. It is stated for an arbitrary `V` and an arbitrary injective
`R`-linear `S → V` rather than for `S ⊆ L`, since neither the multiplication on `V` nor the fact
that the embedding is a ring map plays any role; `solution` instantiates `V := L` and the
embedding by `IsScalarTower.toAlgHom R S L`, which is injective because `IsFractionRing S L`.
This is the source's "apply 00PE to `S ⊆ L ≅ K^{⊕n}`", with no choice of a `K`-basis of `L`
and no localization of `R` intervening: the length bound is already over `R`, and it needs only
`Ring.KrullDimLE 1 R` rather than `dim R = 1`.

That lemma splits into the two cases the weakened dimension hypothesis creates. For `m ≠ ⊥` it is
`module_finite_quotient_span_singleton`, the application of the length bound in the uniform form
`length_quotient_smul_le_finrank_mul` (Stacks 00PE/00PF, in
`StacksFrontier.RingTheory.KrullAkizuki`),
which bounds `length_R (M/xM) ≤ finrank K V · length_R (R/xR)` for an `R`-submodule `M` of `V`;
finite length gives Noetherian, hence finite. For `m = ⊥` the ring `R` is a field, there is no
nonzero `x ∈ m` to run the length argument with, and `S` itself is finite over `R` because
`R → K` is then onto: this is `module_finite_of_isField`. Both cases end in the same step, a
further quotient of a finite quotient — `module_finite_quotient_of_le`, which is also what
produces the finiteness of `κ(n) = S/n` over `R` from that of `S/mS`.

The source passes from `length_R (S/mS) < ∞` to `dim_{κ(m)} S/mS < ∞` by Stacks 00IY. Here the
finiteness is produced as `Module.Finite R (S/mS)` in the first place, and the descent of the base
along `R → κ(m)` is `Module.Finite.of_restrictScalars_finite`, which is the direction of 00IY(2)
that the argument uses. The structural input on Artinian rings that the source takes from
Stacks 00JB is used twice, in Mathlib's form: `IsArtinianRing.isField_of_isDomain` at `S/n`, which
makes the maximality of `n` a consequence of the finiteness of `κ(n)/κ(m)` rather than a separate
argument, and the instance `Finite (PrimeSpectrum _)` at `S/mS`. So this statement is proved without
depending on 00JB's statement.

## References

* [StacksProject 031F](https://stacks.math.columbia.edu/tag/031F)
-/

namespace Stacks.PrimesOver.KrullAkizuki

open Pointwise

/-- A further quotient of a quotient that is finite over the base is finite over the base. -/
private lemma module_finite_quotient_of_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} (h : I ≤ J) [Module.Finite R (S ⧸ I)] : Module.Finite R (S ⧸ J) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ R h).toLinearMap
    (Ideal.Quotient.factor_surjective h)

/-- If `R` is a field with fraction field `K`, then an `R`-module which embeds `R`-linearly in a
finite-dimensional `K`-vector space is a finite `R`-module.

This is the degenerate case `m = ⊥` of Stacks 031F: a Noetherian domain of Krull dimension at
most one may be a field, and then the length argument has no nonzero `x ∈ m` to run with. -/
private lemma module_finite_of_isField (R K V N : Type*) [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup N] [Module R N] (hR : IsField R)
    (f : N →ₗ[R] V) (hf : Function.Injective f) : Module.Finite R N := by
  let _ : Field R := hR.toField
  -- `R → K` is onto, since every nonzero element of `R` is already invertible.
  have : Module.Finite R K := Module.Finite.of_surjective (Algebra.linearMap R K)
    (IsField.localization_map_bijective zero_notMem_nonZeroDivisors hR).surjective
  have : Module.Finite R V := Module.Finite.trans K V
  exact Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm

/-- **Stacks 00PE, applied to an embedding of `S` in a finite-dimensional `K`-vector space.** If
`R` is a Noetherian domain of Krull dimension at most one with fraction field `K`, and the
`R`-algebra `S` embeds `R`-linearly in a finite-dimensional `K`-vector space `V`, then `S/xS` is
a finite `R`-module for every nonzero `x : R`. -/
private lemma module_finite_quotient_span_singleton (R S K V : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (f : S →ₗ[R] V) (hf : Function.Injective f) {x : R} (hx : x ≠ 0) :
    Module.Finite R (S ⧸ Ideal.span {algebraMap R S x}) := by
  -- The length bound `length_R (M/xM) ≤ finrank K V · length_R (R/xR)` for `M = range f`, whose
  -- right-hand side is finite because `x` is a nonzerodivisor.
  have hlen : IsFiniteLength R (QuotSMulTop x (LinearMap.range f)) := by
    rw [← Module.length_ne_top_iff]
    refine ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top _) ?_)
      (length_quotient_smul_le_finrank_mul R K (LinearMap.range f) hx)
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx))
  have : IsNoetherian R (QuotSMulTop x S) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      ((QuotSMulTop.congr x (LinearEquiv.ofInjective f hf).symm).isFiniteLength hlen)).1
  have : Module.Finite R (QuotSMulTop x S) := ⟨IsNoetherian.noetherian ⊤⟩
  -- As an `R`-submodule of `S`, the ideal `xS` is `x • ⊤`.
  have hxS : (x • ⊤ : Submodule R S)
      = Submodule.restrictScalars R (Ideal.span {algebraMap R S x}) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Ideal.map_span,
      Set.image_singleton]
  exact Module.Finite.equiv ((Submodule.quotEquivOfEq _ _ hxS).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R S x})))

/-- **The fibre of Stacks 031F.** If `R` is a Noetherian domain of Krull dimension at most one
with fraction field `K`, the `R`-algebra `S` embeds `R`-linearly in a finite-dimensional
`K`-vector space `V`, and `m` is a maximal ideal of `R`, then the fibre ring `S/mS` is a finite
`R`-module.

For `m ≠ ⊥` this is the length bound applied to a nonzero `x ∈ m`, since `S/mS` is a quotient of
`S/xS`; for `m = ⊥` the ring `R` is a field and already `S` is finite over `R`. -/
private lemma module_finite_quotient_map (R S K V : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (f : S →ₗ[R] V) (hf : Function.Injective f) (m : Ideal R) [m.IsMaximal] :
    Module.Finite R (S ⧸ m.map (algebraMap R S)) := by
  rcases eq_or_ne m ⊥ with rfl | hm
  · have := module_finite_of_isField R K V S (Ring.isField_iff_maximal_bot.mpr ‹_›) f hf
    exact Module.Finite.quotient R _
  · obtain ⟨x, hxm, hx⟩ := (Submodule.ne_bot_iff m).mp hm
    have := module_finite_quotient_span_singleton R S K V f hf hx
    exact module_finite_quotient_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hxm))

/-- If the fibre ring `S/J` has finitely many primes and every prime of `S` lying over `m`
contains `J`, then only finitely many primes of `S` lie over `m`: such a prime is the contraction
of its image in `S/J`. -/
private lemma finite_primesOver_of_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) (J : Ideal S) [Finite (PrimeSpectrum (S ⧸ J))]
    (hJ : ∀ n ∈ m.primesOver S, J ≤ n) : (m.primesOver S).Finite := by
  refine Set.Finite.subset (Set.finite_range fun p : PrimeSpectrum (S ⧸ J) =>
    p.asIdeal.comap (Ideal.Quotient.mk J)) fun n hn => ?_
  have := hn.1
  exact ⟨⟨n.map (Ideal.Quotient.mk J), Ideal.isPrime_map_quotientMk_of_isPrime (hJ n hn)⟩,
    Ideal.comap_map_mk (hJ n hn)⟩

/-- For a maximal ideal `m` of a Noetherian domain `R` of dimension at most one, every prime of `S`
over `m` is maximal, only finitely many primes of `S` lie over `m`, each quotient `S/n` by such a
prime is finite over `R/m`, and so is `S/mS`. -/
public theorem solution
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] (m : Ideal R) [m.IsMaximal] :
    (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], n.IsMaximal) ∧
      (m.primesOver S).Finite ∧
      (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n)) ∧
      Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) := by
  -- Every prime of `S` lying over `m` contains `mS`.
  have hle : ∀ n : Ideal S, n.LiesOver m → m.map (algebraMap R S) ≤ n := fun n hn =>
    Ideal.map_le_iff_le_comap.mpr hn.over.le
  have hfibre : Module.Finite R (S ⧸ m.map (algebraMap R S)) :=
    module_finite_quotient_map R S K L (IsScalarTower.toAlgHom R S L).toLinearMap
      (IsFractionRing.injective S L) m
  -- `S/mS` and each `S/n` are finite-dimensional `κ(m)`-algebras, hence Artinian rings.
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  have hres : ∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n) := by
    intro n _ hn
    have := module_finite_quotient_of_le (R := R) (hle n hn)
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ m) (S ⧸ n)
  have hfin : Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ m) _
  have : IsArtinianRing (S ⧸ m.map (algebraMap R S)) :=
    finite_dimensional_algebra_is_artinian (R ⧸ m) _
  refine ⟨fun n _ _ => ?_, finite_primesOver_of_le m _ fun n hn => hle n hn.2, hres, hfin⟩
  -- `S/n` is an Artinian domain, hence a field.
  have := hres n
  have : IsArtinianRing (S ⧸ n) := finite_dimensional_algebra_is_artinian (R ⧸ m) _
  exact Ideal.Quotient.maximal_of_isField n (IsArtinianRing.isField_of_isDomain _)

end Stacks.PrimesOver.KrullAkizuki

/-!
# Primes over a maximal ideal of a one-dimensional Noetherian domain

Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let `L/K`
be a finite field extension, and let `S` be a domain sitting in between, that is, an `R`-algebra
which is a domain with fraction field `L`. Then for every maximal ideal `m` of `R` the fibre ring
`S/mS` is a finite-dimensional `κ(m) = R/m`-vector space. Consequently every prime `n` of `S`
lying over `m` is maximal, there are only finitely many such primes, and each residue field
extension `κ(n)/κ(m)` is finite.

The mechanism is the finite length of `S/xS`: choosing a nonzero `x ∈ m`, the ring `S` is an
`R`-submodule of `L ≅ K^{[L : K]}`, so `S/xS` has finite length over `R`, hence so does its
quotient `S/mS`; the latter is killed by `m`, so its length over `R` is its dimension over the
field `κ(m)`. A finite-dimensional algebra over a field is Artinian, which gives the maximality
of the primes over `m` and their finiteness, and the finiteness of `κ(n)/κ(m)` is the
finite-dimensionality itself, `κ(n) = S/n` being a quotient of `S/mS`.

Note that `S` is not assumed to be of finite type over `R`: that is the point of this lemma and
of the Krull–Akizuki circle of results it belongs to, where `S` is typically the integral closure
of `R` in `L` and can fail to be a finite `R`-module.

## Main results

* `Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient`: the primes of `S` over a
  maximal ideal `m` of `R` are maximal and finite in number, their residue field extensions over
  `κ(m)` are finite, and `S/mS` is a finite-dimensional `κ(m)`-vector space.

## Implementation notes

The source assumes `R` Noetherian local of dimension one and speaks of *the* maximal ideal
`m`; here `m` is an arbitrary maximal ideal of a Noetherian domain with `Ring.KrullDimLE 1 R`.
The local case is the instantiation `m := IsLocalRing.maximalIdeal R`, and conversely the general
statement follows from the local one by localizing at `m`: neither the set of primes of `S` over
`m` nor the residue fields involved change under `R → R_m`, `S → S ⊗[R] R_m` (a domain with the
same fraction field `L`). The generality is not decoration: the dependents 09IG, 09E5 and 09II
apply this lemma at every maximal ideal of a ring that is not local.

The source's `dim(R) = 1` is weakened to `Ring.KrullDimLE 1 R`, Mathlib's spelling of `dim R ≤ 1`,
which for a domain is equivalent to `Ring.DimensionLEOne R` (every nonzero prime is maximal), the
form carried by `IsDedekindRing` and used in the statement of 09IG. Dimension exactly one is used
by no conclusion: the degenerate case this admits is `R` a field, where `m = ⊥`, `K = R`, `S` is a
domain finite-dimensional over `K` hence a field, and all four conclusions are immediate. The
hypotheses are, on the other hand, sharp in the dimension: for `R = k[x, y]_{(x, y)}`, which has
dimension two, and `S = R[y/x] ⊆ L = K`, one has `mS = xS` with `S/xS ≅ k[y/x]`, so that `xS` is a
non-maximal prime lying over `m` and infinitely many primes lie over `m`.

`K` and `L` are abstract fraction fields (`IsFractionRing`) rather than the constructions
`FractionRing R` and `FractionRing S`. The source's inclusions `R ⊆ S` and `K ⊆ L` are not
assumed: `FaithfulSMul R S` follows from the two scalar towers, since `algebraMap R L` factors as
the injective composite `R → K → L`; and `[Algebra K L]` with `[IsScalarTower R K L]` pins the
`R`-algebra map `K → L` uniquely (by the universal property of the localization `K`), so no
choice of an embedding is left open. It is injective because `K` is a field.

The residue fields are written as the quotients `R ⧸ m` and `S ⧸ n`, which is legitimate for
`S ⧸ n` precisely because of the first conclusion, `n` being maximal; the `Ideal.ResidueField`
form `Module.Finite m.ResidueField n.ResidueField` used by Mathlib's quasi-finiteness API follows
through `Ideal.bijective_algebraMap_quotient_residueField`. The `(R ⧸ m)`-algebra structure on
`S ⧸ n` is the canonical `Ideal.Quotient.algebraOfLiesOver`, and `Ideal.primesOver m S` is
`{n | n.IsPrime ∧ n.LiesOver m}`, so that the second conclusion is the finiteness of the fibre of
`Spec(S) → Spec(R)` over `m`.

The last conjunct, `Module.Finite (R ⧸ m) (S ⧸ mS)`, is what the author's proof establishes
before deducing the three assertions of the tag, and it is strictly stronger than their
conjunction (finitely many primes, all maximal, with finite residue field extensions do not bound
the nilpotents of `S/mS`). It is recorded because a dependent that packages fibres as
`Algebra.QuasiFinite R S` — Mathlib's form of tag 00PL, used in the statement of 09IG — needs
exactly the finite-dimensionality of `κ(m) ⊗[R] S` at the maximal ideals, and because from it the
second conclusion is also available as `Algebra.QuasiFinite.finite_primesOver`.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` and `Ring.KrullDimLE 1 R` are what
make `S/xS` of finite length over `R` for `0 ≠ x ∈ m`, `FiniteDimensional K L` is what makes `S`
a submodule of a finite-dimensional `K`-space, `IsFractionRing R K` and `IsFractionRing S L` fix
`K` and `L` as the fraction fields of `R` and `S`, `IsDomain R` and `IsDomain S` are the source's
hypothesis that both rings are domains, and `m.IsMaximal` is needed for `S/mS` to be an algebra
over a field (over a non-maximal prime the fibre can be infinite-dimensional). (2) The scalars
and the base are the source's: the finiteness assertions are over `κ(m) = R ⧸ m` and the primes
are ideals of `S` itself, not of a localization, and no conclusion is phrased over `K` or `L`.
(3) The maps the source names are pinned rather than merely assumed to exist: `K → L` by
`IsScalarTower R K L`, the inclusion of `S` in `L` by `IsFractionRing S L` together with
`IsScalarTower R S L`, and `κ(m) → κ(n)` by `Ideal.Quotient.algebraOfLiesOver`. (4) The
instantiation is not degenerate: `R = ℤ`, `K = ℚ`, `L = ℚ(i)`, `S = ℤ[i]` and `m = (5)` gives two
primes `(2 ± i)` over `m`, each maximal with residue field `𝔽₅`, and `S/mS ≅ 𝔽₅ × 𝔽₅` of
dimension `2 = [L : K]`; `S = ℤ[1/2]` with `m = (2)` gives an empty fibre and `S/mS = 0`, which is
why the second conclusion is a `Set.Finite` and not a cardinality bound.

## References

* [StacksProject 031F](https://stacks.math.columbia.edu/tag/031F)

## Tags

Krull-Akizuki, residue field extension, quasi-finite, dimension one, Noetherian domain
-/

namespace Ideal

/-- Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let
`L/K` be a finite field extension, and let `S` be a domain with fraction field `L` which is an
`R`-algebra compatibly with `K ⊆ L`. Then, for every maximal ideal `m` of `R`, every prime `n` of
`S` lying over `m` is maximal, only finitely many primes of `S` lie over `m`, each residue field
extension `κ(n)/κ(m)` is finite, and moreover `S/mS` is a finite-dimensional `κ(m)`-vector
space. -/
@[stacks 031F "The three assertions of the tag, for an arbitrary maximal ideal `m` of a Noetherian
domain with `Ring.KrullDimLE 1` rather than for the maximal ideal of a local ring of dimension
one, together with the finite-dimensionality of `S/mS` over `κ(m)` from which the author's proof
deduces them. See the module docstring."]
public theorem isMaximal_and_finite_primesOver_and_module_finite_quotient
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] (m : Ideal R) [m.IsMaximal] :
    (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], n.IsMaximal) ∧
      (m.primesOver S).Finite ∧
      (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n)) ∧
      Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) :=
  Stacks.PrimesOver.KrullAkizuki.solution R S K L m

end Ideal

/-!
# Residue field extensions of a local homomorphism in codimension one

Let `A` be a Noetherian local ring of Krull dimension at most one and let `B` be a local
`A`-algebra, the structure map being a local homomorphism. If `q` is a prime of `B` lying over a
prime `p` of `A` for which the residue field extension `κ(p) ⊆ κ(q)` is finite, then the residue
field extension `κ(A) ⊆ κ(B)` of the closed points is finite as well.

This is the local form of the finiteness half of Krull–Akizuki, and the step which upgrades
generic finiteness to quasi-finiteness over a point of codimension one: geometrically, `p` is the
image of a generic point of `Spec(B)`, and the conclusion says that the closed point of `Spec(B)`
is closed in its fibre over the closed point of `Spec(A)`.

## Main results

* `IsLocalRing.finite_residueField_of_isFractionRing_quotient`: the statement with the two
  residue fields `κ(p)` and `κ(q)` given as abstract fraction fields of `A ⧸ p` and `B ⧸ q`.
* `IsLocalRing.finite_residueField_of_finite_residueField_liesOver`: the same with the two
  residue fields taken to be `Ideal.ResidueField`.
* `IsLocalRing.finite_residueField_of_quasiFiniteAt`: the form in which the hypothesis at `p`
  and `q` is quasi-finiteness of `B` over `A` at `q`.

## Implementation notes

The whole content is `Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient`
(Stacks 031F) applied to the pair of domains `A ⧸ p ⊆ B ⧸ q`: the first is Noetherian of Krull
dimension at most one because `A` is, and `κ(p)` and `κ(q)` are precisely their fraction fields.
The maximal ideal `m` of `A ⧸ p` is the image of the maximal ideal of `A`, the prime of `B ⧸ q`
lying over it is the image of the maximal ideal of `B` — which does lie over it because the
structure map is a local homomorphism — and the two iterated quotients `(A ⧸ p) ⧸ m` and
`(B ⧸ q) ⧸ n` are the residue fields of `A` and of `B` by `DoubleQuot.quotQuotEquivQuotOfLE`.

No lower bound on the dimension of `A` is needed, and `p` is not required to differ from the
maximal ideal of `A`. In that degenerate case the statement is the degenerate case of 031F in
which the base is a field: `B ⧸ q` is then a domain which is finite-dimensional over `κ(A)`,
hence a field, so `q` is the maximal ideal of `B`.

## References

* [Stacks Project, Tag 00PG](https://stacks.math.columbia.edu/tag/00PG)
* [Stacks Project, Tag 031F](https://stacks.math.columbia.edu/tag/031F)
-/

namespace IsLocalRing

end IsLocalRing
