# Corrected module localization in Renard A.III.1, example 4

Authors: Worker 618; Worker 6 supplied the source diagnosis and counterexample in
`notes/renard/appendix-a-corrections.md`. Worker 618 read the original passage,
checked the rendered wording, and implemented the Lean interface and proofs.

## Original and correction

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, example 4,
printed page 252 / PDF page 258. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The right universal problem is defined on printed page 251 / PDF page 257;
the comparison of two solutions is discussed at the top of printed page 252 /
PDF page 258. These are the exact source locations for this interface.

The main condition of example 4 says that every denominator acts invertibly on
the module. Its parenthesis replaces this with a pointwise scalar-inverse
condition: for each denominator s and vector n there is a coefficient t such
that both (ts)n and (st)n equal n. This is stronger and is not equivalent to
invertibility of the module endomorphism. The Lean definition follows the main
condition. The rational counterexample below is an internal source diagnosis,
not a result asserted by Renard. The supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 18–19 were checked; that portion does not correct this parenthesis.
This is a limited reading of the 2010 errata, not an exhaustive errata claim.

## Hypotheses and universes

Every name below is in the namespace `Langlands.Renard.ModuleLocalization`.
The general interface assumes exactly a commutative unital ring
`R : Type u`, a submonoid `S : Submonoid R`, a unital source module
`M : Type v` with `[AddCommGroup M] [Module R M]`, and, when used, a unital
target `N : Type w` with `[AddCommGroup N] [Module R N]`. The comparison
also allows `L : Type x` with `[AddCommGroup L] [Module R L]`.
All four universes are independent.

The actual Mathlib type `LocalizedModule S M` is in `Type (max u v)`.
The target universe w has no relation to u or v. In particular, no `Small`
instance or universe shrinking is assumed. There are no domain, faithful-action,
finite-generation, finite-dimensionality, nontriviality or nonzero-denominator
hypotheses. The ring may be the zero ring and S may contain zero.

## Source-to-Lean interface

`IsSLocal S N : Prop` means

```lean
∀ s : S, IsUnit (algebraMap R (Module.End R N) (s : R))
```

Here `algebraMap R (Module.End R N) r` is the actual R-linear scalar
endomorphism `n ↦ r • n`. This corresponds to the object condition defining
the source's full subcategory of local modules, with the false parenthesis
removed. `isSLocal_iff_bijective S N` identifies this predicate with
`∀ s : S, Function.Bijective (fun n : N => (s : R) • n)`.
The proof applies the checked Mathlib `Module.End.isUnit_iff` in both
directions. That lemma requires only a semiring R, an additive commutative
monoid N and a unital R-module N; the present interface uses rings and additive
groups, as requested by the source.

The source object is exactly `LocalizedModule S M`; its canonical map is exactly
`LocalizedModule.mkLinearMap S M : M →ₗ[R] LocalizedModule S M`, sending m to
`LocalizedModule.mk m 1`. No new quotient or assumed certificate replaces this
construction. Mathlib's instance `localizedModuleIsLocalizedModule` certifies
this actual map. `localizedModule_isSLocal` obtains its locality from
`IsLocalizedModule.map_units` on that map.

`divBy_scalar s z` and `scalar_divBy s z`, for `s : S` and
`z : LocalizedModule S M`, prove the two inverse identities

```lean
LocalizedModule.divBy s ((s : R) • z) = z
(s : R) • LocalizedModule.divBy s z = z
```

They use `LocalizedModule.divBy_mul_by` and `LocalizedModule.mul_by_divBy`.
`divBy_mk s t m` gives the actual inverse action on fractions:
`LocalizedModule.divBy s (LocalizedModule.mk m t) = LocalizedModule.mk m (t * s)`.
It unfolds the existing definition, rather than introducing a new inverse.

For a concrete map `ι : M →ₗ[R] L`, `HasUniversalProperty S ι : Prop`
quantifies over every `N : Type w`, every additive commutative group structure
and unital R-module structure on N, every `hN : IsSLocal S N`, and every
`f : M →ₗ[R] N`. It asserts

```lean
∃! g : L →ₗ[R] N, g.comp ι = f
```

This is the linear-map form of the right universal problem. It does not itself
assert locality of L: the canonical construction is supplied with both
`localizedModule_isSLocal` and `canonical_hasUniversalProperty`. The latter has
universe specialization `HasUniversalProperty.{u, v, max u v, w}` and proves
the property for `LocalizedModule.mkLinearMap S M` at every independent target
universe w.

For `hN : IsSLocal S N` and `f : M →ₗ[R] N`, `factor S hN f` is exactly
`LocalizedModule.lift S f hN : LocalizedModule S M →ₗ[R] N`.
`factor_mk S hN f m s` gives

```lean
factor S hN f (LocalizedModule.mk m s) = (hN s).unit⁻¹.val (f m)
```

The right side applies the inverse unit in `Module.End R N`; it does not assert
that this inverse is a scalar from R. `factor_comp` is the factorization
identity, and `factor_unique` says that any g with that identity equals the
chosen factor. These are direct uses of `LocalizedModule.lift_mk`, `lift_comp`
and `lift_unique`, with the equality in the uniqueness law reversed to match
Lean's unique-existence convention. `canonical_hasUniversalProperty` packages
these three laws into the proposition above.

For `ι : M →ₗ[R] L` and `κ : M →ₗ[R] N` with the two explicit instance
hypotheses `[IsLocalizedModule S ι] [IsLocalizedModule S κ]`,
`comparison S ι κ : L ≃ₗ[R] N` is an abbreviation for
`IsLocalizedModule.linearEquiv S ι κ`. This is Mathlib's canonical equivalence
built using `IsLocalizedModule.iso`; it is not an additional construction.
`comparison_comp` asserts that its forward linear map composed with ι is κ;
`comparison_symm_comp` asserts the reverse compatibility with κ and ι.
The proofs apply `IsLocalizedModule.linearEquiv_apply` and
`IsLocalizedModule.linearEquiv_symm_apply` pointwise. Certificates are inputs
only for this comparison of arbitrary localizations, not for the existence of
the concrete canonical localization above.

`localizedModule_subsingleton h0`, with the sole extra hypothesis
`h0 : (0 : R) ∈ S`, is `Subsingleton (LocalizedModule S M)`. It reuses
`LocalizedModule.subsingleton h0` directly. The actual localized module has a
zero element, so this is precisely the source's zero-module boundary statement.

## Formal evidence against the parenthesis

All declarations in this paragraph are closed concrete results with the usual
unital integer-module structure on the rational numbers; they have no general
ring or module parameters. `rationals_isSLocal` proves
`IsSLocal (Submonoid.powers (2 : ℤ)) ℚ`. For a denominator represented by
`2 ^ n`, the proof checks it is a nonzero integer and a nonzero rational, then
uses `LinearEquiv.smulOfNeZero ℚ ℚ` and `isSLocal_iff_bijective`. The rational
scalar map has the same underlying function as the integer scalar action.

`no_integer_inverse_two t`, for every `t : ℤ`, proves
`(t * 2) • (1 : ℚ) ≠ 1`. It transports a hypothetical equality to the integer
equation `t * 2 = 1`; integer arithmetic rejects that equation.
`scalar_inverse_parenthesis_counterexample` combines locality with the
negation of the full parenthetical condition, including both product orders.
It substitutes `s = 2`, whose membership in the powers submonoid is proved by
`Submonoid.mem_powers`, and `q = 1`, then uses `no_integer_inverse_two`.
Thus the failure occurs in a module satisfying the corrected definition.

`rationalHalf : Module.End ℤ ℚ` restricts the rational-linear scalar map for
`1 / 2` to integer scalars. `rationalHalf_apply q` states that its value is
`(1 / 2 : ℚ) * q`. For every `q : ℚ`, `rationalHalf_scalar_two q` and
`scalar_two_rationalHalf q` prove that it is a two-sided inverse of the
integer scalar endomorphism for 2. These identities use rational multiplication
and arithmetic simplification. `rationalHalf_not_integer_scalar t` proves that
this inverse endomorphism is unequal to `algebraMap ℤ (Module.End ℤ ℚ) t`
for every integer t, by applying the first inverse identity at 1 and reducing
to `no_integer_inverse_two`. This explains exactly why invertibility of an
endomorphism does not supply an inverse coefficient in the original ring.

## Reuse and scope

The reused Mathlib source is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`, principally
`Mathlib/Algebra/Module/LocalizedModule/Basic.lean` (Andrew Yang and Jujian
Zhang) and `Mathlib/Algebra/Module/Equiv/Basic.lean`. The constructions and
intrinsic laws are source correspondence for example 4; the corrected
interpretation and counterexample are explicitly internal work. No additional
axioms are introduced.

This unit does not construct the full subcategory, its inclusion or a packaged
universal arrow. Mathlib's functor to modules over `Localization S` is not that
full-subcategory interface. Those category constructions, ring-localization
example 3, the polynomial-module equivalence and example 5, PDF259's lemma and
corollary, exactness, and general adjunction theory remain parent obligations.
