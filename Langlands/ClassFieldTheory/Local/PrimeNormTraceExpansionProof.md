# Prime-degree determinant norm expansion modulo traces

Worker 107 wrote this proof module and its explanation. It proves the published
proposition `Langlands.LocalClassField.PrimeNormTraceExpansion.{u,v}`, authored
by Workers 27 and 107, without changing that statement or its dependencies.
The main theorem is

```lean
theorem Langlands.LocalClassField.primeNormTraceExpansion :
    PrimeNormTraceExpansion.{u, v}
```

The theorem retains the independent universes of the base and extension fields
and every hypothesis of the published proposition. Given the supplied finite
Galois extension of prime degree, its total-ramification hypothesis, any
`n : ℕ`, and an element `x` of the canonical integer ring in the nth power of
its maximal ideal, it produces an element `z` in the `2*n`th power satisfying
the exact equality in the supplied base field:

```text
norm(1 + x) - 1 - trace(x) - norm(x) = trace(z).
```

Here the norm is Mathlib's determinant norm for the supplied algebra and the
trace is its field trace. The witness is an actual element of the canonical
integer ring. Total ramification remains quantified in the target but is
unused by this proof.

## Imported combinatorial argument

The proof imports
`Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionProof` and
applies `Langlands.LocalClassField.primeOrbitProductTraceExpansion`.
Worker 807 wrote that proof; Workers 107 and 726 wrote its statement.
It is a proved theorem, with no additional expansion premise in this module.

For a prime-order finite group acting on a commutative ring and preserving an
ideal `I`, that theorem expands the product of `1 + g • x` over all subsets
of the group. The empty, singleton and full subsets contribute `1`, the orbit
sum of `x`, and the product of all conjugates of `x`. Every remaining subset
has between two and one less than the group order elements. Its stabilizer
is trivial: the prime-order subgroup dichotomy leaves only the trivial
subgroup or the whole group, and a nonempty subset fixed by the whole group
is the full subset.

The imported proof removes these free orbits by strong induction on the
finite family of middle subsets. It adds one representative product per
orbit to form `z`. Every product has two factors in `I` and hence lies in
`I²`; additive closure puts `z` in `I²`. Equivariance of subset products and
injectivity of each orbit map identify the sum over an orbit with the orbit
sum of its representative product. Additivity combines them into the orbit
sum of `z`. No division by the group order is used.

## Canonical ideal and field identifications

The actual action on the canonical integer ring is
`Ramification.Padic.integerAction`. Its ring equivalences are
`Ramification.Padic.integerAutomorphism`, whose coercions to the extension
field agree definitionally with the supplied Galois automorphisms.

The private lemma `canonical_integerAutomorphism_mem_maximalIdeal_pow` maps
an ideal membership along this ring equivalence using
`Ideal.mem_map_of_mem`. `Ideal.map_pow` and
`IsLocalRing.map_ringEquiv_maximalIdeal` identify the image ideal with the
same maximal-ideal power. The action version
`canonical_integerAction_preserves_maximalIdeal_pow` supplies precisely the
invariance hypothesis of the imported theorem.

The private lemma `canonical_integer_equation_to_norm_trace` coerces the
integer-ring product-and-sum equality into the actual extension field.
Coercion preserves the ring operations and finite products and sums.
`Algebra.norm_eq_prod_automorphisms` identifies the two products with the
images of the determinant norms, and `trace_eq_sum_automorphisms` identifies
the two sums with the images of the field traces. Injectivity of the supplied
base-field algebra map gives the required equality in the base field.

The private lemma `canonical_maximalIdeal_pow_square` uses the power laws
to identify `(m^n)^2` with `m^(2*n)`.

## Assembly and boundary cases

The main theorem unfolds the target's local abbreviations and installs the
canonical integer-ring action. `IsGalois.card_aut_eq_finrank`, together with
`Fintype.card_eq_nat_card`, transfers the supplied primality of the field
degree to primality of the cardinality of its actual Galois group. Both this
group and the integer ring live in universe `v`, so the generic theorem is
used at universes `v,v` while the base field keeps its independent universe
`u`.

Apply the imported theorem with `I := m^n`. The preservation lemma supplies
invariance and the given `hx` supplies membership. It returns the witness `z`,
membership in `(m^n)^2`, and the exact integer-ring orbit equality.
Rewriting the ideal square and applying the field translation lemma proves
the target.

There is no restriction on `n`, `x`, or `1+x`. The ideal-map and power
identities include `n=0`, and the product expansion includes zero factors.
For degree two the middle family is empty, so the imported construction
returns `z=0`. The argument also covers `x=0` and `1+x=0`.

## Provenance

The source argument is Jean-Pierre Serre, *Local Fields*, Greenberg English
translation, GTM 67, Springer (1979), Chapter V, §3, Lemma 5 and its proof,
printed pp.83–84 / PDF pp.90–91, registered as `serre-1979-local-fields`.
Worker 107 read those pages and the registered
`serre-book-corrections-2019`, PDF pp.2–3; the corrections do not change this
passage.

The implemented route is Serre's subset-product and prime-order orbit
argument, factored through the published ring-level theorem. That theorem
uses stabilizers and strong induction instead of an explicit cyclic
generator and an explicit transversal. The private reduction lemmas here
are derived implementation steps using existing Library and Mathlib
mathematics. The proof uses no different or trace-ideal formula, graded norm
result, or downstream local class-field theorem.
