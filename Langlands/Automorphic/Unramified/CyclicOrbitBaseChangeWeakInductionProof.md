# Weak induction from weak base change to the full Galois orbit and a norm self-twist

`Langlands.Automorphic.Unramified.cyclicOrbitBaseChangeWeakInduction` proves the
published proposition
`Langlands.Automorphic.Unramified.CyclicOrbitBaseChangeWeakInductionStatement.{uF,uE,uV,uW}`
of `Langlands.Automorphic.Unramified.CyclicOrbitInductionComparisonStatement` at its
stated scope. The extension `E/F` is Galois with cyclic Galois group, of arbitrary
degree. The Hecke character `η` of `F` has exactly the norm kernel. The actual lower
cuspidal class `c` is fixed by the finite-order determinant twist by `η`. The full Galois
orbit of the actual upper class `d`, with its multiplicities, is a weak base change of
the singleton datum of `c`. The theorem concludes that `c` is weakly induced from `d`,
with genuine attached spectral systems and the rank equation
`r + 1 = (m + 1) [E : F]`. There is no regularity hypothesis on `d`, no condition on the
archimedean places, and the field and presentation universes are independent.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120 (1989), registered as
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.

- Chapter III, Definition 6.1, printed p. 215 (PDF p. 229): automorphic induction by
  the unramified Hecke eigenvalues at the places above a base place.
- Formulas (6.1)–(6.2), printed p. 216 (PDF p. 230): at an inert place the induced
  Satake parameter is `t^{1/l} ⊕ ζ t^{1/l} ⊕ ⋯ ⊕ ζ^{l-1} t^{1/l}` for a primitive
  `l`-th root of unity `ζ`.
- Proof of Theorem 6.2, equations (6.5)–(6.6) and the calculation after them,
  printed pp. 216–217 (PDF pp. 230–231): from `π ≅ π ⊗ η` the parameter of `π` at an
  inert place is stable under multiplication by `ζ = η_v(ϖ_v)`, hence is a union of
  orbits `t_i, ζ t_i, …, ζ^{l-1} t_i`; by (6.6) the `l`-th powers are `l` times the
  parameter `T` of the upper representation, so `t_i` is an `l`-th root of `T_i` and
  (6.2) holds.

The source makes this calculation after reducing Theorem 6.2 to prime degree `l`, at
split and inert places, and Definition 6.1(iii) leaves the places of intermediate
decomposition to the reader. The Lean proof carries out the same calculation directly
at every unramified base place `v` in arbitrary cyclic degree, with the common residue
degree `f` of the places above `v` in place of `l`; split places are the case `f = 1`.

## The implemented proof

### Algebra of orbits

The section `CyclicOrbitWeakInduction` (algebra part) works with multisets of nonzero
complex numbers. For `ζ` a primitive `f`-th root of unity, `rootOrbit ζ f α` is the
multiset `α, ζ α, …, ζ^{f-1} α`.

- `mem_rootOrbit`: its elements are exactly the `x` with `x ^ f = α ^ f`
  (`IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity`); `nodup_rootOrbit` and
  `card_rootOrbit`: it has `f` distinct elements.
- `rootOrbit_le`: a multiset stable under multiplication by `ζ` contains the whole
  orbit of each of its elements; `map_mul_rootOrbit`: an orbit is stable under
  multiplication by `ζ`; `map_pow_rootOrbit`: its `f`-th powers are `f` copies of
  `α ^ f`.
- `prod_rootOrbit`: `∏ (1 - ζ^i α X) = 1 - α^f X^f`. This is Mathlib's
  `X_pow_sub_C_eq_prod` over the domain `ℂ[X]`, with the primitive root `C ζ` and the
  root `C α · X`, evaluated at `1`.
- `exists_rootOrbit_decomposition`: if `A` is stable under multiplication by `ζ` and
  the multiset of `f`-th powers of `A` is `f • B`, then `A` is the union of the orbits
  of a multiset `L` whose `f`-th powers are `B`. The proof is strong induction on the
  cardinality of `A`: remove the orbit of one element `α`, which also removes `f`
  copies of `α ^ f` from `f • B`, and cancel.
- `eulerPolynomial_eq_of_rootOrbit`: under the same hypotheses the Euler polynomial of
  the spectrum `A` is `∏_{β ∈ B} (1 - β X^f)`; `prod_eulerPolynomial_comp`: this is the
  product over a family of spectra with sum `B` of their Euler polynomials composed with
  `X^f`.

### Galois orbits of places

`sum_placeOrbit`: if every place above `v` is unramified of residue degree `f`, then
summing a function of places over all Galois automorphisms applied to one place `w`
(`placeOrbit w σ`, the arithmetic pullback of `w`) counts every place above `v` exactly
`f` times. The Galois group acts transitively on the places above `v`
(`Algebra.IsInvariant.exists_smul_of_under_eq`), the fibres of the orbit map have equal
size, and the fundamental identity `finitePlacesAbove_sum_ramification_inertia` gives
their common size `f`. The private lemmas before it repeat, for this file, the same
counting argument as the private lemmas of `WeakInductionOrbitRestriction`, with the
residue degree supplied as a hypothesis.

### Assembly

The proof of `cyclicOrbitBaseChangeWeakInduction` proceeds as follows.

1. The weak base change supplies the rank equation `hR`, a system `s` attached to the
   singleton datum of `c`, a system `tO` attached to the full orbit, and the cofinite
   arithmetic weak base change between them. `IsobaricData.HasSpectralSystem.exists_ofCuspidal`
   gives an actual presentation `P` of a representative `S` of `c` whose system has the
   Euler polynomials of `s` outside a finite set.
2. Since the orbit contains `d` itself (the identity automorphism,
   `PositiveRankCuspidalClass.galoisConj_one`), the attachment of `tO` contains an
   actual presentation `Q` of a representative `T` of `d`.
3. Genuine Galois attachment: as in `weakInductionOrbitBaseChange`, the arithmetic
   pullbacks `Q.arithmeticComap σ⁻¹` over all `σ ∈ Gal(E/F)` give a system `tO'`
   attached to the same orbit, whose spectrum at `w` is the sum of the spectra of `Q`
   at the places `placeOrbit w σ`. `IsobaricData.HasSpectralSystem.sameEulerPolynomials`
   identifies `tO` and `tO'` outside a finite set.
4. The rank equation follows from `IsobaricData.rank_galoisOrbit_of_isGalois`.
5. Self-twist: `IsoClass.isFiniteOrderDeterminantTwist_iff_eq` turns the hypothesis into
   `IsoClass.determinantTwist c η = c`. By
   `IsoClass.HasSpectralSystem.determinantTwist` the system of `P` scaled pointwise by
   `η.finiteUniformizerValue` is attached to the twisted class, hence to `c`, and
   `IsoClass.HasSpectralSystem.eigenvalues_eq` compares it with the system of `P` at
   every place where both are defined.
6. The exact local order: `HeckeCharacter.cyclicNormKernelUnramifiedOrder` gives,
   outside a finite set of `v`, that every place above `v` is unramified and the order
   of `ζ = η.finiteUniformizerValue v` equals the residue degree of every place above
   `v`. So these residue degrees have a common value `f`, and `ζ` is a primitive `f`-th
   root of unity.
7. At each remaining place `v`, the lower spectrum `A` of `P` is stable under
   multiplication by `ζ` (step 5). At one place `w₀` above `v`, the weak base change,
   step 1 and step 3 give that the `f`-th powers of `A` are the sum over `σ` of the
   spectra of `Q` at `placeOrbit w₀ σ`, which is `f` copies of the sum `B` of the
   spectra of `Q` at the places above `v` by `sum_placeOrbit`.
   `eulerPolynomial_eq_of_rootOrbit` and `prod_eulerPolynomial_comp` then give the
   induced Euler polynomial `∏_w (Euler polynomial of Q at w)(X^f)`, which is the
   weak-induction identity of `SpectralSystem.IsArithmeticWeakInductionOf` at `v`.

The cofinite set is the intersection of the set of the weak base change, the set where
`P` and `s` agree, the complement of the exceptional set of `P` and of the finite tail of
the twisted presentation, the set above which `tO` and `tO'` agree, the set above which
`Q` is defined, and the set of the norm-kernel order statement.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
