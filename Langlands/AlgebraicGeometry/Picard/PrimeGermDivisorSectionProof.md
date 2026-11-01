# Proof of the prime-germ divisor-section statement

This module proves `Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement`
(module `Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement`) as the
theorem `Langlands.AlgebraicGeometry.Picard.primeGermDivisorSection`, in two steps.

## `primeGermDivisorSection_of_gluing`

The theorem `primeGermDivisorSection_of_gluing` derives the statement from a gluing
hypothesis `hglue`: for every integral scheme `X`, every open cover `T : ι → X.Opens`
(`⨆ i, T i = ⊤`, with `ι : Type u`) and every family of local functions `a i : Γ(X, T i)`
whose germs are nonzero at every point of `T i` and pairwise associated at every point of
`T i ⊓ T j`, there are a line bundle `L` and a global section `s` with
`T i ⊓ trivializationOpen L.obj s = X.basicOpen (a i)` for every `i`, and with
`VanishesAlong L g s ↔ g.appLE (T i) ⊤ hg (a i) = 0` for every morphism `g` into `T i`.

Its proof, for `X` integral and locally Noetherian with factorial stalks, a point `e` and a
prime `π` of the stalk at `e`, uses the lemmas of
`Langlands.AlgebraicGeometry.Picard.PrimeDivisorEquations` (namespace `PrimeDivisor`):

1. `exists_primeGermPoint` gives a point `ζ` of coheight one specializing to `e` such that,
   for every open `U ∋ e` and function `f` on `U`, `ζ ∈ X.basicOpen f` if and only if `π`
   does not divide the germ of `f` at `e`.
2. `exists_affine_equation` gives, for every point `x`, an affine open `U x ∋ x` and a
   nonzero function `a x` on it generating the ideal `closureIdeal ζ` of the closure of `ζ`
   on `U x`. The cover is `T x = U x`, indexed by the points of `X`.
3. The germs of `a x` are nonzero at every point of `U x` (`germ_injective_of_isIntegral`),
   and any two equations have associated germs on overlaps (`associated_equation_germs`).
   So `hglue` applies and gives `L` and `s` with
   `T x ⊓ trivializationOpen L.obj s = X.basicOpen (a x)` and the local vanishing criterion.
4. The four clauses:
   * `e ∉ trivializationOpen L.obj s`: otherwise `e ∈ X.basicOpen (a e)`; but
     `mem_basicOpen_equation_iff` says that a point of `U e` lies in this basic open exactly
     when it is not a specialization of `ζ`, and `ζ ⤳ e`.
   * The generation open is nonempty: `a e ≠ 0`, so `X.basicOpen (a e)` is not empty, and it
     lies in the generation open.
   * If `π` divides the germ of `f` at `e`, then `ζ ∉ X.basicOpen f` by step 1, so no point
     `x` of `X.basicOpen f` is a specialization of `ζ` (opens are closed under
     generization); by `mem_basicOpen_equation_iff`, `x ∈ X.basicOpen (a x)`, which lies in
     the generation open.
   * The local equation at `e` is `a e` on `T e`; its germ at `e` is associated to `π` by
     `associated_equation_germ_prime`, and the vanishing criterion is the second output of
     `hglue` for the index `e`.

## `primeGermDivisorSection`

The gluing hypothesis is exactly the type of
`Langlands.AlgebraicGeometry.Picard.exists_lineBundle_of_associated_equations` (module
`Langlands.AlgebraicGeometry.Picard.AssociatedEquationGluing`). Hence
`primeGermDivisorSection := primeGermDivisorSection_of_gluing (fun … ↦
exists_lineBundle_of_associated_equations …)` proves the statement with no remaining
hypothesis.

## Provenance

This is a local-equation implementation of the Stacks Project construction (registered
source `stacks-divisors-locally-factorial-2026-10-31`): the closure of `ζ` is the prime
divisor `D`, Lemma 31.16.7 (tag 0AGA) is realized by the principal local equations of
step 2, and the glued line bundle and section play the roles of `𝒪_X(D)` and its canonical
section `1_D` (Definition 31.15.1, tag 01WX; proof of Lemma 31.28.7, tag 0BE9). It supports
the prime-divisor step of Milne, *Abelian Varieties* (corrected author version, 2022),
proof of Theorem 7.1, p. 11. No projectivity, ampleness or separating line bundle is used.
The construction is uniform in the universe and makes no dimension assumption; when the
stalks have no prime elements the statement is vacuous.
