# Free generation of class functions by fundamental trace characters

This module proves the Library statement
`Langlands.GroupScheme.SplitFundamentalCharacterGenerationStatement.{u}` from
`Langlands.GroupScheme.Rational.FundamentalCharacters` as the theorem
`Langlands.GroupScheme.splitFundamentalCharacterGeneration`. The statement covers every
algebraically closed field `k : Type u` of any characteristic, every actual affine
group scheme `G` over `Spec k` with a split pinning `p`, every proof that `G` is simply
connected, every ordering `e : Fin r ≃ p.base.support` of the simple roots, and every
family `F` of actual fundamental representations. For all of these,
`p.fundamentalCharacterMap e F`, the `k`-algebra map from the polynomial ring in `r`
variables to `ClassFunctions.algebra G` that sends variable `j` to the trace character
of `F (e j)`, is bijective. The theorem adds no hypothesis.

The argument follows Steinberg, *Regular elements of semisimple algebraic groups*
(1965), §6, Lemmas 6.2–6.3 and Corollary 6.4. Class functions inject into
Weyl-invariant functions on the torus, and the restricted fundamental characters freely
generate those functions by a triangularity argument. Lemma 6.2 (injectivity) is proved
by a different route than Steinberg's; see below.

## Declarations (namespace `Langlands.GroupScheme.SplitPinning`)

Write `Res = p.torusRestriction` for the published restriction
`ClassFunctions.algebra G →ₐ[k] AddMonoidAlgebra k (characterLattice p.torus)` from
`TorusClassFunctionRestriction`.

- `torusRestriction_comp_fundamentalCharacterMap`: `Res ∘ fundamentalCharacterMap e F`
  equals `MvPolynomial.aeval` at the restricted characters `Res (F (e j)).character`
  (`MvPolynomial.comp_aeval`).
- `fundamentalCharacterMap_bijective_of_torus`: this is a formal lemma with three
  hypotheses: `Res` is injective, the `aeval` map at the restricted characters is
  injective, and every element of `k[X]` whose coefficients are invariant under all
  root reflections lies in the range of that `aeval` map. Under these hypotheses the
  fundamental character map is bijective. Injectivity comes from the composite formula.
  For surjectivity, `Res f` is reflection invariant (`torusRestriction_coeff_reflection`),
  so it equals `aeval q`, and injectivity of `Res` gives `fundamentalCharacterMap q = f`.
- `eq_zero_of_forall_simple_coroot_of_isSemisimple`: for semisimple `G`, a character
  pairing to zero with every simple coroot is zero. The finiteness of
  `X ⧸ rootSpan` comes from the published
  `IsSemisimple.finite_quotient_rootSpan`. The published
  `Langlands.RootDatum.Triangular.eq_zero_of_forall_simple_coroot` then applies.
- `fundamentalCharacterMap_bijective_of_torusRestriction_injective (hG :
  IsSimplyConnected G) e F hinj`: the fundamental character map is bijective once `Res`
  is injective. The highest weight `λ_j` of `F (e j)` pairs to `1` with the coroot of
  `e j` and to `0` with the other simple coroots (`isFundamentalWeight`). Each
  restricted character has coefficient `1` at `λ_j` and support in
  `λ_j - positiveRootMonoid` (`torusRestriction_character_coeff_highestWeight`,
  `sub_mem_positiveRootMonoid_of_mem_support`). So it is a top-weight element
  (`Triangular.IsTopWeight`). The published triangularity results
  `Triangular.aeval_injective` and `Triangular.mem_range_aeval` from
  `DominantWeightTriangularity` give the remaining two hypotheses of the formal lemma.
  Reflection invariance of polynomials in the restricted characters comes from the
  composite formula and `torusRestriction_coeff_reflection`. Simple connectedness
  enters only through `hG.isSemisimple`.
- `torusRestriction_injective [IsAlgClosed k]`: `Res` is injective. If `Res f = 0`, then
  `f` vanishes at the image of every torus point over every algebra
  (`pointCoordinates_torusPoint_eq_zero`). So `f = 0` by
  `TorusConjugation.classFunction_eq_zero`, applied to the pinning's inclusion together
  with its `isConnectedReductive`, `isMaximalTorus` and `isSplitTorus` fields.

## Main theorem (namespace `Langlands.GroupScheme`)

`splitFundamentalCharacterGeneration : SplitFundamentalCharacterGenerationStatement.{u}`
applies `fundamentalCharacterMap_bijective_of_torusRestriction_injective` with
`torusRestriction_injective`.

## Injectivity of torus restriction

Steinberg proves Lemma 6.2 from the density of semisimple elements. The helper module
`Langlands.GroupScheme.Rational.ClassFunctionsTorusDensity`, which is part of this
contribution, uses a different route. A rational torus point `τ₀` at which no root takes
the value `1` exists by the Nullstellensatz. At `(1, τ₀)`, the conjugation morphism
`G × T → G`, `(g, t) ↦ g j(t) g⁻¹`, is surjective on tangent vectors. This uses the
weight decomposition of the Lie algebra and the published fact that a maximal torus of
a connected reductive group is its own centralizer. So the conjugation morphism has
dense range. Since `G` is integral, pullback along it is injective, and the pullback of
a class function is its pullback along the torus inclusion.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
