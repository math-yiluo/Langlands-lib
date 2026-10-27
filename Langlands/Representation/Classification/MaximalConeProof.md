# Proof of the maximal-cone selection

Author: Worker 23.

This module proves

```text
theorem Langlands.glMaximalConeJacquetQuotient :
    GLMaximalConeJacquetQuotientStatement.{uF, uV}
```

for the statement of [`MaximalConeStatement`](MaximalConeStatement.md). The
theorem's entire type is the published proposition. The field and carrier
universes `uF` and `uV` remain independent. The theorem has no hypotheses, so
it adds no premise, no rank restriction beyond the statement's own `0 < n`,
and no equality of universes. The target pair and its imports are not edited.

## Proof

The theorem is one term:

```text
glMaximalConeJacquetQuotient_of glDualJacquetFiniteness glBlockConeExists
  Parabolic.oppositeJacquetFiniteGeneration
  (glProductLeviDualOppositeTemperedSufficiency_of_core
    glProductLeviTemperedExponentSufficiency)
```

`glMaximalConeJacquetQuotient_of hfin hcone hfg htemp`
([`MaximalConeAssembly`](MaximalConeAssembly.md)) derives the target from four
published propositions. Here each one is supplied by its published proof:

- `hfin := glDualJacquetFiniteness`
  ([`Exponents/DualJacquetFinitenessProof`](../Exponents/DualJacquetFinitenessProof.md)).
  It proves `GLDualJacquetFinitenessStatement`; the assembly uses its first
  clause, finiteness of the set of full-dual opposite Jacquet exponents along
  each block shape.
- `hcone := glBlockConeExists`
  ([`ParabolicConeExistenceProof`](ParabolicConeExistenceProof.md)). It proves
  `GLBlockConeExistenceStatement`: every real block vector has a numerical cone
  coarsening (pool adjacent violators).
- `hfg := Parabolic.oppositeJacquetFiniteGeneration`
  ([`Parabolic/OppositeJacquetFiniteGenerationProof`](../Parabolic/OppositeJacquetFiniteGenerationProof.md)).
  It proves that normalized opposite Jacquet modules of finitely generated
  smooth representations are finitely generated.
- `htemp := glProductLeviDualOppositeTemperedSufficiency_of_core
  glProductLeviTemperedExponentSufficiency`. The adapter
  `glProductLeviDualOppositeTemperedSufficiency_of_core`
  ([`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md))
  derives the opposite dual-eigenfunctional form of product-Levi tempered
  sufficiency from its upper generalized-exponent form. That upper form is the
  theorem `glProductLeviTemperedExponentSufficiency`
  ([`ProductLeviTemperedSufficiencyProof`](ProductLeviTemperedSufficiencyProof.md)).

All four inputs are instantiated at the same `uF` and `uV` as the target;
`GLBlockConeExistenceStatement` has no universe parameters.

## How the inputs are used

The assembly's Markdown gives the full argument. In outline, for an
irreducible admissible `A` of `GL_n(F)` with `n > 0`:

1. For each block shape, the real parts of the dual exponents of `A` form a
   finite set (`hfin`). The central character gives a dual exponent along the
   one-block shape, so the family is nonempty, and `hcone` gives cones for all
   its members.
2. A dominance-maximal pair is selected from this finite family: a real part `r`
   of an actual dual exponent `χ` along a shape `B`, with a cone `(C, q, t)`
   whose positive part no cone of any member strictly dominates under
   `GLBlockPositivePartStrictlyDominates`. Competitors range over every dual
   exponent on every standard shape and every numerical cone coarsening.
3. The restriction `χC` of `χ` along `q` is a dual exponent along `C`. With
   finite generation (`hfg`) and published admissibility of opposite Jacquet
   modules, it yields an irreducible admissible quotient `S` of the whole
   normalized opposite Jacquet module along `C`, on which the block scalars act
   by `χC`.
4. After twisting `S` by the inverse real Levi determinant character, the
   central character is unitary. For every refinement of `C`, maximality makes
   the within-block prefix sums of the real part of every dual exponent of the
   twisted quotient's refined opposite Jacquet module nonpositive. This uses
   exponent lifting along the surjection and a polygon comparison. `htemp`
   then gives temperedness for every Borel Haar measure on the full centre
   quotient.

`glProductLeviTemperedExponentSufficiency` is proved as
`ProductLeviTempered.tempered_of_cellCount` applied to the published
`CartanQuotient.cartanCellCount`. That argument combines the product-Levi
chamber coefficient bound (`glProductLeviChamberCoefficientBound`), the Cartan
decomposition, a count of left cosets in each Cartan double coset, and the
summability of the resulting `L^(2+ε)` estimate over the cells.

The proof is independent of the final regular Langlands exhaustion theorem.
No module in the import closure of this module proves an exhaustion or final
classification theorem. The word "exhaustion" occurs in the closure only in
proposition and definition names: a compact-open exhaustion of a unipotent
radical, and clauses of correspondence and spherical-classification
statements. None of these is assumed as a premise.

## Sources

- T. Konno, *A note on the Langlands classification and irreducibility of
  induced representations of p-adic groups* (2003), registered as
  `konno-2003-langlands-classification`: Lemmas 3.3–3.4 and Theorem 3.5(i),
  pp.394–397. These give the dominance-maximal selection, which the assembly
  follows. Konno selects along a cuspidal support and works with a
  subrepresentation of an isotypic part. The assembly instead uses the full
  family of dual exponents and takes a quotient of the whole opposite Jacquet
  module, as the statement requires. Those extensions are derived in the
  assembly, not taken from Konno.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups* (1995), registered as
  `casselman-1995-admissible-representations`, Theorem 3.3.1, p.35. The
  imported modules cite it for finite generation and admissibility of Jacquet
  modules.
- The analytic sufficiency criterion is cited in
  [`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md)
  to J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
  d'après Harish-Chandra* (2003), and A. J. Silberger, *Introduction to
  harmonic analysis on reductive p-adic groups* (1979). The published proofs
  imported here implement it by their own route. The chamber bound uses
  compressed actions on compact-open fixed vectors, not Waldspurger's route
  through `Ξ`. The coset count is derived through residue maps, not by
  Waldspurger's Iwahori argument.
- A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
  Proposition 7.2, motivates the cone and whole-quotient formulation. As the
  statement's Markdown records, its maximum-block-count selection is false with
  these conclusions. The proof uses dominance maximality instead.
