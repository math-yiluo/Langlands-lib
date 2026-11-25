# Proof of universal Japanese finiteness over a complete Noetherian local ring

`Langlands.CommutativeAlgebra.completeLocalNormalizationFiniteness.{u}` proves the Library
proposition `Langlands.CommutativeAlgebra.CompleteLocalNormalizationFinitenessStatement.{u}`,
imported from `Langlands.CommutativeAlgebra.CompleteLocalNormalizationFiniteness`. Its type is
exactly that closed proposition, with one universe level `u` for all rings and fields. The
statement module is unchanged.

```lean
theorem completeLocalNormalizationFiniteness :
    CompleteLocalNormalizationFinitenessStatement.{u}
```

## Statement proved

Let \(R\) be a Noetherian local ring, complete with respect to its maximal ideal, and let \(S\) be
a domain of finite type over \(R\). For every finite extension \(L\) of the fraction field of
\(S\), with \(S\to L\) factoring through the fraction field, the integral closure of \(S\) in
\(L\) is a finite \(S\)-module. In Lean:

```lean
def CompleteLocalNormalizationFinitenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (L : Type u) [Field L] [Algebra (FractionRing S) L] [Algebra S L]
    [IsScalarTower S (FractionRing S) L] [FiniteDimensional (FractionRing S) L],
    Module.Finite S (integralClosure S L)
```

## Proof

1. **\(R\) is Nagata** (Tag 032W). The copy's theorem

   ```lean
   theorem StacksIsNagataRing.of_isPrecomplete_maximalIdeal {R : Type u} [CommRing R]
       [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R] :
       StacksIsNagataRing R
   ```

   applies, the precompleteness instance being part of `IsAdicComplete`.
2. **\(R\) is universally Japanese** (Tag 0334). The copy's theorem

   ```lean
   theorem isNagataRing_tfae {R : Type u} [CommRing R] :
       List.TFAE
         [ StacksIsNagataRing R,
           ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], StacksIsNagataRing S,
           IsUniversallyJapaneseRing R ∧ IsNoetherianRing R ]
   ```

   gives, from the first condition to the third (`List.TFAE.out 1 3`),
   `IsUniversallyJapaneseRing R ∧ IsNoetherianRing R`.
3. **The finiteness.** The copy's class
   `IsUniversallyJapaneseRing R` has the field
   `japanese (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S] :
   IsJapaneseRing S`, and `IsJapaneseRing S` has the field
   `finite (L : Type u) [Field L] [Algebra (FractionRing S) L] [Algebra S L]
   [IsScalarTower S (FractionRing S) L] [FiniteDimensional (FractionRing S) L] :
   Module.Finite S (integralClosure S L)`, which is the conclusion, with the same binders in the
   same order. The proof is `(hU.1.japanese S).finite L`.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

From the extract of the Stacks copy (`StacksFrontier/`, module system files):

- `StacksIsNagataRing.of_isPrecomplete_maximalIdeal`
  (`StacksFrontier.RingTheory.Nagata.CompleteLocalRing`), Tag 032W;
- `isNagataRing_tfae` (`StacksFrontier.RingTheory.Nagata.FiniteType`), Tag 0334;
- `StacksIsNagataRing`, `IsUniversallyJapaneseRing`, `IsJapaneseRing`
  (`StacksFrontier.RingTheory.Nagata.Defs`), Tags 032R and 032F.

From the Library: `CompleteLocalNormalizationFinitenessStatement`
(`Langlands.CommutativeAlgebra.CompleteLocalNormalizationFiniteness`).

The module imports the statement module and the three modules of the extract named above.

## Sources

- Stacks Project, [Tag 032W](https://stacks.math.columbia.edu/tag/032W): a Noetherian complete
  local ring is a Nagata ring.
- [Tag 0334](https://stacks.math.columbia.edu/tag/0334): a Nagata ring is universally Japanese,
  and every ring of finite type over it is Nagata.
- [Tag 032R](https://stacks.math.columbia.edu/tag/032R) (Nagata and universally Japanese rings)
  and [Tag 032F](https://stacks.math.columbia.edu/tag/032F) (N-2, or Japanese, domains).
- The proofs of Tags 032W and 0334 in Lean are those of the Stacks copy (AxiomMath/Stacks, commit
  `c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache-2.0), files
  `StacksFrontier/RingTheory/Nagata/CompleteLocalRing.lean` and
  `StacksFrontier/RingTheory/Nagata/FiniteType.lean`, through the extract of that library kept
  in `StacksCore/` and `StacksFrontier/`, where the copy's class `IsNagataRing` is named
  `StacksIsNagataRing`.
