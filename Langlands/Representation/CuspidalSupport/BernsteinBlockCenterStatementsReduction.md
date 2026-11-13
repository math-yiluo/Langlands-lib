# Conditional reduction of Renard VI.10.4, Corollary and Remark 3, to the Theorem of VI.10.4

Worker 5226, task 03c64afa (Renard VI.10.4–VI.10.5), target 3.

The source is Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`):

- VI.10.4, Theorem (first sentence), its proof, Corollary and Remark 3, printed p.212 /
  PDF p.218;
- VI.7.1, Theorem, printed pp.180–181 / PDF pp.186–187.

**Scope.** This module does not prove the published target
`BernsteinBlockCenterStatements` unconditionally. It proves that the target follows from
one published statement that is not yet proved in the Library:
`BernsteinBlockCenterFunctionsStatement`, the first sentence of the Theorem of VI.10.4 with
Remark 1 (module `BernsteinCenterFunctionsStatements`; its proof is the work of task
c4d4541b). Once that statement is proved, the target follows by applying
`bernsteinBlockCenterStatements_of_centerFunctions`.

## Lean statement

```
def BernsteinBlockCenterStatementsReductionStatement : Prop :=
  BernsteinBlockCenterFunctionsStatement.{uF, uV} → BernsteinBlockCenterStatements.{uF, uV}
```

Both sides are the published propositions, unchanged, at the same universes `uF`
(the field) and `uV`. In both, the cuspidal datum has carriers in `Type (max uF uV)`.
`BernsteinBlockCenterStatements` is the conjunction of
`BernsteinBlockCenterNoetherianStatement` (VI.10.4, Corollary: the centre `CatCenter` of
the block `M(G)_Ω` is a Noetherian ring) and `BernsteinBlockIndecomposableStatement`
(VI.10.4, Remark 3: every decomposition of the block into two full subcategories, in the
sense of A.IX, has a factor containing only zero objects).

The module proves the statement as `bernsteinBlockCenterStatementsReductionStatement_holds`.
It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is a derived statement. Renard deduces the Corollary from the Theorem: the centre
`ℨ_Ω` is isomorphic to the algebra `O(Ω)` of polynomial functions on `Ω`, which is the
algebra of regular functions on the quotient of a complex algebraic torus by a finite
group (VI.7.1), so it is a Noetherian `ℂ`-algebra. Remark 3 says the blocks are
indecomposable, generalizing Corollary VI.4.5; Renard gives no separate argument. The
argument implemented here is the standard one: a decomposition of the block gives an
idempotent of its centre, and `O(Ω)` is a domain because `Ω` is irreducible (VI.7.1), so
the idempotent is `0` or `1`.

## Proof (as implemented)

### General lemma (namespace `Langlands.Renard`)

`exists_isZero_of_decomposition_of_centerEquiv`. Let `C` be a preadditive category and
`R` a ring that is a domain, and let `e : CatCenter C ≃+* R` be a ring isomorphism.
Then every decomposition `P : Bool → ObjectProperty C` of `C` in the sense of A.IX
(`IsCategoryDecomposition P`) has an index `b` such that every object `X` with `P b X`
is zero.

Proof. The published `decompositionIdem hP` is a central element. It acts by the identity
on the objects of the factor `true` and by zero on those of the factor `false`, and it is
idempotent (`decompositionIdem_isIdempotentElem`). Its image under `e` is an idempotent of
the domain `R`, hence `0` or `1` (`IsIdempotentElem.iff_eq_zero_or_one`). Since `e` is
injective, `decompositionIdem hP` itself is `0` or `1`.

- If it is `0`, the objects of the factor `true` are zero
  (`isZero_of_decompositionIdem_eq_zero`).
- If it is `1`, the objects of the factor `false` are zero
  (`isZero_of_decompositionIdem_eq_one`).

### The reduction (namespace `Langlands.CuspidalSupport`)

`bernsteinBlockCenterStatements_of_centerFunctions` proves the target from
`hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV}`. Fix the data `F, G, T, i, ν`, the
instances, a standard family and an actual cuspidal datum `a` with carriers in
`Type (max uF uV)`.

1. `hS1` at `a` gives a subalgebra `O` of `X(M) → ℂ` whose carrier is the set `invariant`
   of regular functions constant on association classes, and a ring isomorphism
   `e : CatCenter (M(G)_Ω) ≃+* O`.
2. The proved VI.7.1 Theorem `bernsteinComponentVariety`, at universes `uF` and
   `max uF uV`, gives a subalgebra `O'` with the same carrier `invariant` (the two
   statements define `X`, `twist`, `Assoc`, `regular` and `invariant` by the same
   expressions), such that `O'` is a finitely generated `ℂ`-algebra and a domain.
3. `O = O'`, because subalgebras with equal carriers are equal (`SetLike.coe_injective`).
4. **Corollary.** `O` is Noetherian by Hilbert's basis theorem
   (`Algebra.FiniteType.isNoetherianRing`), and the centre is Noetherian because it is
   isomorphic to `O` as a ring (`isNoetherianRing_of_ringEquiv`).
5. **Remark 3.** The general lemma applies to the block, the domain `O` and the
   isomorphism `e`.

`bernsteinBlockCenterStatementsReductionStatement_holds` is
`bernsteinBlockCenterStatements_of_centerFunctions`.

## Declarations

- `Langlands.Renard.exists_isZero_of_decomposition_of_centerEquiv` (theorem, general).
- `Langlands.CuspidalSupport.BernsteinBlockCenterStatementsReductionStatement`
  (the proposition above).
- `Langlands.CuspidalSupport.bernsteinBlockCenterStatements_of_centerFunctions` (theorem).
- `Langlands.CuspidalSupport.bernsteinBlockCenterStatementsReductionStatement_holds`
  (theorem).
